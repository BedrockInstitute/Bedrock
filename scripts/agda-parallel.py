#!/usr/bin/env python3
"""Build an Agda project in parallel along its module-import DAG.

Agda 2.8 has no module-level jobs option. This driver starts one Agda process
per scheduled project module, but only after every project-local import has completed.
Before starting workers, one serial Agda invocation builds the transitive
closure of the required external imports. Each worker therefore owns one project
interface output while sharing read-only dependency interfaces.  Optional
Bedrock traces are written per process and merged only after all writers exit.
Incremental mode schedules only stale interfaces and preserves the latest trace
records needed by the HTML renderer.
"""

from __future__ import annotations

import argparse
from concurrent.futures import FIRST_COMPLETED, Future, ThreadPoolExecutor, wait
import heapq
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile
import time


FENCE = re.compile(r"^```agda\s*\n(.*?)^```\s*$", re.M | re.S)
IMPORT = re.compile(r"^\s*(?:open\s+)?import\s+([\w.]+)", re.M)


def module_name(path: Path, source_root: Path) -> str:
    relative = path.relative_to(source_root).as_posix()
    return relative.removesuffix(".lagda.md").replace("/", ".")


def source_imports(path: Path) -> set[str]:
    text = path.read_text(encoding="utf-8")
    return {
        name for block in FENCE.findall(text) for name in IMPORT.findall(block)
    }


def local_graph(source_root: Path) -> tuple[dict[str, Path], dict[str, set[str]]]:
    paths = {
        module_name(path, source_root): path
        for path in sorted(source_root.rglob("*.lagda.md"))
    }
    graph = {}
    for module, path in paths.items():
        graph[module] = source_imports(path) & paths.keys()
    return paths, graph


def external_dependencies(paths: dict[str, Path], modules: set[str]) -> set[str]:
    project_modules = paths.keys()
    return {
        dependency
        for module in modules
        for dependency in source_imports(paths[module])
        if dependency not in project_modules
    }


def precompile_external_dependencies(
    *,
    project_root: Path,
    agda: Path,
    dependencies: set[str],
) -> None:
    """Build shared library interfaces once before project workers start."""
    if not dependencies:
        return
    environment = os.environ.copy()
    environment.pop("BEDROCK_AGDA_TYPES", None)
    environment.pop("BEDROCK_AGDA_RUN", None)
    with tempfile.TemporaryDirectory(prefix="bedrock-agda-dependencies-") as directory:
        seed = Path(directory) / "BedrockExternalDependencies.agda"
        imports = "\n".join(f"import {module}" for module in sorted(dependencies))
        seed.write_text(
            "{-# OPTIONS --cubical --safe --guardedness #-}\n"
            "module BedrockExternalDependencies where\n\n"
            f"{imports}\n",
            encoding="utf-8",
        )
        print(
            f"parallel Agda: precompiling {len(dependencies)} external dependencies",
            file=sys.stderr,
        )
        subprocess.run(
            [str(agda), "-i", directory, str(seed)],
            cwd=project_root,
            env=environment,
            check=True,
        )


def closure(graph: dict[str, set[str]], root: str) -> set[str]:
    if root not in graph:
        raise ValueError(f"unknown root module: {root}")
    found: set[str] = set()
    active: list[str] = []

    def visit(module: str) -> None:
        if module in active:
            cycle = active[active.index(module):] + [module]
            raise ValueError("project import cycle: " + " -> ".join(cycle))
        if module in found:
            return
        active.append(module)
        for dependency in sorted(graph[module]):
            visit(dependency)
        active.pop()
        found.add(module)

    visit(root)
    return found


def stale_modules(
    paths: dict[str, Path], graph: dict[str, set[str]], modules: set[str],
    interface_root: Path,
) -> set[str]:
    """Recheck changed modules and their dependants; leave warm interfaces alone."""
    stale: set[str] = set()
    visited: set[str] = set()

    def interface_for(module: str) -> Path:
        return interface_root / (module.replace(".", "/") + ".agdai")

    def visit(module: str) -> None:
        if module in visited:
            return
        for dependency in graph[module] & modules:
            visit(dependency)
        interface = interface_for(module)
        if not interface.exists():
            stale.add(module)
        else:
            built_at = interface.stat().st_mtime_ns
            dependencies = graph[module] & modules
            if (paths[module].stat().st_mtime_ns > built_at
                    or any(dependency in stale or
                           interface_for(dependency).stat().st_mtime_ns > built_at
                           for dependency in dependencies)):
                stale.add(module)
        visited.add(module)

    for module in modules:
        visit(module)
    return stale


def run_module(
    module: str,
    path: Path,
    *,
    project_root: Path,
    agda: Path,
    trace_dir: Path | None,
    run_id: str,
) -> tuple[str, subprocess.CompletedProcess[str]]:
    environment = os.environ.copy()
    environment.pop("BEDROCK_AGDA_TYPES", None)
    environment.pop("BEDROCK_AGDA_RUN", None)
    if trace_dir is not None:
        trace_path = trace_dir / f"{module}.jsonl"
        trace_path.parent.mkdir(parents=True, exist_ok=True)
        environment["BEDROCK_AGDA_TYPES"] = str(trace_path)
        environment["BEDROCK_AGDA_RUN"] = run_id
    command = [str(agda), str(path.relative_to(project_root))]
    result = subprocess.run(
        command,
        cwd=project_root,
        env=environment,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
    )
    return module, result


def parallel_check(
    *,
    project_root: Path,
    source_root: Path,
    root: str,
    agda: Path,
    jobs: int,
    trace_dir: Path | None = None,
    interface_root: Path | None = None,
) -> list[str]:
    paths, complete_graph = local_graph(source_root)
    modules = closure(complete_graph, root)
    if interface_root is not None:
        modules = stale_modules(paths, complete_graph, modules, interface_root)
    if not modules:
        print("parallel Agda: all project interfaces are current", file=sys.stderr)
        return []
    precompile_external_dependencies(
        project_root=project_root,
        agda=agda,
        dependencies=external_dependencies(paths, modules),
    )
    graph = {module: complete_graph[module] & modules for module in modules}
    dependants = {module: set() for module in modules}
    remaining = {module: len(graph[module]) for module in modules}
    for module, dependencies in graph.items():
        for dependency in dependencies:
            dependants[dependency].add(module)

    ready = [module for module, count in remaining.items() if count == 0]
    heapq.heapify(ready)
    completed: list[str] = []
    running: dict[Future[tuple[str, subprocess.CompletedProcess[str]]], str] = {}
    run_id = f"parallel-{time.time_ns()}-{os.getpid()}"
    failure: tuple[str, subprocess.CompletedProcess[str]] | None = None

    print(f"parallel Agda: {len(modules)} modules, {jobs} workers", file=sys.stderr)
    with ThreadPoolExecutor(max_workers=jobs) as executor:
        while ready or running:
            while ready and len(running) < jobs and failure is None:
                module = heapq.heappop(ready)
                future = executor.submit(
                    run_module,
                    module,
                    paths[module],
                    project_root=project_root,
                    agda=agda,
                    trace_dir=trace_dir,
                    run_id=run_id,
                )
                running[future] = module
            if not running:
                break
            done, _ = wait(running, return_when=FIRST_COMPLETED)
            for future in done:
                running.pop(future)
                module, result = future.result()
                if result.stdout:
                    sys.stderr.write(result.stdout)
                if result.returncode:
                    failure = (module, result)
                    continue
                completed.append(module)
                print(f"[{len(completed)}/{len(modules)}] {module}", file=sys.stderr)
                for dependant in dependants[module]:
                    remaining[dependant] -= 1
                    if remaining[dependant] == 0:
                        heapq.heappush(ready, dependant)

    if failure is not None:
        module, result = failure
        raise RuntimeError(f"Agda failed for {module} with exit code {result.returncode}")
    if len(completed) != len(modules):
        blocked = sorted(modules - set(completed))
        raise RuntimeError("parallel scheduler stalled: " + ", ".join(blocked))
    return completed


def merge_traces(
    trace_dir: Path, trace_out: Path, *, preserve_existing: bool = False,
    final_trace: Path | None = None,
) -> None:
    temporary = trace_out.with_suffix(trace_out.suffix + ".tmp")
    trace_out.parent.mkdir(parents=True, exist_ok=True)
    with temporary.open("wb") as destination:
        if preserve_existing and trace_out.exists():
            with trace_out.open("rb") as previous:
                shutil.copyfileobj(previous, destination)
        for path in sorted(trace_dir.rglob("*.jsonl")):
            if path == final_trace:
                continue
            with path.open("rb") as part:
                shutil.copyfileobj(part, destination)
        if final_trace is not None and final_trace.exists():
            with final_trace.open("rb") as final:
                shutil.copyfileobj(final, destination)
    temporary.replace(trace_out)


def run_html(
    agda: Path, project_root: Path, root_path: Path, html_dir: Path,
    trace_path: Path | None = None,
) -> None:
    environment = os.environ.copy()
    environment.pop("BEDROCK_AGDA_TYPES", None)
    environment.pop("BEDROCK_AGDA_RUN", None)
    if trace_path is not None:
        environment["BEDROCK_AGDA_TYPES"] = str(trace_path)
        environment["BEDROCK_AGDA_RUN"] = f"html-{time.time_ns()}-{os.getpid()}"
    subprocess.run(
        [str(agda), "--html", "--html-highlight=code", f"--html-dir={html_dir}",
         str(root_path.relative_to(project_root))],
        cwd=project_root,
        env=environment,
        check=True,
    )


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--agda", type=Path, required=True)
    parser.add_argument("--project-root", type=Path, default=Path.cwd())
    parser.add_argument("--src", type=Path, default=Path("src"))
    parser.add_argument("--root", default="Origin")
    parser.add_argument("--jobs", type=int, default=2)
    parser.add_argument("--trace-out", type=Path)
    parser.add_argument("--html-dir", type=Path)
    parser.add_argument("--incremental", action="store_true")
    parser.add_argument("--interface-root", type=Path)
    args = parser.parse_args()
    if args.jobs < 1:
        parser.error("--jobs must be at least 1")
    if args.incremental and args.interface_root is None:
        parser.error("--incremental requires --interface-root")

    project_root = args.project_root.resolve()
    source_root = (project_root / args.src).resolve()
    agda = args.agda.resolve()
    trace_out = args.trace_out.resolve() if args.trace_out else None
    trace_dir = trace_out.parent / (trace_out.name + ".parts") if trace_out else None
    interface_root = args.interface_root.resolve() if args.interface_root else None
    if trace_dir:
        shutil.rmtree(trace_dir, ignore_errors=True)
        trace_dir.mkdir(parents=True)

    paths, _ = local_graph(source_root)
    try:
        parallel_check(
            project_root=project_root,
            source_root=source_root,
            root=args.root,
            agda=agda,
            jobs=args.jobs,
            trace_dir=trace_dir,
            interface_root=interface_root if args.incremental else None,
        )
        if trace_dir and trace_out and not args.incremental:
            merge_traces(trace_dir, trace_out)
        final_trace = trace_dir / "html.jsonl" if trace_dir and args.incremental and args.html_dir else None
        if args.html_dir:
            html_dir = args.html_dir.resolve()
            html_dir.mkdir(parents=True, exist_ok=True)
            run_html(agda, project_root, paths[args.root], html_dir, final_trace)
        elif args.incremental:
            environment = os.environ.copy()
            environment.pop("BEDROCK_AGDA_TYPES", None)
            environment.pop("BEDROCK_AGDA_RUN", None)
            subprocess.run([str(agda), str(paths[args.root].relative_to(project_root))],
                           cwd=project_root, env=environment, check=True)
        if trace_dir and trace_out and args.incremental:
            merge_traces(trace_dir, trace_out, preserve_existing=True,
                         final_trace=final_trace)
    except (OSError, RuntimeError, ValueError, subprocess.CalledProcessError) as error:
        print(f"agda-parallel: {error}", file=sys.stderr)
        return 1
    finally:
        if trace_dir:
            shutil.rmtree(trace_dir, ignore_errors=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
