#!/usr/bin/env python3
"""Run one agda invocation under the heap cap and a wall-clock cap.

Usage: run_one.py <file.agda> <timeout-seconds> <label>

- deletes the file's interface under _build/2.8.0/agda/ (cold run)
- records load before and after (1-minute average, os.getloadavg)
- runs `agda` with GHCRTS="-A64m -I0 -M8g"
- writes a raw run log to agents/tasks/LJ-1-217/runs/<label>.txt
"""
import os, subprocess, sys, time, signal

def main():
    file = sys.argv[1]
    timeout_s = int(sys.argv[2])
    label = sys.argv[3]

    # interface path mirrors agda's _build layout
    rel = os.path.relpath(file)
    # agda writes _build/<version>/agda/<rel-with-.agda->.agdai>
    parts = rel.split(os.sep)
    stem = parts[-1][:-5] + ".agdai"  # strip .agda
    iface = os.path.join("_build", "2.8.0", "agda", *parts[:-1], stem)

    if os.path.exists(iface):
        os.remove(iface)
        iface_state = "deleted"
    else:
        iface_state = "absent"

    outdir = "agents/tasks/LJ-1-217/runs"
    os.makedirs(outdir, exist_ok=True)
    logpath = os.path.join(outdir, label + ".txt")

    env = dict(os.environ)
    env["GHCRTS"] = "-A64m -I0 -M8g"

    load_before = os.getloadavg()
    t0 = time.monotonic()
    wall = -1
    exit_code = -1
    killed = False
    err = ""

    proc = subprocess.Popen(
        ["agda", file], env=env,
        stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True,
    )
    try:
        out, err = proc.communicate(timeout=timeout_s)
        exit_code = proc.returncode
        wall = time.monotonic() - t0
    except subprocess.TimeoutExpired:
        # interrupt, then report elapsed seconds
        proc.send_signal(signal.SIGINT)
        try:
            out, err = proc.communicate(timeout=10)
        except subprocess.TimeoutExpired:
            proc.kill()
            out, err = proc.communicate()
        wall = time.monotonic() - t0
        killed = True
        exit_code = "TIMEOUT"

    load_after = os.getloadavg()

    with open(logpath, "w") as f:
        f.write(f"# label {label}\n")
        f.write(f"# file {file}\n")
        f.write(f"# interface {iface} ({iface_state})\n")
        f.write(f"# load before 1m {load_before[0]:.2f}\n")
        f.write(f"# wall seconds {wall:.3f}\n")
        f.write(f"# exit {exit_code}\n")
        f.write(f"# killed {killed}\n")
        f.write(f"# load after 1m {load_after[0]:.2f}\n")
        f.write("---- stdout ----\n")
        f.write(out or "")
        f.write("\n---- stderr ----\n")
        f.write(err or "")
        f.write("\n")

    print(f"label={label} wall={wall:.3f}s exit={exit_code} killed={killed} "
          f"load_before={load_before[0]:.2f} load_after={load_after[0]:.2f}")

if __name__ == "__main__":
    main()
