#!/usr/bin/env python3
"""LJ-1.158: collapse one master's module telescope into ONE record parameter.

`[LJ-1.155]` measured the cure and this script LANDS it. It moves every
hypothesis VERBATIM: the text of a field is the text of the telescope
hypothesis, shifted by one column and with its outer parentheses removed.
Nothing is retyped, so the collapse cannot change what a theorem says.

The named hypotheses in `keep` stay in the telescope. **`sucK` is always kept**,
because `[LJ-1.155]` measured that `sucV` in a RECORD FIELD type exhausts an
8 GB heap and that the same field costs 2.02 s with that one token removed
(probes B8, B11, B12; `dev/LESSONS.md` P-x).

Usage:
    apply_collapse.py <upper|lower|twelve>
"""
from __future__ import annotations

import pathlib
import sys

ROOT = pathlib.Path("/Users/alsg/Agentic/Bedrock")

# key -> (path, record name, module name, record binder, kept in telescope,
#         module header line, first hypothesis line, last hypothesis line)
# The three line numbers are 1-indexed and inclusive, at HEAD `0e4ddcd`.
PLAN = {
    "upper": ("src/L/Condensation/UpperAgree.lagda.md", "UFacts", "UpperAgree",
              "uf", ["sucK"], 77, 80, 178),
    "lower": ("src/L/Condensation/LowerAgree.lagda.md", "LFacts", "LowerAgree",
              "lf", [], 76, 79, 187),
    "twelve": ("src/L/Condensation/TwelveAgree.lagda.md", "TFacts", "AbstractFrame",
               "tf", ["sucK"], 114, 117, 287),
}

NOTE = """-- THE FRAME'S FACT BLOCK, as ONE record rather than {count} telescope
-- hypotheses.  `[LJ-1.62]` states the reason at `src/L/Condensation.lagda.md`
-- :5990-5994, and these masters never got it: a module telescope is prepended
-- to the STORED TYPE of every definition inside the module, and Agda's
-- `DeadCode.DeadCodeReachable` pass then walks those stored types once per
-- definition.
--
-- MEASURED by `[LJ-1.158]`, a controlled pair of probes over THIS telescope,
-- two runs each side: {measure}
--
-- `sucK` STAYS A TELESCOPE HYPOTHESIS and is never a field.  `[LJ-1.155]`
-- measured `sucV` in a record field type at an 8 GB heap wall, and the same
-- field at 2.02 s with that one token removed (P-x).
"""


def groups(lines: list[str]) -> list[list[str]]:
    """Split telescope source into one list of lines per parenthesised hypothesis."""
    out: list[list[str]] = []
    depth, cur = 0, []
    for line in lines:
        cur.append(line)
        depth += line.count("(") - line.count(")")
        if depth == 0:
            out.append(cur)
            cur = []
    assert depth == 0 and not cur, "unbalanced telescope"
    return out


def as_field(group: list[str]) -> list[str]:
    """The same text as a record field: outer parens gone, one column right."""
    body = list(group)
    assert body[0].startswith("  ("), body[0]
    body[0] = "    " + body[0][3:]
    for i in range(1, len(body)):
        body[i] = " " + body[i]
    assert body[-1].endswith(")"), body[-1]
    body[-1] = body[-1][:-1]
    return body


CALLSITE_NOTE = """  -- THE TWO PARTIALS' FACT BLOCKS, built ONCE from this frame's own record.
  -- Before `[LJ-1.158]` the six call sites below listed every hypothesis by
  -- name, so the same {n0} and {n1} arguments were written six times.  The
  -- archived `asRecursion`
  -- (archive/src/2026-08-09-rud-route/L/Recursion.lagda.md:320) is the same
  -- move: one record built from another record's fields.
  --
  -- `arityK` is DERIVED here from `transK` and is a HYPOTHESIS of
  -- `UpperAgree`, so `uf` supplies the derivation.  That is what the
  -- positional call sites did before, and it discharges nothing (C-38).
"""


def record_fields(key: str) -> list[str]:
    """The field names of the record this script already wrote into that master.

    It reads the DELIVERED record rather than the old telescope, because the
    telescope is gone by the time the call sites are rewritten.
    """
    path, rec = PLAN[key][0], PLAN[key][1]
    lines = (ROOT / path).read_text().split("\n")
    i = next(j for j, s in enumerate(lines) if s.startswith(f"record {rec} "))
    i = next(j for j in range(i, len(lines)) if lines[j] == "  field")
    out = []
    for line in lines[i + 1 :]:
        if not line.startswith("    "):
            break                       # the record's field block has ended
        if line.startswith("     "):
            continue                    # a field's continuation line
        out.append(line.strip().split(":")[0].strip())
    return out


def callsites() -> int:
    """Rewrite `TwelveAgree`'s six positional call sites to pass ONE record each."""
    path = ROOT / PLAN["twelve"][0]
    src = path.read_text()
    lo = record_fields("lower")
    up = record_fields("upper")
    args = "N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1 K γ'"

    def build(name: str, rec: str, fields: list[str]) -> str:
        out = f"  {name} : {rec} {{n}} {args}\n  {name} = record\n"
        for i, f in enumerate(fields):
            out += f"    {'{' if i == 0 else ';'} {f} = {f}\n"
        return out[:-1] + " }\n"

    block = CALLSITE_NOTE.format(n0=len(lo), n1=len(up))
    block += build("lf", "LFacts", lo) + "\n" + build("uf", "UFacts", up)
    assert "  p0b : Formula S (11 + n)\n" in src
    src = src.replace("  p0b : Formula S (11 + n)\n",
                      block + "\n  p0b : Formula S (11 + n)\n", 1)
    path.write_text(src)
    print(f"{path}: `lf` built with {len(lo)} fields, `uf` with {len(up)}. "
          f"The four call sites are edited by hand.")
    return 0


def main() -> int:
    key = sys.argv[1]
    if key == "twelve-callsites":
        return callsites()
    path, rec, mod, binder, keep, head, first, last = PLAN[key]
    src = (ROOT / path).read_text().split("\n")
    lead = src[head : first - 1]
    gs = groups(src[first - 1 : last])
    names = [g[0].split(":")[0].strip().lstrip("(") for g in gs]
    fields = [g for g, nm in zip(gs, names) if nm not in keep]
    tele = [g for g, nm in zip(gs, names) if nm in keep]
    args = " ".join(l.strip().lstrip("(").rstrip(")").split(":")[0].strip() for l in lead)

    out = src[: head - 1]
    out += NOTE.format(count=len(gs), measure=MEASURE[key]).split("\n")[:-1]
    out += [f"record {rec} {{n : ℕ}}"] + lead[:-1] + [lead[-1] + " : Type (ℓ-suc ℓ) where",
                                                     "  field"]
    for g in fields:
        out += as_field(g)
    out += ["", f"module {mod} {{n : ℕ}}"] + lead
    for g in tele:
        out += g
    out += [f"  ({binder} : {rec} {args})", "  where", "",
            f"  open {rec} {binder}"]
    assert src[last].strip() == "where", src[last]
    out += src[last + 1:]
    (ROOT / path).write_text("\n".join(out))
    print(f"{path}: {len(fields)} fields in `{rec}`, "
          f"{len(tele)} kept in the telescope ({', '.join(keep) or 'none'})")
    return 0


#: The controlled pair this master's own collapse rests on. Every figure is a
#: mean of two runs, `--profile=internal`, cold, warm-up discarded.
MEASURE = {
    "upper": "`DeadCode` 2,652 ms to 25 ms and the probe file minus 52 percent "
             "(`[LJ-1.155]` probes B1 and B10).",
    "lower": "`DeadCode` 2,689 ms to 26 ms and the probe file 7,243 ms to 3,726, "
             "minus 49 percent (probes L1 and L2).",
    "twelve": "`DeadCode` 13,018 ms to 95 ms and the probe file 20,958 ms to 6,421, "
              "minus 69 percent (probes T1 and T2).",
}


if __name__ == "__main__":
    raise SystemExit(main())
