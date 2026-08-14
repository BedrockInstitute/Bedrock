#!/usr/bin/env python3
"""[LJ-1.210] the class-parameter SURFACE census.

For each master it reports:
  code   in-fence non-blank lines (the DD8 method)
  hdr    header lines that FIX the class: an import from L.Constructible or
         L.Axioms, an `open hPropStructure 𝒮ʟ`, or a module application that
         passes `isL`
  body   remaining in-fence lines that name `isL`, `𝒮ʟ` or an L-only fact
  facts  the L-only facts the master imports, which become hypotheses on a
         generic class

Run it from the repository root.
"""

import re
import sys

HDR = re.compile(
    r"(L\.Constructible|L\.Axioms\.|open hPropStructure 𝒮ʟ|hPropStructure 𝒮ʟ"
    r"|FOL\.Absoluteness\.Single 𝒮ᵥ isL|FOL\.ZFModel 𝒮ʟ|FOL\.Coding .*𝒮ʟ)"
)
BODY = re.compile(r"𝒮ʟ|isL")
FACTS = re.compile(
    r"hasSeparationL|hasPowerL|hasUnionL|ωʟ|ω-specL|LsetS|𝒟ₒ→isL|Lset-suc"
    r"|pr∈Lset-suc|finSet|numeralL|pairʟ|sucʟ|unionʟ|AtStage|isL-trans"
)


def fence_lines(path: str) -> list[str]:
    out: list[str] = []
    inside = False
    for line in open(path, encoding="utf-8"):
        s = line.rstrip("\n")
        if s.startswith("```agda"):
            inside = True
            continue
        if s.startswith("```"):
            inside = False
            continue
        if inside and s.strip():
            out.append(s)
    return out


def main() -> None:
    tot_code = tot_hdr = tot_body = 0
    print("master\tcode\thdr\tbody")
    for path in sys.argv[1:]:
        lines = fence_lines(path)
        hdr = [x for x in lines if HDR.search(x)]
        body = [x for x in lines if BODY.search(x) and x not in hdr]
        facts = sorted({m for x in lines for m in FACTS.findall(x)})
        tot_code += len(lines)
        tot_hdr += len(hdr)
        tot_body += len(body)
        print(f"{path}\t{len(lines)}\t{len(hdr)}\t{len(body)}")
        if facts:
            print(f"    facts: {' '.join(facts)}")
    print(f"TOTAL\t{tot_code}\t{tot_hdr}\t{tot_body}")


if __name__ == "__main__":
    main()
