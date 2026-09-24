#!/usr/bin/env python3
"""Build the two-cluster OFL font used only for ⇒̇ and ¬̇.

Reproduce with:
  uv run --no-project --with fonttools --with brotli --with uharfbuzz \
    python scripts/site/build-dotted-operator-font.py
The regular site build uses the checked-in WOFF2 and needs none of these tools.
"""
from io import BytesIO
from pathlib import Path

from fontTools import subset
from fontTools.feaLib.builder import addOpenTypeFeaturesFromString
from fontTools.ttLib import TTFont
import uharfbuzz as hb

ROOT = Path(__file__).resolve().parents[2]
FONT_DIR = ROOT / "site/static/fonts"


def main():
    font = TTFont(FONT_DIR / "JuliaMono-Regular.woff2", recalcTimestamp=False)
    original = {cp: font["hmtx"][font.getBestCmap()[cp]][0]
                for cp in (0x21D2, 0xAC)}
    options = subset.Options()
    options.layout_features = []
    options.name_IDs = [0, 1, 2, 3, 4, 5, 6, 13, 14, 16, 17]
    worker = subset.Subsetter(options=options)
    worker.populate(unicodes=[0x21D2, 0xAC, 0x0307])
    worker.subset(font)
    for tag in ("GPOS", "GSUB", "GDEF"):
        if tag in font:
            del font[tag]
    cmap = font.getBestCmap()
    arrow, negation, dot = [cmap[cp] for cp in (0x21D2, 0xAC, 0x0307)]
    # Keep JuliaMono's outlines, baseline and 1200-unit cell. The original
    # positive-width mark has no attachment on these bases; make it a mark
    # and attach its centre to the centre of each unchanged base cell.
    font["hmtx"][dot] = (0, font["hmtx"][dot][1])
    addOpenTypeFeaturesFromString(font, f"""
        languagesystem DFLT dflt;
        languagesystem latn dflt;
        markClass {dot} <anchor 600 0> @DOT;
        feature mark {{
            pos base {arrow} <anchor 600 0> mark @DOT;
            pos base {negation} <anchor 600 0> mark @DOT;
        }} mark;
    """)
    names = {1: "Bedrock Dotted Operators", 2: "Regular",
             3: "BedrockDottedOperators-Regular-1.0",
             4: "Bedrock Dotted Operators Regular", 5: "Version 1.000",
             6: "BedrockDottedOperators-Regular",
             16: "Bedrock Dotted Operators", 17: "Regular"}
    for record in font["name"].names:
        if record.nameID in names:
            record.string = names[record.nameID].encode(record.getEncoding())
    # Verify shaping rather than merely character coverage. Both clusters
    # retain exactly one original cell, with zero-advance, centred marks.
    font.flavor = None
    buffer = BytesIO()
    font.save(buffer)
    shaped_font = hb.Font(hb.Face(buffer.getvalue()))
    for text in ("⇒̇", "¬̇"):
        run = hb.Buffer()
        run.add_str(text)
        run.guess_segment_properties()
        hb.shape(shaped_font, run)
        positions = run.glyph_positions
        assert len(positions) == 2
        assert positions[0].x_advance == original[ord(text[0])]
        assert positions[1].x_advance == 0
        assert positions[0].x_advance + positions[1].x_offset == 0
    font.flavor = "woff2"
    target = FONT_DIR / "BedrockDottedOperators-Regular.woff2"
    font.save(target)
    print(f"Verified both clusters; wrote {target.name} ({target.stat().st_size} bytes)")


if __name__ == "__main__":
    main()
