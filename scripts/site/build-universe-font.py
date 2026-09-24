#!/usr/bin/env python3
"""Subset the official Noto Sans Math 3.000 release for universe notation.

Download NotoSansMath-v3.000.zip from
https://github.com/notofonts/math/releases/tag/NotoSansMath-v3.000
and pass its full/ttf/NotoSansMath-Regular.ttf to:
  uv run --no-project --with fonttools --with brotli \
    python scripts/site/build-universe-font.py /path/to/NotoSansMath-Regular.ttf
Ordinary site builds use the checked-in WOFF2; no download is required.
"""
import hashlib
from pathlib import Path
import sys

from fontTools import subset
from fontTools.ttLib import TTFont
from fontTools.pens.ttGlyphPen import TTGlyphPen

SHA256 = '7283c396e9b22699bb542d9631030dc804a7e5b954f193d8f8f5b5f1162fbc61'
ROOT = Path(__file__).resolve().parents[2]


def main():
    source = Path(sys.argv[1])
    if hashlib.sha256(source.read_bytes()).hexdigest() != SHA256:
        raise SystemExit('Expected the official full TTF from Noto Sans Math 3.000')
    font = TTFont(source, recalcTimestamp=False)
    # Noto Math leaves Unicode sub/superscript digits to the math layout engine.
    # Supply those codepoints from its own digits using its MATH constants,
    # rather than silently mixing JuliaMono suffixes with Noto's ell.
    constants = font['MATH'].table.MathConstants
    scale = constants.ScriptPercentScaleDown / 100
    superscripts = '⁰¹²³⁴⁵⁶⁷⁸⁹⁺⁻⁼⁽⁾'
    subscripts = '₀₁₂₃₄₅₆₇₈₉₊₋₌₍₎'
    cmap = font.getBestCmap()
    order = list(font.getGlyphOrder())
    for symbols, shift in ((superscripts, constants.SuperscriptShiftUp.Value),
                           (subscripts, -constants.SubscriptShiftDown.Value)):
        for base, symbol in zip('0123456789+-=()', symbols):
            if ord(symbol) in cmap:
                continue
            name = f'level{ord(symbol):04X}'
            base_name = cmap[ord(base)]
            pen = TTGlyphPen(font.getGlyphSet())
            pen.addComponent(base_name, (scale, 0, 0, scale, 0, shift))
            font['glyf'][name] = pen.glyph()
            order.append(name)
            width, bearing = font['hmtx'][base_name]
            font['hmtx'][name] = (round(width * scale), round(bearing * scale))
            for table in font['cmap'].tables:
                if table.isUnicode():
                    table.cmap[ord(symbol)] = name
    font.setGlyphOrder(order)
    options = subset.Options()
    options.name_IDs = [0, 1, 2, 3, 4, 5, 6, 13, 14, 16, 17]
    options.layout_features = ['ccmp', 'mark', 'mkmk', 'kern']
    worker = subset.Subsetter(options=options)
    characters = set(range(0x20, 0x7f)) | set(range(0x300, 0x400))
    characters |= set(range(0x1d00, 0x1dc0)) | set(range(0x2070, 0x20a0))
    characters |= set(range(0x2032, 0x2038)) | {0x2113, 0x2294, 0x2019, 0x2057, 0xb2, 0xb3, 0xb9}
    worker.populate(unicodes=characters)
    worker.subset(font)
    names = {1: 'Bedrock Universe Levels', 2: 'Regular',
             3: 'BedrockUniverseLevels-Regular-3.000',
             4: 'Bedrock Universe Levels Regular', 6: 'BedrockUniverseLevels-Regular',
             16: 'Bedrock Universe Levels', 17: 'Regular'}
    for record in font['name'].names:
        if record.nameID in names:
            record.string = names[record.nameID].encode(record.getEncoding())
    assert set(map(ord, "ℓℓ₀₁₂₃₄₅₆₇₈₉⁰¹²³⁴⁵⁶⁷⁸⁹⁺′″‴⁗'0 ⊔ (α β)")) <= set(font.getBestCmap())
    font.flavor = 'woff2'
    target = ROOT / 'site/static/fonts/BedrockUniverseLevels-Regular.woff2'
    font.save(target)
    print(f'Verified level symbols; wrote {target.name} ({target.stat().st_size} bytes)')


if __name__ == '__main__':
    main()
