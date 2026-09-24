"""Shared source-level Agda fence/import grammar; no project discovery."""
import re

AGDA_FENCE = re.compile(r'^```agda\s*\n(.*?)^```\s*$', re.M | re.S)
IMPORT = re.compile(r'^\s*(?:open\s+)?import\s+([\w.]+)', re.M)


def imports(text):
    return [name for block in AGDA_FENCE.findall(text) for name in IMPORT.findall(block)]
