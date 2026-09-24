#!/usr/bin/env python3
"""Supply Bedrock's entry point and library to Outcrop's Agda adapter."""
import sys
from outcrop.adapters.extract_types import main

if __name__ == '__main__':
    raise SystemExit(main(['--src', 'src', '--html-dir', '_build/html',
                          '--entry', 'Origin', '--libraries', 'cubical', *sys.argv[1:]]))
