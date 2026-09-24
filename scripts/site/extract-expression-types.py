#!/usr/bin/env python3
"""Supply Bedrock's trace paths to Outcrop's expression adapter."""
import sys
from outcrop.adapters.extract_expression_types import main

if __name__ == '__main__':
    raise SystemExit(main(['--src', 'src', '--html-dir', '_build/html',
        '--trace', '_build/outcrop-agda-types.jsonl', '--out', '_build/expression-types.json',
        *sys.argv[1:]]))
