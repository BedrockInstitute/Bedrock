"""Regenerate the example's optional compiler package in a build directory.

The ordinary website build uses the recorded semantic/ package and does not
need Agda. This maintainer command never changes the authored Markdown files.
"""
import argparse
import json
import os
from pathlib import Path
import subprocess
import sys

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--agda', type=Path, required=True)
parser.add_argument('--staging', type=Path, required=True)
args = parser.parse_args()
example = Path(__file__).resolve().parent
staging = args.staging.resolve()
sources = staging / 'sources'
for path in (example / 'chapters').rglob('*.md'):
    target = sources / path.relative_to(example / 'chapters').with_suffix('.lagda.md')
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_bytes(path.read_bytes())
output = staging / 'html'
trace = staging / 'trace.jsonl'
environment = {**os.environ, 'GHCRTS': '-A64m -I0 -M8g',
    'BEDROCK_AGDA_TYPES': str(trace), 'BEDROCK_AGDA_RUN': 'lantern-fixture'}
subprocess.run([str(args.agda.resolve()), '--no-libraries', '-i', str(sources),
    '--html', '--html-highlight=code', '--html-dir=' + str(output),
    str(sources / 'Welcome.lagda.md')], env=environment, check=True)
scripts = example.parents[1] / 'scripts/site'
subprocess.run([sys.executable, str(scripts / 'extract-expression-types.py'),
    '--src', str(sources), '--html-dir', str(output), '--trace', str(trace),
    '--out', str(staging / 'expressions.json')], check=True)
subprocess.run([sys.executable, str(scripts / 'extract-types.py'),
    '--agda', str(args.agda.resolve()), '--src', str(sources),
    '--html-dir', str(output), '--entry', 'Welcome', '--libraries', '',
    '--out', str(staging / 'types.json')], env=environment, check=True)
print(staging)
