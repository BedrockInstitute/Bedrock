"""Locate actual module code for legacy DOM-unit scenarios.

New state-machine tests import the public ES modules directly. These adapters
retain old minimal-DOM behavioral tests without depending on bundle ordering.
"""
from pathlib import Path
from outcrop import site as site_package
RESOURCES = Path(site_package.__file__).resolve().parent / "resources"
import re

READER = RESOURCES / 'static/reader'


def source(*modules):
    return '\n'.join((READER / (module + '.js')).read_text() for module in modules)


def functions(module, *names):
    code = source(module)
    result = []
    for name in names:
        match = re.search(r'^( *)(?:export )?function ' + re.escape(name)
                          + r'\([^\n]*\) \{', code, re.M)
        if not match:
            raise AssertionError(f'{module}: function {name} not found')
        end = re.search(r'^' + match[1] + r'\}', code[match.end():], re.M)
        result.append(code[match.start():match.end() + end.end()].replace('export function ', 'function ', 1))
    return '\n'.join(result)
