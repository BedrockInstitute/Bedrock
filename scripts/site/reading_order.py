"""Catalog order validation shared by lint and website adapters."""
from collections import Counter
from source_syntax import imports


def reading_order_errors(sources, catalog, *, previews=()):
    order = [entry['id'] for entry in catalog['chapters']]
    expected, actual = set(sources), set(order)
    errors = [f'missing chapter: {name}' for name in sorted(expected - actual)]
    errors += [f'unknown catalog chapter: {name}' for name in sorted(actual - expected)]
    errors += [f'duplicate chapter: {name}' for name, n in Counter(order).items() if n > 1]
    position = {name: i for i, name in enumerate(order)}
    for name in order:
        if name in previews or name not in expected:
            continue
        for dependency in dict.fromkeys(imports(sources[name])):
            if dependency not in expected:
                continue
            if dependency in previews:
                errors.append(f'{name} depends on preview {dependency}, not its proving chapter')
            elif dependency in position and position[dependency] >= position[name]:
                errors.append(f'{name} precedes prerequisite {dependency}')
    return errors
