"""Publish a coherent, immutable snapshot of the browser module graph.

Native relative imports stay native: all JavaScript files share one digest
directory. Changing a worker or any transitive dependency changes every entry
URL, so a cached entry cannot accidentally load a different runtime generation.
No JavaScript parser, package manager or external bundler is required.
"""
from pathlib import Path
import hashlib


class AssetBundle:
    """Capture once, then publish exactly what was hashed, even during edits."""
    def __init__(self, source, *, project_assets=None):
        root = Path(source)
        self.files = {path.relative_to(root).as_posix(): path.read_bytes()
                      for path in sorted(root.rglob('*')) if path.is_file()
                      and 'runtime' not in path.relative_to(root).parts
                      and path.relative_to(root).parts[0] != 'assets'}
        self.files.update(project_assets or {})
        digest = hashlib.sha256()
        for name, data in self.files.items():
            if name.endswith('.js'):
                digest.update(name.encode() + b'\0' + data + b'\0')
        self.runtime = 'runtime/' + digest.hexdigest()[:16]

    def template(self, template):
        slots = {'CSS': 'bedrock.css', 'ROUTECSS': 'reading-routes.css',
                 'ASKCSS': 'ask-ai.css', 'APPEARANCECSS': 'appearance.css'}
        for slot, name in slots.items():
            version = hashlib.sha256(self.files.get(name, b'')).hexdigest()[:16]
            template = template.replace('%%' + slot + 'VER%%', version)
        return template.replace('%%RUNTIME%%', self.runtime)

    def publish(self, destination):
        root = Path(destination)
        for name, data in self.files.items():
            target = root / name
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes(data)
            if name.endswith('.js'):
                target = root / self.runtime / name
                target.parent.mkdir(parents=True, exist_ok=True)
                target.write_bytes(data)
