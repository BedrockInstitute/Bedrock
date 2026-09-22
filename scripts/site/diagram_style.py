"""Source contract for textbook figures; geometry is local, appearance is shared."""
from html.parser import HTMLParser
from pathlib import Path
import re

FIGURE = re.compile(r'<figure\b.*?</figure>', re.S)
SHAPES = {'path', 'circle', 'rect', 'line', 'polyline', 'polygon', 'ellipse'}
ROLES = {
    'path': {'diagram-path', 'diagram-map-line', 'diagram-map-tip',
             'diagram-guide', 'diagram-higher-path', 'diagram-path-space'},
    'circle': {'diagram-point', 'diagram-centre-ring'},
    'rect': {'diagram-space-shape'},
    'line': {'diagram-map-line', 'diagram-guide'},
    'polyline': {'diagram-map-line', 'diagram-map-tip', 'diagram-guide'},
    'polygon': {'diagram-higher-path'},
    'ellipse': {'diagram-higher-path'},
}
GEOMETRY = {'left', 'top', 'aspect-ratio'}
PAINT = {'fill', 'stroke', 'stroke-width', 'stroke-dasharray', 'opacity',
         'color', 'rx', 'ry', 'marker-start', 'marker-mid', 'marker-end',
         'fill-opacity', 'stroke-opacity', 'stroke-linecap', 'stroke-linejoin',
         'stroke-dashoffset', 'stroke-miterlimit', 'vector-effect', 'filter',
         'transform', 'classid'}
VOID = {'br', 'hr', 'img', 'input', 'meta', 'link', 'wbr', 'source'}


class Node:
    def __init__(self, tag, attrs=(), parent=None):
        self.tag, self.attrs, self.parent = tag, dict(attrs), parent
        self.children = []

    @property
    def classes(self):
        return set(self.attrs.get('class', '').split())

    def descendants(self):
        for child in self.children:
            yield child
            yield from child.descendants()


class Tree(HTMLParser):
    def __init__(self, source):
        super().__init__()
        self.root = self.current = Node('root')
        self.feed(source)

    def handle_starttag(self, tag, attrs):
        node = Node(tag, attrs, self.current)
        self.current.children.append(node)
        if tag not in VOID:
            self.current = node

    def handle_startendtag(self, tag, attrs):
        self.handle_starttag(tag, attrs)
        if tag not in VOID:
            self.handle_endtag(tag)

    def handle_endtag(self, tag):
        node = self.current
        while node.parent:
            if node.tag == tag:
                self.current = node.parent
                return
            node = node.parent


def path_endpoints(data):
    """Endpoints of open absolute SVG subpaths. Reject ambiguous/unsupported syntax."""
    tokens = re.findall(r'[A-Za-z]|[-+]?(?:\d*\.\d+|\d+\.?\d*)(?:[eE][-+]?\d+)?', data)
    pos = start = None
    result = []
    arity = {'M': 2, 'L': 2, 'H': 1, 'V': 1, 'Q': 4, 'C': 6, 'S': 4, 'T': 2}
    i = 0
    while i < len(tokens):
        op = tokens[i]
        if op not in arity:
            raise ValueError('ordinary paths use explicit absolute M/L/H/V/Q/C/S/T commands')
        n = arity[op]
        try:
            nums = list(map(float, tokens[i + 1:i + n + 1]))
        except ValueError as error:
            raise ValueError('invalid path geometry') from error
        if len(nums) != n or (pos is None and op != 'M'):
            raise ValueError('invalid path geometry')
        if op == 'M':
            if start is not None:
                result.extend((start, pos))
            pos = start = tuple(nums)
        elif op == 'H': pos = (nums[0], pos[1])
        elif op == 'V': pos = (pos[0], nums[0])
        else: pos = tuple(nums[-2:])
        i += n + 1
    if start is not None:
        result.extend((start, pos))
    return result


def check_text(source):
    errors, seen = [], set()
    # Code examples are not figures. Preserve line offsets for useful diagnostics.
    source = re.sub(r'^(`{3,}|~{3,})[^\n]*\n.*?^\1\s*$',
                    lambda m: '\n' * m[0].count('\n'), source, flags=re.M | re.S)
    previous_end = None
    for match in FIGURE.finditer(source):
        line = source.count('\n', 0, match.start()) + 1
        fragment = match[0]
        tree = Tree(fragment)
        figure = tree.root.children[0]
        nodes = list(figure.descendants())
        ident = figure.attrs.get('id', '')
        def fail(message): errors.append(f'{line}: {ident or "figure"}: {message}')
        if 'book-diagram' not in figure.classes: fail('use the shared book-diagram component')
        if not re.fullmatch(r'fig-[a-z0-9]+(?:-[a-z0-9]+)*', ident): fail('use a stable fig-* id')
        if ident in seen: fail('duplicate figure id')
        seen.add(ident)
        if 'diagram-panel' in figure.classes or 'diagram-space' in figure.classes:
            fail('frame only the content wrapper; keep the figure and caption unframed')
        frames = [n for n in [figure] + nodes if 'diagram-framed' in n.classes]
        if frames:
            if len(frames) != 1 or frames[0].tag != 'div' or frames[0].parent is not figure:
                fail('diagram-framed must be one direct content div, never the figure or caption')
            elif len(figure.children) != 2 or figure.children[0] is not frames[0] or figure.children[1].tag != 'figcaption':
                fail('a framed figure must contain its content div followed by an unframed sibling figcaption')
        captions = [n for n in nodes if n.tag == 'figcaption']
        if len(captions) != 1 or captions[0].parent is not figure:
            fail('require one direct figcaption, outside the panels')
        elif captions[0].attrs.get('id') != ident + '-caption':
            fail('caption id must be fig-id-caption')
        elif figure.children[-1] is not captions[0]:
            fail('place the caption after the diagram')
        if figure.attrs.get('aria-describedby') != ident + '-caption':
            fail('link the figure to its caption with aria-describedby')
        cap = re.search(r'<figcaption\b[^>]*>(.*?)</figcaption>', fragment, re.S)
        if cap:
            for lang in ('en', 'zh', 'ja'):
                block = re.search(r'<!--'+lang+r'-->\s*(.*?)\s*(?=<!--(?:en|zh|ja|/)-->)', cap[1], re.S)
                if not block or not re.sub(r'<[^>]*>|\s', '', block[1]):
                    fail(f'caption needs explicit {lang} text')
        if previous_end is not None:
            between = re.sub(r'<!--.*?-->|<[^>]*>', '', source[previous_end:match.start()], flags=re.S)
            between = re.sub(r'\$\$.*?\$\$|\$[^$\n]+\$|`[^`]+`', '', between, flags=re.S)
            if not re.search(r'[A-Za-z\u3040-\u30ff\u3400-\u9fff]', between):
                fail('separate successive figures with substantive prose')
        previous_end = match.end()
        for node in [figure] + nodes:
            for declaration in node.attrs.get('style', '').split(';'):
                if declaration.strip() and declaration.split(':')[0].strip() not in GEOMETRY:
                    fail('inline style is limited to left, top and aspect-ratio; use shared CSS')
            if PAINT & node.attrs.keys(): fail('paint, arrow markers and corner radii belong in shared CSS')
            if node.tag in {'style', 'script', 'img', 'iframe', 'foreignobject', 'use', 'marker',
                            'lineargradient', 'radialgradient', 'pattern', 'filter', 'animate', 'set'}:
                fail(f'{node.tag} bypasses the shared diagram grammar')
            if node.tag in SHAPES and len(node.classes & ROLES.get(node.tag, set())) != 1:
                fail(f'{node.tag} needs one shared mathematical role class')
            if 'diagram-panel' in node.classes:
                parent = node.parent
                while parent is not figure and parent is not None:
                    if 'diagram-panel' in parent.classes: fail('do not nest decorative panels')
                    parent = parent.parent
            if node.tag == 'svg':
                if not node.attrs.get('viewbox'): fail('SVG needs a responsive viewBox')
                if node.attrs.get('aria-hidden') != 'true' or node.attrs.get('focusable') != 'false':
                    fail('SVG geometry must be aria-hidden and nonfocusable; use visible math labels')
                descendants = list(node.descendants())
                points = []
                for point in descendants:
                    if 'diagram-point' in point.classes:
                        try:
                            points.append((float(point.attrs['cx']), float(point.attrs['cy'])))
                            if float(point.attrs['r']) <= 0: fail('endpoint radius must be positive')
                        except (ValueError, KeyError): fail('endpoint needs numeric cx, cy and r')
                for path in descendants:
                    if 'diagram-path' not in path.classes: continue
                    try:
                        endpoints = path_endpoints(path.attrs.get('d', ''))
                        if not endpoints: fail('ordinary path needs geometry')
                        for endpoint in endpoints:
                            if not any(abs(endpoint[0]-p[0]) < .01 and abs(endpoint[1]-p[1]) < .01 for p in points):
                                fail(f'ordinary path endpoint {endpoint} needs a white diagram-point')
                    except ValueError as error: fail(str(error))
    if len(re.findall(r'<figure\b', source)) != len(seen):
        errors.append('unclosed or duplicate figure')
    return errors


def check_sources(paths):
    return [f'{path}:{error}' for path in paths for error in check_text(Path(path).read_text())]
