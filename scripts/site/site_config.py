"""Validated project configuration for the reusable textbook website.

Configuration is data. It cannot name Python modules, templates containing code,
or providers to execute. Input paths are confined to an explicit project root.
"""
from pathlib import Path, PurePosixPath
from urllib.parse import urlsplit
import json
import re
from copy import deepcopy

LANG_LABELS = {'en': 'English', 'zh': '中文', 'ja': '日本語'}


def relative_path(value, field):
    if not isinstance(value, str) or not value or '\\' in value:
        raise ValueError(f'{field}: expected a relative POSIX path')
    path = PurePosixPath(value)
    if path.is_absolute() or '..' in path.parts or any(c in value for c in ':?#') or any(ord(c) < 32 for c in value):
        raise ValueError(f'{field}: path must stay inside the project')
    return value


def web_url(value, field, *, optional=False):
    if optional and value == '':
        return value
    if not isinstance(value, str):
        raise ValueError(f'{field}: expected a URL string')
    if any(c.isspace() or c in '<>"\x00' for c in value):
        raise ValueError(f'{field}: URL contains unsafe characters')
    url = urlsplit(value)
    if url.scheme not in ('http', 'https') or not url.netloc or url.username or url.password:
        raise ValueError(f'{field}: expected an http(s) URL without credentials')
    return value.rstrip('/')


class SiteConfig:
    """One project instance. No default project, source tree, or metadata files."""
    def __init__(self, values, *, root):
        self.root = Path(root).resolve()
        if not isinstance(values, dict) or values.get('version') != 1:
            raise ValueError('site config: expected a version 1 object')
        values = deepcopy(values)
        self.values = values
        for field in ('name', 'publisher', 'storage_namespace'):
            value = values.get(field)
            if not isinstance(value, str) or not value.strip():
                raise ValueError(f'{field}: expected a nonempty string')
            setattr(self, field, value)
        if not all(c.isalnum() or c in '-_' for c in self.storage_namespace):
            raise ValueError('storage_namespace: use letters, digits, hyphens or underscores')
        self.languages = values.get('languages')
        if (not isinstance(self.languages, list) or not self.languages or
                any(not isinstance(lang, str) or lang not in LANG_LABELS for lang in self.languages) or
                len(set(self.languages)) != len(self.languages)):
            raise ValueError('languages: expected unique supported language codes')
        self.canonical = web_url(values.get('canonical'), 'canonical')
        self.repository = web_url(values.get('repository', ''), 'repository', optional=True)
        self.source_tree = web_url(values.get('source_tree', ''), 'source_tree', optional=True)
        self.source_extension = values.get('source_extension', '.md')
        if self.source_extension not in ('.md', '.lagda.md'):
            raise ValueError('source_extension: expected .md or .lagda.md')
        self.sources = relative_path(values.get('sources'), 'sources')
        for field in ('catalog', 'glossary', 'highlighted', 'types', 'expression_types', 'favicon', 'logo'):
            value = values.get(field, '')
            if not isinstance(value, str):
                raise ValueError(f'{field}: expected a relative path string')
            setattr(self, field, relative_path(value, field) if value else '')
        if not isinstance(values.get('base_url', ''), str):
            raise ValueError('base_url: expected a string')
        self.base_url = values.get('base_url', '').rstrip('/')
        if self.base_url and (not self.base_url.startswith('/') or self.base_url.startswith('//')
                              or any(c.isspace() or ord(c) < 32 or c in ':?#<>"\\' for c in self.base_url)
                              or '..' in self.base_url.split('/')):
            raise ValueError('base_url: expected an absolute path prefix')
        self.prelude_module = values.get('prelude_module', '')
        self.landing_module = values.get('landing_module', '')
        self.hubs = values.get('hubs', [])
        for field in ('prelude_module', 'landing_module'):
            if not isinstance(getattr(self, field), str):
                raise ValueError(f'{field}: expected a module id string')
        if not isinstance(self.hubs, list) or any(not isinstance(item, str) for item in self.hubs):
            raise ValueError('hubs: expected module id strings')
        self.descriptions = values.get('descriptions', {})
        if not isinstance(self.descriptions, dict) or any(not isinstance(self.descriptions.get(lang), str) for lang in self.languages):
            raise ValueError('descriptions: expected text for every configured language')
        self.topics = values.get('topics', [])
        if not isinstance(self.topics, list) or any(not isinstance(item, str) for item in self.topics):
            raise ValueError('topics: expected strings')
        self.agent = values.get('agent', {})
        if not isinstance(self.agent, dict):
            raise ValueError('agent: expected an object')
        self.license = values.get('license', {})
        if not isinstance(self.license, dict) or not isinstance(self.license.get('name'), str):
            raise ValueError('license: expected name and url')
        web_url(self.license.get('url'), 'license.url')
        for field in ('favicon', 'logo'):
            if getattr(self, field) and not getattr(self, field).endswith('.svg'):
                raise ValueError(f'{field}: expected an SVG asset')
        if not self.favicon:
            raise ValueError('favicon: a project SVG is required; no instance icon is inherited')
        if values.get('variable_legacy'):
            relative_path(values['variable_legacy'], 'variable_legacy')
        agda = values.get('agda_policy', {})
        if not isinstance(agda, dict):
            raise ValueError('agda_policy: expected an object')
        for key, value in agda.items():
            if key in {'forbid_monomorphic_empty', 'hprop_projection'} and type(value) is bool:
                continue
            if key in {'prelude_module', 'empty_family'} and isinstance(value, str):
                continue
            if key in {'options', 'bare_open_hubs'} and isinstance(value, list) and all(isinstance(x, str) for x in value):
                continue
            if key == 'prelude_public_names' and isinstance(value, dict) and all(
                    isinstance(k, str) and isinstance(v, list) and all(isinstance(x, str) for x in v) for k, v in value.items()):
                continue
            raise ValueError(f'agda_policy.{key}: unsupported field or value')
        numbered = values.get('numbered_theorems', {})
        if not isinstance(numbered, dict) or any(not isinstance(v, list) or any(type(x) is not int or x < 0 for x in v) for v in numbered.values()):
            raise ValueError('numbered_theorems: expected chapter-to-nonnegative-number lists')
        links = values.get('source_links', [])
        if not isinstance(links, list):
            raise ValueError('source_links: expected a list')
        for link in links:
            if not isinstance(link, dict) or not all(isinstance(link.get(field), str) for field in ('url', 'description')):
                raise ValueError('source_links: expected url and description')
            web_url(link['url'], 'source_links.url')
        self.policies = values.get('policies', {})
        if not isinstance(self.policies, dict):
            raise ValueError('policies: expected an object')
        for field, value in self.policies.items():
            if field not in {'formal_setup', 'trilingual'}:
                raise ValueError(f'policies.{field}: unsupported policy')
            if type(value) is not bool:
                raise ValueError(f'policies.{field}: expected a boolean')
        module_id = re.compile(r'^[^./\\\s<>"\x00]+(?:\.[^./\\\s<>"\x00]+)*$')
        for field in ('prelude_module', 'landing_module'):
            value = getattr(self, field)
            if value and not module_id.fullmatch(value):
                raise ValueError(f'{field}: invalid module id')
        for field in ('hubs', 'visible_import_chapters'):
            items = values.get(field, [])
            if not isinstance(items, list) or any(not isinstance(item, str) or not module_id.fullmatch(item) for item in items):
                raise ValueError(f'{field}: expected valid module ids')
        prerequisites = values.get('prerequisites')
        if prerequisites is not None and (not isinstance(prerequisites, dict) or any(
                not isinstance(key, str) or not module_id.fullmatch(key) or not isinstance(deps, list) or
                any(not isinstance(dep, str) or not module_id.fullmatch(dep) for dep in deps)
                for key, deps in prerequisites.items())):
            raise ValueError('prerequisites: expected module ids mapped to lists of module ids')
        redirects = values.get('legacy_pages', {})
        if not isinstance(redirects, dict):
            raise ValueError('legacy_pages: expected page-to-target mapping')
        for page, target in redirects.items():
            relative_path(page, 'legacy_pages key')
            if '/' in page or not page.endswith('.html'):
                raise ValueError('legacy_pages key: expected a flat .html filename')
            if not isinstance(target, str) or target.startswith(('/', '//')) or ':' in target:
                raise ValueError('legacy_pages target: expected a local page and optional anchor')
            relative_path(target.split('#', 1)[0], 'legacy_pages target')
        translations = self.agent.get('translations', {})
        if not isinstance(translations, dict):
            raise ValueError('agent.translations: expected language mapping')
        scalar_fields = {'docTitle', 'intro', 'hProject', 'fLibrary'}
        for lang, fields in translations.items():
            if lang not in LANG_LABELS or not isinstance(fields, dict):
                raise ValueError('agent.translations: invalid language or fields')
            for field, value in fields.items():
                if field in scalar_fields and isinstance(value, str):
                    continue
                if field in {'project', 'want'} and isinstance(value, list) and all(isinstance(x, str) for x in value):
                    continue
                raise ValueError(f'agent.translations.{lang}.{field}: unsupported field or value')
        if not isinstance(self.agent.get('guide', ''), str):
            raise ValueError('agent.guide: expected text')

    def with_overrides(self, **overrides):
        return SiteConfig({**self.values, **overrides}, root=self.root)

    def validate_references(self, modules):
        references = set(self.hubs) | set(self.values.get('visible_import_chapters', []))
        references.update(self.values.get('numbered_theorems', {}))
        references.update(value for value in (self.prelude_module, self.landing_module) if value)
        for module, dependencies in self.values.get('prerequisites', {}).items():
            references.add(module)
            references.update(dependencies)
        missing = references - set(modules)
        if missing:
            raise ValueError('unknown configured chapters: ' + ', '.join(sorted(missing)))

    def path(self, relative):
        relative_path(relative, 'input')
        result = (self.root / relative).resolve()
        if not result.is_relative_to(self.root):
            raise ValueError(f'input escapes project root: {relative}')
        return result

    def source_path(self, module):
        return self.path(self.sources + '/' + module.replace('.', '/') + self.source_extension)

    def source_url(self, module):
        return self.source_tree + '/' + module.replace('.', '/') + self.source_extension if self.source_tree else ''

    @classmethod
    def load(cls, filename, *, root):
        return cls(json.loads(Path(filename).read_text(encoding='utf-8')), root=root)


class BookCatalog:
    """Localized chapter identity and addresses shared by every output consumer."""
    def __init__(self, nodes=()):
        self.titles = {}
        self.meta = {}
        self.replace(nodes)

    def replace(self, nodes):
        self.titles.clear()
        self.meta.clear()
        for node in nodes:
            self.titles[node['id']] = dict(node['title'])
            self.meta[node['id']] = {key: value for key, value in node.items() if key not in ('id', 'title')}

    def title(self, module, lang):
        titles = self.titles.get(module, {})
        return titles.get(lang, titles.get('en', module))

    def href(self, module, anchor=''):
        meta = self.meta.get(module)
        return (meta['page'] + (anchor or meta.get('anchor', ''))) if meta else module + '.html' + anchor

    def field(self, module, field, lang, default=''):
        values = self.meta.get(module, {}).get(field, {})
        return values.get(lang, values.get('en', default))
