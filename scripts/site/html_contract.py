"""Shared compiler-HTML and Markdown token contracts; no project data."""
import re

PRE_RE = re.compile(r'<pre class="Agda">.*?</pre>', re.DOTALL)


SUBMODULE_HTML_TOKEN_RE = re.compile(
    r'<pre class="Agda">.*?</pre>|</?details\b[^>]*>|</?summary\b[^>]*>',
    re.DOTALL,
)


DEF_RE = re.compile(r'<a id="([^"]+)"></a><a id="(\d+)"[^>]*class="([^"]*)"')


RENAMED_RE = re.compile(
    r'<a id="\d+" class="Symbol">to</a>[ \t]*'
    r'<a id="(\d+)" class="([^"]+)">([^<]+)</a>'
)


LOCAL_SIGNATURE_RE = re.compile(
    r'(?m)^(?:<pre\b[^>]*>)?[ \t]*(?:<a id="[^"]+"></a>)?'
    r'<a id="(?P<pos>\d+)" href="(?P<module>[^"]+)\.html#(?P=pos)" '
    r'class="(?P<aspect>[^"]*)">(?P<name>[^<]+)</a>[ \t]*'
    r'<a id="\d+" class="Symbol">:</a>[ \t]*(?P<type>[^\n]+)'
)


LOCAL_DECL_RE = re.compile(
    r'<a id="(?P<pos>\d+)" href="(?P<module>[^"]+)\.html#(?P=pos)" '
    r'class="(?P<aspect>[^"]*)">(?P<name>[^<]+)</a>'
)


TYPE_COLON_RE = re.compile(r'<a id="\d+" class="Symbol">:</a>[ \t]*')


LINK_RE = re.compile(r'<a (id="\d+" )?href="([^"#]+)\.html(#\d+)?"([^>]*)>')


INLINE_AGDA_RE = re.compile(r'`([^`]+)`\{\.Agda\}')


INLINE_AGDA_LINK_RE = re.compile(r'\[([^\]]+)\]\(([\w.]+)\.html#([^\s)]+)\)\{\.Agda\}')


SUMMARY_RE = re.compile(r'<summary([^>]*)>(.*?)</summary>', re.DOTALL)


A_TAG_RE  = re.compile(r'<a\b([^>]*)>([^<]+)</a>')


TOKEN_RE = re.compile(r'<a\b[^>]*\bid="(\d+)"[^>]*>(.*?)</a>', re.DOTALL)


HREF_RE   = re.compile(r'\bhref="([^"]+\.html(?:#\d+)?)"')


CLASS_RE  = re.compile(r'\bclass="([^"]*)"')


ID_RE = re.compile(r'\bid="(\d+)"')


NUL = "\x00"


_PLACEHOLDER = re.compile(NUL + r'[A-Z]+\d+' + NUL)


_BLOCK_PLACEHOLDER = re.compile(NUL + r'(?:CODE|DMATH)\d+' + NUL)


TYPE_NODE_TAG_RE = re.compile(r'<span class="type-node"[^>]*>|</span>')


NON_HOVER_PRIMITIVE_SORTS = {
    "Prop", "Set", "SSet", "Propω", "Setω", "SSetω", "LevelUniv",
}


SPAN_EVENT_RE = re.compile(r'<span\b[^>]*>|</span>|\n[ \t]*')


_BARE_REFERENCE_ASPECTS = {
    "Function", "Datatype", "Record", "Primitive", "PrimitiveType", "Field",
    "Module", "Macro", "Postulate", "InductiveConstructor", "CoinductiveConstructor",
}


BLOCK_RE = re.compile(r'<(/?)(p|li|blockquote|table)\b')


__all__ = ['PRE_RE', 'SUBMODULE_HTML_TOKEN_RE', 'DEF_RE', 'RENAMED_RE', 'LOCAL_SIGNATURE_RE', 'LOCAL_DECL_RE', 'TYPE_COLON_RE', 'LINK_RE', 'INLINE_AGDA_RE', 'INLINE_AGDA_LINK_RE', 'SUMMARY_RE', 'A_TAG_RE', 'TOKEN_RE', 'HREF_RE', 'CLASS_RE', 'ID_RE', 'NUL', '_PLACEHOLDER', '_BLOCK_PLACEHOLDER', 'TYPE_NODE_TAG_RE', 'NON_HOVER_PRIMITIVE_SORTS', 'SPAN_EVENT_RE', '_BARE_REFERENCE_ASPECTS', 'BLOCK_RE']
