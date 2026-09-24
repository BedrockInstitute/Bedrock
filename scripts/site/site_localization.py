"""Reader interface wording, independent of project branding and mathematics."""
import html as htmllib
from site_config import LANG_LABELS
UI = {
    "en": {"search": "Search…", "theme": "Toggle theme", "contents": "On this page",
           "menu": "Menu", "close": "Close",
           "untranslated": "This page is not yet translated; showing English.",
           "modules": "Modules", "source": "Source", "overview": "Overview",
           "depmap": "Dependency graph", "routes": "Reading routes",
           "current_route": "Current route",
           "guide": "Interactive contents", "catalog": "Chapter catalog",
           "landmark": "Origin", "terms": "Glossary",
           "prev": "Previous chapter", "next": "Next chapter",
           "license": "content licensed CC BY-NC-SA 4.0",
           "markdown": "Markdown", "agents": "llms.txt",
           "mdtitle": "This page as plain Markdown, for AI agents and scripts",
           "agentstitle": "How an AI agent should read this site",
           "credit": 'Rendered with a generator adapted from '
                     '<a href="https://1lab.dev">the 1lab</a> (AGPL-3.0).',
           "external": "You are viewing the Cubical library.",
           "back": "Back to {site}"},
    "zh": {"search": "搜索…", "theme": "切换主题", "contents": "本页内容",
           "menu": "菜单", "close": "关闭",
           "untranslated": "本页尚未翻译，此处显示英文。",
           "modules": "模块", "source": "源码", "overview": "概览",
           "depmap": "依赖图", "routes": "阅读路线",
           "current_route": "当前路线",
           "guide": "交互式目录", "catalog": "章节目录",
           "landmark": "原点", "terms": "术语表",
           "prev": "上一章", "next": "下一章",
           "license": "内容以 CC BY-NC-SA 4.0 许可",
           "markdown": "Markdown", "agents": "llms.txt",
           "mdtitle": "本页的纯 Markdown 版本，供 AI 与脚本读取",
           "agentstitle": "AI 应当如何阅读本站",
           "credit": '使用改编自 <a href="https://1lab.dev">1lab</a> 的生成器渲染 '
                     '(AGPL-3.0)',
           "external": "您正在浏览 Cubical 库。",
           "back": "返回 {site}"},
    "ja": {"search": "検索…", "theme": "テーマ切替", "contents": "このページの内容",
           "menu": "メニュー", "close": "閉じる",
           "untranslated": "このページは未翻訳です。英語を表示しています。",
           "modules": "モジュール", "source": "ソース", "overview": "概要",
           "depmap": "依存グラフ", "routes": "学習ルート",
           "current_route": "現在のルート",
           "guide": "対話型目次", "catalog": "章の目次",
           "landmark": "原点", "terms": "用語集",
           "prev": "前の章", "next": "次の章",
           "license": "コンテンツは CC BY-NC-SA 4.0 ライセンス",
           "markdown": "Markdown", "agents": "llms.txt",
           "mdtitle": "このページの純 Markdown 版。AI とスクリプト向け",
           "agentstitle": "AI エージェントのための読み方",
           "credit": '<a href="https://1lab.dev">1lab</a> を改変した'
                     'ジェネレータでレンダリング (AGPL-3.0)。',
           "external": "Cubical ライブラリを閲覧しています。",
           "back": "{site} に戻る"},
}


def lang_nav(out_name, lang, langs):
    """Language switcher; `out_name` is this page's filename (index.html for the landing)."""
    bits = []
    for L in langs:
        if L == lang:
            bits.append(f'<span class="cur">{LANG_LABELS[L]}</span>')
        else:
            bits.append(f'<a href="../{L}/{out_name}">{LANG_LABELS[L]}</a>')
    return " · ".join(bits)


def hreflang_links(out_name, langs, base):
    return "\n".join(
        f'  <link rel="alternate" hreflang="{L}" href="{base}/{L}/{out_name}" />'
        for L in langs)


def interface_copy(config, book):
    ui = {lang: dict(words) for lang, words in UI.items()}
    for lang, words in ui.items():
        words['back'] = words['back'].replace('{site}', config.name)
        words['landmark'] = book.title(config.landing_module, lang) if config.landing_module else words['overview']
        words['license'] = words['license'].replace('CC BY-NC-SA 4.0', config.license['name'].replace('CC-BY-NC-SA-4.0', 'CC BY-NC-SA 4.0'))
    return ui
