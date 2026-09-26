#!/usr/bin/env python3
"""Serve the built site and its real-browser regression fixture on localhost.

Open /regression in Safari. No browser settings, dependencies, or production
content are changed. Deliberately redirect .html URLs to exercise modal mirrors
under the same canonical redirects used by the static host.
"""
import argparse
import http.server
import time
import re
from pathlib import Path
from urllib.parse import parse_qs, urlsplit

ROOT = Path(__file__).resolve().parents[2]
FIXTURES = {
    '/regression': 'browser-boilerplate.html',
    '/padding-regression': 'browser-code-padding.html',
    '/directory-regression': 'browser-directory.html',
    '/appearance-regression': 'browser-appearance.html',
    '/universe-regression': 'browser-universe-levels.html',
    '/fonts-regression': 'browser-fonts.html',
    '/mobile-reader': 'browser-mobile-reader.html',
    '/header-shell-regression': 'browser-header-shell.html',
    '/punctuation-regression': 'browser-punctuation-wrap.html',
    '/notes-regression': 'browser-notes.html',
    '/mathematical-notation-regression': 'browser-mathematical-notation.html',
}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--site', type=Path, default=ROOT / '_build/site')
    parser.add_argument('--port', type=int, default=18764)
    parser.add_argument('--modal-delay', type=float, default=0,
                        help='Delay modal documents by 0..10 seconds to inspect loading states')
    args = parser.parse_args()
    if not 0 <= args.modal_delay <= 10:
        parser.error('--modal-delay must be between 0 and 10 seconds')
    if not (args.site / 'zh/Base.Choice.html').is_file():
        parser.error('build the trilingual site first')

    class Handler(http.server.SimpleHTTPRequestHandler):
        def __init__(self, *positional, **kwargs):
            super().__init__(*positional, directory=str(args.site.resolve()), **kwargs)

        def guess_type(self, path):
            kind = super().guess_type(path)
            if path.endswith(('.txt', '.md')) and 'charset=' not in kind:
                return kind + '; charset=utf-8'
            return kind

        def end_headers(self):
            # History entries can reuse an iframe URL. Keep the artificial
            # loading delay observable even when the browser has seen it before.
            self.send_header('Cache-Control', 'no-store')
            super().end_headers()

        def do_GET(self):
            url = urlsplit(self.path)
            if url.path in FIXTURES:
                # Exercise the exact production generation, not mutable source
                # copies. Popup iframe pages already reference this same hash.
                page = (args.site / 'en/index.html').read_text(encoding='utf-8')
                runtime = re.search(r'/static/(runtime/[0-9a-f]+)/outcrop.js', page)
                fixture = (ROOT / 'scripts/tests' / FIXTURES[url.path]).read_text(encoding='utf-8')
                fixture = fixture.replace('/site/static/', '/static/')
                if runtime:
                    fixture = fixture.replace('__OUTCROP_RUNTIME__', runtime[1])
                    fixture = re.sub(r'/static/([a-z-]+\.js)',
                        lambda match: '/static/' + runtime[1] + '/' + match[1], fixture)
                payload = fixture.encode('utf-8')
                self.send_response(200)
                self.send_header('Content-Type', 'text/html; charset=utf-8')
                self.send_header('Content-Length', str(len(payload)))
                self.end_headers()
                self.wfile.write(payload)
                return
            if url.path.endswith('.html'):
                self.send_response(307)
                self.send_header('Location', url.path[:-5] + ('?' + url.query if url.query else ''))
                self.end_headers()
                return
            if parse_qs(url.query).get('outcrop-modal') == ['1']:
                time.sleep(args.modal_delay)
            if parse_qs(url.query).get('reader-test') == ['touch']:
                source = Path(self.translate_path(self.path)).read_text(encoding='utf-8')
                probe = (ROOT / 'scripts/tests/browser-mobile-probe.js').read_text(encoding='utf-8')
                payload = source.replace('<head>', '<head><script>' + probe + '</script>').encode('utf-8')
                self.send_response(200)
                self.send_header('Content-Type', 'text/html; charset=utf-8')
                self.send_header('Content-Length', str(len(payload)))
                self.end_headers()
                self.wfile.write(payload)
                return
            super().do_GET()

        def translate_path(self, path):
            fixture = FIXTURES.get(urlsplit(path).path)
            if fixture:
                return str(ROOT / 'scripts/tests' / fixture)
            result = Path(super().translate_path(path))
            candidate = result.with_suffix(result.suffix + '.html')
            return str(candidate if not result.exists() and candidate.is_file() else result)

        def do_POST(self):
            length = int(self.headers.get('Content-Length', '0'))
            if self.path != '/results' or not 0 <= length <= 65536:
                self.send_error(400)
                return
            print('BROWSER ' + self.rfile.read(length).decode('utf-8', errors='replace'), flush=True)
            self.send_response(204)
            self.end_headers()

    print(f'Open http://127.0.0.1:{args.port}/regression', flush=True)
    http.server.ThreadingHTTPServer(('127.0.0.1', args.port), Handler).serve_forever()


if __name__ == '__main__':
    main()
