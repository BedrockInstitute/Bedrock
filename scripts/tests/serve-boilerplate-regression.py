#!/usr/bin/env python3
"""Serve the built site and its real-browser regression fixture on localhost.

Open /regression in Safari. No browser settings, dependencies, or production
content are changed. Deliberately redirect .html URLs to exercise modal mirrors
under the same canonical redirects used by the static host.
"""
import argparse
import http.server
import time
from pathlib import Path
from urllib.parse import parse_qs, urlsplit

ROOT = Path(__file__).resolve().parents[2]


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

        def end_headers(self):
            # History entries can reuse an iframe URL. Keep the artificial
            # loading delay observable even when the browser has seen it before.
            self.send_header('Cache-Control', 'no-store')
            super().end_headers()

        def do_GET(self):
            url = urlsplit(self.path)
            if url.path.endswith('.html'):
                self.send_response(307)
                self.send_header('Location', url.path[:-5] + ('?' + url.query if url.query else ''))
                self.end_headers()
                return
            if parse_qs(url.query).get('bedrock-modal') == ['1']:
                time.sleep(args.modal_delay)
            super().do_GET()

        def translate_path(self, path):
            if urlsplit(path).path == '/regression':
                return str(ROOT / 'scripts/tests/browser-boilerplate.html')
            if urlsplit(path).path == '/padding-regression':
                return str(ROOT / 'scripts/tests/browser-code-padding.html')
            if urlsplit(path).path == '/directory-regression':
                return str(ROOT / 'scripts/tests/browser-directory.html')
            if urlsplit(path).path == '/appearance-regression':
                return str(ROOT / 'scripts/tests/browser-appearance.html')
            if urlsplit(path).path == '/universe-regression':
                return str(ROOT / 'scripts/tests/browser-universe-levels.html')
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
