"""Tests for relative site links and HTML fragments."""

from contextlib import redirect_stderr, redirect_stdout
import importlib.util
from io import StringIO
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

spec = importlib.util.spec_from_file_location(
    "link_check", Path(__file__).resolve().parents[1] / "site/link-check.py")
link_check = importlib.util.module_from_spec(spec)
spec.loader.exec_module(link_check)


class LinkCheckTests(unittest.TestCase):
    def write(self, root, relative, text):
        path = root / relative
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text, encoding="utf-8")
        return path

    def run_check(self, root):
        stdout = StringIO()
        stderr = StringIO()
        with redirect_stdout(stdout), redirect_stderr(stderr):
            result = link_check.check_site(str(root))
        return result, stdout.getvalue(), stderr.getvalue()

    def test_valid_cross_page_encoded_and_same_page_anchors(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            self.write(root, "index.html", """
                <main id="local anchor">
                  <a href="#local%20anchor">local</a>
                  <a href="chapter%20one.html?mode=read#sec%2Fone">encoded</a>
                  <a href='entities.html#fish&amp;chips'>entities</a>
                  <a href="/missing.html#ignored">root</a>
                  <a href="https://example.test/missing#ignored">external</a>
                  <img src="data:image/gif;base64,AAAA">
                </main>
            """)
            self.write(root, "chapter one.html", '<section id="sec/one"></section>')
            self.write(root, "entities.html", '<section id="fish&amp;chips"></section>')

            result, output, summary = self.run_check(root)

            self.assertEqual(result, 0, output)
            self.assertEqual(output, "")
            self.assertIn("3 relative link(s)", summary)
            self.assertIn("0 broken", summary)

    def test_reports_missing_cross_page_and_same_page_anchors(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            index = self.write(root, "index.html", """
                <a href="#absent%20here">same</a>
                <a href="other.html#absent%20there">cross</a>
            """)
            self.write(root, "other.html", '<h2 id="present"></h2>')

            result, output, summary = self.run_check(root)

            self.assertEqual(result, 1)
            self.assertIn(f"{index}: missing anchor #absent here", output)
            self.assertIn("missing anchor #absent there -> other.html#absent%20there", output)
            self.assertIn("2 broken", summary)

    def test_repeated_cross_page_links_read_destination_once(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            self.write(root, "index.html", """
                <a href="other.html#one">one</a>
                <a href="other.html#two">two</a>
                <a href="other.html#one">again</a>
            """)
            destination = self.write(root, "other.html", '<i id="one"></i><i id="two"></i>')
            real_open = open
            reads = []

            def recording_open(path, *args, **kwargs):
                if Path(path) == destination:
                    reads.append(path)
                return real_open(path, *args, **kwargs)

            with patch("builtins.open", side_effect=recording_open):
                result, output, _ = self.run_check(root)

            self.assertEqual(result, 0, output)
            self.assertEqual(len(reads), 1)


if __name__ == "__main__":
    unittest.main()
