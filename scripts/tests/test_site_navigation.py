import json
import re
import shutil
import subprocess
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]


class SiteNavigationTests(unittest.TestCase):
    @unittest.skipUnless(shutil.which("node"), "Node.js is needed for the JavaScript behavior test")
    def test_active_section_link_stays_inside_sidebar_viewport(self):
        javascript = (ROOT / "site" / "static" / "bedrock.js").read_text()
        helper = re.search(
            r"    function revealTocLink\(link\) \{.*?\n    \}\n",
            javascript,
            re.DOTALL,
        )
        self.assertIsNotNone(helper)
        scenario = r'''
var toc = {
  scrollTop: 100,
  getBoundingClientRect: function () { return {top: 10, bottom: 110}; }
};
var document = {getElementById: function () { return toc; }};
function show(top, bottom) {
  toc.scrollTop = 100;
  revealTocLink({getBoundingClientRect: function () { return {top: top, bottom: bottom}; }});
  return toc.scrollTop;
}
console.log(JSON.stringify({above: show(-5, 5), visible: show(30, 50), below: show(120, 140)}));
'''
        completed = subprocess.run(
            [shutil.which("node"), "-e", helper.group(0) + scenario],
            check=True,
            capture_output=True,
            text=True,
            timeout=5,
        )
        self.assertEqual(json.loads(completed.stdout), {
            "above": 77,
            "visible": 100,
            "below": 138,
        })


if __name__ == "__main__":
    unittest.main()
