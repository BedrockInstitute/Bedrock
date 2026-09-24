"""Exercise the shared popup timers, including re-arming cancelled ancestors."""
import json
from pathlib import Path
import shutil
import subprocess
import unittest

ROOT = Path(__file__).resolve().parents[2]


@unittest.skipUnless(shutil.which('node'), 'Node.js is required')
class HoverLifecycleTests(unittest.TestCase):
    def test_nested_exit_rearms_ancestors_but_never_mobile_timers(self):
        imports = "import {HoverBranch} from " + json.dumps(
            (ROOT / 'site/static/reader/hover-branch.js').as_uri()) + ";\n"
        scenario = r'''
var compactPointer = {matches: false}, hoverCloseDelay = 360;
var timers = new Map(), sequence = 0;
var clock = {
  setTimeout: callback => { timers.set(++sequence, callback); return sequence; },
  clearTimeout: key => timers.delete(key)
};
const lifecycle = new HoverBranch({clock, persistent: () => compactPointer.matches,
  dispose: () => {}});
const namePopups = lifecycle.entries;
const laterHideName = entry => lifecycle.leave(entry);
const cancelNameClose = entry => lifecycle.enter(entry);
function tick() {
  [...timers].forEach(([key, callback]) => {
    if (timers.delete(key)) callback();
  });
}
function branch() {
  lifecycle.removeFrom(0);
  for (let i = 0; i < 3; i++) {
    const entry = {parent: namePopups[i - 1], hovered: false, closeTimer: null};
    entry.anchor = {matches: () => false};
    entry.popup = {matches: () => entry.hovered};
    lifecycle.append(entry);
  }
  return namePopups[2];
}
let child = branch();
laterHideName(namePopups[0]);
cancelNameClose(child);
const cancelled = timers.size;
laterHideName(child);
const rearmed = timers.size;
tick();
const fullyClosed = namePopups.length;
child = branch();
laterHideName(child);
child.hovered = true;
cancelNameClose(child);
tick();
const reentered = namePopups.length;
child.hovered = false;
namePopups[0].hovered = true;
laterHideName(child); tick();
const ancestorRetained = namePopups.length;
namePopups[0].hovered = false;
laterHideName(namePopups[0]); tick();
const ancestorClosed = namePopups.length;
child = branch(); compactPointer.matches = true;
laterHideName(child); tick();
console.log(JSON.stringify({cancelled, rearmed, fullyClosed, reentered,
  ancestorRetained, ancestorClosed, mobileEntries: namePopups.length,
  mobileTimers: timers.size}));
'''
        result = subprocess.run([shutil.which('node'), '--input-type=module', '-e', imports + scenario],
                                text=True, capture_output=True, check=True, timeout=5)
        self.assertEqual(json.loads(result.stdout), dict(cancelled=0, rearmed=3,
            fullyClosed=0, reentered=3, ancestorRetained=1, ancestorClosed=0,
            mobileEntries=3, mobileTimers=0))
