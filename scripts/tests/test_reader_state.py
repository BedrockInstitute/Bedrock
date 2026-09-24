"""Public state-machine contracts replacing closure-variable spelling checks."""
import json
from pathlib import Path
import shutil
import subprocess
import unittest

READER = Path(__file__).resolve().parents[2] / 'site/static/reader'


@unittest.skipUnless(shutil.which('node'), 'Node.js is required')
class ReaderStateTests(unittest.TestCase):
    def run_js(self, exports, scenario):
        imports = '\n'.join('import {' + names + '} from ' + json.dumps(
            (READER / filename).as_uri()) + ';' for filename, names in exports.items())
        result = subprocess.run(['node', '--input-type=module', '-e', imports + scenario],
                                check=True, capture_output=True, text=True)
        return json.loads(result.stdout)

    def test_unbounded_history_identity_forward_truncation_and_cancel(self):
        result = self.run_js({'definition-session.js': 'DefinitionSession'}, '''
const s = new DefinitionSession();
for (let i=0;i<120;i++) s.push({url:'page#'+i}, 'definition '+i);
const total=s.entries.length;
s.move(-1); const old=s.current.target.url;
s.push({url:'replacement#1'},'replacement');
const forward=s.canForward, back=s.canBack;
let releases=0;
const first=s.begin(); s.own(()=>releases++);
const second=s.begin(); const stale=s.isCurrent(first), current=s.isCurrent(second);
s.own(()=>releases++); s.close(); s.close();
console.log(JSON.stringify({total,old,forward,back,stale,current,releases,
  closed:s.current,revived:s.isCurrent(second),length:s.entries.length}));
''')
        self.assertEqual(result, dict(total=120, old='page#118', forward=False, back=True,
            stale=False, current=True, releases=2, closed=None, revived=False, length=0))

    def test_common_downward_geometry_and_horizontal_clamping(self):
        result = self.run_js({'hover-view.js': 'belowSource'}, '''
const rect={left:280,right:310,bottom:77};
console.log(JSON.stringify(belowSource(rect,180,{width:320,scrollX:0,scrollY:20})));
''')
        self.assertEqual(result, {'left': 132, 'top': 97})

    def test_hover_has_no_depth_limit_and_disposes_every_entry(self):
        result = self.run_js({'hover-branch.js': 'HoverBranch'}, '''
let count=0;const branch=new HoverBranch({persistent:()=>true,dispose:()=>count++});
for(let i=0;i<120;i++) branch.append({parent:branch.entries[i-1]});
const depth=branch.entries.length;branch.removeFrom(0);
console.log(JSON.stringify({depth,count,left:branch.entries.length}));
''')
        self.assertEqual(result, {'depth':120,'count':120,'left':0})
