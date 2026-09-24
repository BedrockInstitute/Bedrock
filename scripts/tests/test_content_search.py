import importlib.util
import json
from pathlib import Path
import shutil
import subprocess
import sys
import unittest

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / 'scripts/site'))
from search_index import passages


class ContentSearchTests(unittest.TestCase):
    def test_headings_prose_code_and_nested_anchors(self):
        body = ('<h1 id="sec-0">Title</h1><h2 id="sec-1">Section</h2>'
                '<p id="p-1">中文 <code>LEM</code> 正文</p>'
                '<ul><li id="p-2"><p>日本語</p></li></ul>'
                '<pre class="Agda"><a id="22">f</a> = x\n<a id="30">g</a> = y</pre>'
                '<script>SECRET</script><nav>Navigation</nav>')
        data = passages(body, 'M', 'Title', 'zh', 'M.html')
        self.assertTrue(any(e['text'] == '中文 LEM 正文' and e['href'] == 'M.html#p-1' for e in data))
        self.assertTrue(any(e['text'] == '日本語' and e['href'] == 'M.html#p-2' for e in data))
        self.assertTrue(any(e['kind'] == 'code' and e['lang'] == '*' and e['href'] == 'M.html#22' for e in data))
        self.assertFalse(any('SECRET' in e['text'] or 'Navigation' in e['text'] for e in data))

    def test_large_cubical_code_is_complete_and_windows_overlap(self):
        body = '<pre class="Agda">' + '\n'.join(f'<a id="{i}">name{i}</a> = value{i}' for i in range(30)) + '</pre>'
        data = passages(body, 'Cubical.Test', 'Cubical.Test', 'en', 'Cubical.Test.html')
        for i in range(30):
            self.assertTrue(any(f'name{i} = value{i}' in e['text'] for e in data))
        self.assertTrue(any('value7 name8' in e['text'] for e in data))

    @unittest.skipUnless(shutil.which('node'), 'Node required')
    def test_worker_searches_all_languages_and_shared_library_code(self):
        worker = ROOT / 'site/static/search-worker.js'
        script = r'''
const fs = require('fs'), vm = require('vm');
const entries = [
 {name:'English section',text:'constructible universe',module:'A',lang:'en',href:'A.html#p-1',kind:'prose'},
 {name:'中文小节',text:'集合宇宙的解释',module:'A',lang:'zh',href:'A.html#p-1',kind:'prose'},
 {name:'日本語節',text:'集合宇宙の解釈',module:'A',lang:'ja',href:'A.html#p-1',kind:'prose'},
 {name:'transport',text:'transport refl x = x',module:'Cubical.Foundations.Prelude',lang:'*',href:'Cubical.Foundations.Prelude.html#4',kind:'code'}
];
let reply, calls = 0;
const context = {self:{postMessage:r=>reply=r},fetch:async()=>{calls++;return{ok:true,json:async()=>entries}}};
vm.createContext(context); vm.runInContext(fs.readFileSync(process.argv[1],'utf8'),context);
(async()=>{let id=0;for(const lang of ['en','zh','ja'])for(const query of ['constructible','解释','解釈','transport refl']){
await context.self.onmessage({data:{id:++id,query,lang,url:'index'}});
if(reply.error || reply.results.length!==1)throw Error(query+JSON.stringify(reply));
}if(calls!==1)throw Error('Index fetched repeatedly');console.log('all languages and Cubical passed');})().catch(e=>{console.error(e);process.exitCode=1});
'''
        result = subprocess.run(['node', '-e', script, str(worker)], capture_output=True, text=True)
        self.assertEqual(result.returncode, 0, result.stderr)

    def test_instantiated_alias_uses_compiler_scope_not_global_guess(self):
        spec = importlib.util.spec_from_file_location('search_renderer', ROOT / 'scripts/site/render-site.py')
        renderer = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(renderer)
        scope = renderer.compiler_reference_scope(
            '<a href="FOL.ZFModel.html#10" class="Record">isZFModel</a>'
            '<a href="V.Model.html#20" class="Bound">x</a>')
        names = {'FOL.ZFModel.isZFModel': ('FOL.ZFModel', '10')}
        renderer.add_instantiated_type_aliases(names,
            {'V.Model': {'V⊨ZF': 'V.Model.Model.isZFModel', 'bound': 'V.Model.Local.x'}},
            {'V.Model': scope})
        self.assertEqual(names['V.Model.Model.isZFModel'], ('FOL.ZFModel', '10'))
        self.assertNotIn('V.Model.Local.x', names)
        rendered = renderer.render_type('V.Model.Model.isZFModel', names, renderer.qualified_name_pattern(names))
        self.assertIn('data-type="FOL.ZFModel#10"', rendered)


if __name__ == '__main__':
    unittest.main()
