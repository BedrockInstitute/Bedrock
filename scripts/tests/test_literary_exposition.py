import importlib.util
from pathlib import Path
import unittest
spec=importlib.util.spec_from_file_location('literary',Path(__file__).resolve().parents[1]/'gate/check-literary-exposition.py')
lit=importlib.util.module_from_spec(spec); spec.loader.exec_module(lit)

def group(en='Explanation.',zh='解释。',ja='説明です。'):
 return f'<!--en-->\n{en}\n<!--zh-->\n{zh}\n<!--ja-->\n{ja}\n<!--/-->\n'
def rules(text): return [x['rule'] for x in lit.analyze_text(text)['errors']]
class LiteraryExpositionTests(unittest.TestCase):
 def test_five_nonempty_lines_pass(self):
  self.assertEqual(rules(group()+'```agda\na\n\nb\nc\nd\ne\n```\n'),[])
 def test_six_nonempty_lines_fail(self):
  self.assertIn('fence-size',rules(group()+'```agda\na\nb\nc\nd\ne\nf\n```\n'))
 def test_blank_lines_do_not_count_toward_limit(self):
  r=lit.analyze_text(group()+'```agda\na\n\n\nb\n```\n'); self.assertEqual(r['fences'][0]['nonempty_lines'],2); self.assertFalse(r['errors'])
 def test_fallback_cannot_cover_missing_language(self):
  text='<!--en-->\nExplanation.\n<!--zh-->\n解释。\n<!--/-->\n```agda\na\n```\n'
  self.assertIn('trilingual-group',rules(text)); self.assertIn('preceding-exposition',rules(text))
 def test_heading_alone_is_not_explanation(self):
  self.assertIn('preceding-exposition',rules(group('# Title','# 标题','# 題名')+'```agda\na\n```\n'))
 def test_route_metadata_is_neutral(self):
  meta='<!-- bedrock-routes {"version":1,"routes":[]} -->\n'
  self.assertEqual(rules(meta+group()+'```agda\na\n```\n'),[])
 def test_shared_english_prose_is_rejected(self):
  self.assertIn('shared-prose',rules('An English explanation lives here.\n\n'+group()+'```agda\na\n```\n'))
 def test_commentary_cannot_hide_inside_code(self):
  self.assertIn('prose-in-code',rules(group()+'```agda\na = 0\n-- explanation\n```\n'))
 def test_machine_import_directive_is_preserved(self):
  self.assertEqual(rules(group()+'```agda\nopen import M using ( X )  -- lint-agda: keep (qualified projection)\n```\n'),[])
 def test_ordinary_inline_comment_is_still_prose(self):
  self.assertIn('prose-in-code',rules(group()+'```agda\ncon : K → Term K n  -- a constant\n```\n'))
if __name__=='__main__': unittest.main()
