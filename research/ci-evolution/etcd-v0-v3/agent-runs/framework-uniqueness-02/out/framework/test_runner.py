"""Fault-injection checks for the reusable comparator, independent of adapters."""
import copy,unittest
from runner import compare
class RunnerTests(unittest.TestCase):
 def setUp(self):
  self.cases=[dict(id='case',action='x')]
  self.r=dict(id='case',adapter_status='ok',pre_observation={'v':0},input_observation={'arg':1},observation={'state':{'set':[1,2],'sequence':[1,2]},'status':'ok','return':None})
 def verdict(self,change):
  other=copy.deepcopy(self.r);change(other)
  return compare(self.cases,{'case':self.r},{'case':other},['state.set'])[0]['verdict']
 def test_set_permutation(self):self.assertEqual('match',self.verdict(lambda r:r['observation']['state'].update(set=[2,1])))
 def test_sequence_order(self):self.assertEqual('behavioral_mismatch',self.verdict(lambda r:r['observation']['state'].update(sequence=[2,1])))
 def test_multiplicity(self):self.assertEqual('behavioral_mismatch',self.verdict(lambda r:r['observation']['state'].update(set=[1,1,2])))
 def test_pre_mapping(self):self.assertEqual('adapter_error',self.verdict(lambda r:r['pre_observation'].update(v=1)))
 def test_input_mapping(self):self.assertEqual('adapter_error',self.verdict(lambda r:r['input_observation'].update(arg=2)))
 def test_drop(self):self.assertEqual('behavioral_mismatch',self.verdict(lambda r:r['observation'].update(status='dropped')))
 def test_side_effect(self):self.assertEqual('behavioral_mismatch',self.verdict(lambda r:r['observation']['state'].update(new_side_effect=1)))
 def test_missing(self):self.assertEqual('adapter_error',compare(self.cases,{'case':self.r},{},[])[0]['verdict'])
if __name__=='__main__':unittest.main()
