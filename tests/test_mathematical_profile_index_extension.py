"""A retained correction may accept only explicitly bound profile-index additions."""
from copy import deepcopy
import hashlib
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

from math_gauge.mathematical_profile_corrections import (
    DIRECTORY,INDEX_EXTENSION_PATH,INDEX_SOURCE_PATH,INDEX_ALIASES,
    _source_indices,_verify_added_profile,
)


class SourceIndexExtensionTests(unittest.TestCase):
    def setUp(self):
        self.temp=tempfile.TemporaryDirectory();self.addCleanup(self.temp.cleanup)
        self.roots={k:Path(self.temp.name)/k for k in ('public','private')}
        for root in self.roots.values():root.mkdir()
        self.raw=b'unchanged accepted baseline correction'
        contracts=self.put('private','contracts.json',{'tasks':[]})
        self.old={repo:dict(schema='index-'+repo,policy_sha256='policy',models={'old':{'digest':'old-exact'}})
                  for repo in self.roots}
        self.old['private']['contracts']={k:contracts[k] for k in ('path','bytes','sha256')}
        self.sources={}
        self.current={}
        for alias,repo in INDEX_ALIASES.items():
            self.sources[alias]=self.put(repo,INDEX_SOURCE_PATH,self.old[repo])
            self.put(repo,DIRECTORY+'/source-indices/'+repo+'.json',self.old[repo])
            self.current[repo]=deepcopy(self.old[repo]);self.current[repo]['models']['new']={'new-profile':'independently-verified'}
        self.extension=dict(schema='math-gauge.mathematical-profile-source-index-extension/v1',
            version='0.1.0',benchmark_version='1.2.0',source_profile_version='0.4.0',
            post_observation=True,original_bytes_rewritten=False,new_candidate_calls=0,
            original_adoption_sha256=hashlib.sha256(self.raw).hexdigest(),
            original_sources=deepcopy(self.sources),
            retained_sources={alias:self.ref(repo,DIRECTORY+'/source-indices/'+repo+'.json')
                              for alias,repo in INDEX_ALIASES.items()},current_sources={},added_models=['new'])
        self.policy={'private_contract_sha256':contracts['sha256']}
        self.policy_patch=patch('math_gauge.mathematical_profile_corrections.load_policy',return_value=(self.policy,'policy'))
        self.policy_patch.start();self.addCleanup(self.policy_patch.stop)
        self.verify_patch=patch('math_gauge.mathematical_profile_corrections._verify_added_profile')
        self.verify=self.verify_patch.start();self.addCleanup(self.verify_patch.stop)

    def put(self,repo,path,value):
        p=self.roots[repo]/path;p.parent.mkdir(parents=True,exist_ok=True)
        p.write_bytes(value if isinstance(value,bytes) else (json.dumps(value)+'\n').encode())
        return self.ref(repo,path)

    def ref(self,repo,path):
        raw=(self.roots[repo]/path).read_bytes()
        return dict(repository=repo,path=path,bytes=len(raw),sha256=hashlib.sha256(raw).hexdigest())

    def activate(self):
        for alias,repo in INDEX_ALIASES.items():
            self.extension['current_sources'][alias]=self.put(repo,INDEX_SOURCE_PATH,self.current[repo])
        self.put('private',INDEX_EXTENSION_PATH,self.extension)

    def resolve(self):return _source_indices(self.roots,self.raw,self.sources)

    def test_exact_original_indices_need_no_extension_or_new_review(self):
        got=self.resolve()
        self.assertEqual(got,{a:self.old[r] for a,r in INDEX_ALIASES.items()})
        self.verify.assert_not_called()

    def test_append_requires_explicit_metadata_and_returns_immutable_old_sources(self):
        self.put('public',INDEX_SOURCE_PATH,self.current['public'])
        with self.assertRaises(ValueError):self.resolve()
        self.activate();got=self.resolve()
        self.assertEqual(got,{a:self.old[r] for a,r in INDEX_ALIASES.items()})
        self.verify.assert_called_once()
        self.assertEqual(self.verify.call_args.args[1],'new')
        self.assertEqual(self.verify.call_args.args[2],self.current['public']['models']['new'])

    def test_old_entry_deletion_replacement_or_metadata_change_is_rejected(self):
        for mutation in ('delete','replace','metadata'):
            with self.subTest(mutation=mutation):
                self.current['public']=deepcopy(self.old['public'])
                self.current['public']['models']['new']={}
                if mutation=='delete':del self.current['public']['models']['old']
                if mutation=='replace':self.current['public']['models']['old']={'digest':'rewritten'}
                if mutation=='metadata':self.current['public']['policy_sha256']='other-policy'
                self.activate()
                with self.assertRaisesRegex(ValueError,'original metadata or model entries'):self.resolve()

    def test_public_private_additions_must_equal_the_declared_set(self):
        for mutation in ('unpaired','undeclared','duplicate'):
            with self.subTest(mutation=mutation):
                self.current['private']=deepcopy(self.old['private']);self.current['private']['models']['new']={}
                self.extension['added_models']=['new']
                if mutation=='unpaired':del self.current['private']['models']['new']
                if mutation=='undeclared':self.extension['added_models']=['other']
                if mutation=='duplicate':self.extension['added_models']=['new','new']
                self.activate()
                with self.assertRaisesRegex(ValueError,'paired added models'):self.resolve()

    def test_missing_or_damaged_current_index_never_falls_back_to_snapshot(self):
        self.activate();p=self.roots['public']/INDEX_SOURCE_PATH
        p.unlink()
        with self.assertRaises((ValueError,OSError)):self.resolve()
        p.write_bytes(b'corrupt current index')
        with self.assertRaises(ValueError):self.resolve()

    def test_snapshot_and_adoption_hashes_are_exact_and_aliases_are_narrow(self):
        self.activate()
        for field in ('snapshot','adoption','alias'):
            with self.subTest(field=field):
                changed=deepcopy(self.extension)
                if field=='snapshot':changed['retained_sources']['public_base_index']['sha256']='0'*64
                if field=='adoption':changed['original_adoption_sha256']='0'*64
                if field=='alias':changed['original_sources']['unrelated_source']=deepcopy(self.sources['public_base_index'])
                self.put('private',INDEX_EXTENSION_PATH,changed)
                with self.assertRaises(ValueError):self.resolve()

    def test_independent_new_profile_failure_is_not_swallowed(self):
        self.activate();self.verify.side_effect=ValueError('new profile does not reproduce')
        with self.assertRaisesRegex(ValueError,'new profile does not reproduce'):self.resolve()


class AddedProfileSourceTests(unittest.TestCase):
    def test_new_profile_bad_source_bytes_and_foreign_model_are_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            roots={r:Path(directory)/r for r in ('public','private')}
            prefix='results/mathematical-profiles/v0.4.0/new/'
            def put(repo,name,value):
                path=roots[repo]/(prefix+name);path.parent.mkdir(parents=True,exist_ok=True)
                raw=(json.dumps(value)+'\n').encode();path.write_bytes(raw)
                return dict(path=prefix+name,bytes=len(raw),sha256=hashlib.sha256(raw).hexdigest())
            public=put('public','profile.json',{})
            private={key:put('private',name,value) for key,name,value in [
                ('review','review.json',{'model_id':'new'}),
                ('source-bindings','source-bindings.json',{'model_id':'new'}),
                ('score','score.json',{})]}
            private['public_projection']=public
            (roots['private']/private['score']['path']).write_bytes(b'changed score')
            with self.assertRaisesRegex(ValueError,'source bytes changed'):
                _verify_added_profile(roots,'new',public,private,{},'policy',{})
            private['score']=put('private','score.json',{})
            private['review']=put('private','review.json',{'model_id':'other'})
            with self.assertRaisesRegex(ValueError,'another model review'):
                _verify_added_profile(roots,'new',public,private,{},'policy',{})


if __name__=='__main__':unittest.main()
