# SPDX-License-Identifier: Apache-2.0
# Authors: Formal Frontier Agents
# Atlas adaptation of the multivariate-polynomials/Anchor renderer controls.
"""Synthetic adapter controls: not native provenance or proof verification."""
import copy
import json
from pathlib import Path
import subprocess
import tempfile
import unittest
import generate_api as api

REV = 'a' * 40
NAME = 'GradedAlgebra.irrelevant_fg_iff_finiteType'
MODULE = api.EXPECTED[NAME][1]

def fixture():
    records = {m: dict(name=m, declarations=[]) for m in api.MODULES}
    for name, (kind, module) in api.EXPECTED.items():
        path = api.SOURCE_PATHS[module]
        header = (f'<div><span class="decl_kind">{api.DISPLAY_KIND[name]}</span> '
            f'<span class="decl_name">{name}</span> <span>{{A : Type u}} [CommRing A]</span> :'
            '<div class="decl_type">x &lt; y ∧ x ≤ y</div></div>')
        records[module]['declarations'].append(dict(header=header, info=dict(
            name=name, kind=kind, doc='' if name in api.MISSING_DOCSTRINGS else 'Synthetic docstring.',
            line=10, sourceLink='https://github.com/FormalFrontier/graded-rings/blob/' + REV + '/' + path + '#L10-L11',
            docLink='./' + module.replace('.', '/') + '.html#' + name)))
    sources = {p: b'fixture\n' * 40 for p in api.INPUTS}
    for module, path in api.SOURCE_PATHS.items():
        if api.INVENTORY['module_doc_counts'][module]:
            sources[path] = b'/-! Synthetic module documentation. -/\n' + sources[path]
    return records, sources

def row(records):
    return next(r for r in records[MODULE]['declarations'] if r['info']['name'] == NAME)

class Controls(unittest.TestCase):
    def test_complete_inventory(self):
        records, sources = fixture()
        raw, manifest = api.render(records, REV, sources)
        facts = json.loads(manifest)
        self.assertEqual(len(facts['public_declarations']), 104)
        self.assertEqual(raw.count(b'## Module '), 28)
        self.assertEqual(raw.count(b'No declaration docstring is supplied'), 39)
        self.assertEqual(facts['api_sha256'], api.digest(raw))
        self.assertEqual(set(facts['inputs']), set(api.INPUTS))
        self.assertFalse(facts['proof_certification'])

    def test_header_text(self):
        self.assertEqual(api.Header('<div><span>{A : Type u}</span> :<div class="decl_type">x &lt; y ∧ x ≤ y</div></div>').rendered(), '{A : Type u} : x < y ∧ x ≤ y')
        self.assertEqual(api.Header('<span><span>Algebra</span>.<span>TensorProduct</span></span>').rendered(), 'Algebra.TensorProduct')
        records, sources = fixture()
        for kind in ['def', 'axiom', 'unsafe def', 'partial def']:
            altered = copy.deepcopy(records)
            row(altered)['header'] = row(altered)['header'].replace('theorem', kind)
            with self.assertRaises(ValueError):
                api.render(altered, REV, sources)

    def test_corrupt_records(self):
        mutations = [lambda r: r.pop(api.MODULES[0]),
            lambda r: r[MODULE]['declarations'].remove(row(r)),
            lambda r: r[MODULE]['declarations'].append(copy.deepcopy(row(r))),
            lambda r: r[api.MODULES[0]]['declarations'].append(copy.deepcopy(row(r))),
            lambda r: r[MODULE].update(name='Wrong')]
        for key, value in [('name', 'Wrong'), ('kind', 'axiom'), ('doc', ''), ('line', 0),
                           ('line', True), ('line', 999), ('sourceLink', 'moving/main'),
                           ('docLink', 'wrong'), ('doc', '```')]:
            mutations.append(lambda r, k=key, v=value: row(r)['info'].update({k: v}))
        for header in ['<script>bad</script>', '<div><span></div>', '<span onclick="x">bad</span>']:
            mutations.append(lambda r, h=header: row(r).update(header=h))
        for i, mutation in enumerate(mutations):
            with self.subTest(control=i):
                records, sources = fixture()
                mutation(records)
                with self.assertRaises(ValueError):
                    api.render(records, REV, sources)

    def test_missing_docstrings_are_not_fabricated(self):
        records, sources = fixture()
        name = next(iter(api.MISSING_DOCSTRINGS))
        module = api.EXPECTED[name][1]
        target = next(r for r in records[module]['declarations'] if r['info']['name'] == name)
        target['info']['doc'] = 'Fabricated documentation'
        with self.assertRaises(ValueError):
            api.render(records, REV, sources)

    def test_revision_sources_and_module_docs(self):
        records, sources = fixture()
        for rev in ['main', 'a' * 39, '-' * 40]:
            with self.assertRaises(ValueError):
                api.render(records, rev, sources)
        for source in [b'', b'/-! one -/\n/-! two -/', b'/-! outer /- inner -/ -/', b'/-! ``` -/']:
            with self.assertRaises(ValueError):
                api.module_doc(source, MODULE)
        sources.pop('lean-toolchain')
        with self.assertRaises(ValueError):
            api.render(records, REV, sources)

    def test_source_ranges_and_flat_module_paths(self):
        records, sources = fixture()
        self.assertEqual(api.SOURCE_PATHS['Symmetric'], 'examples/Symmetric.lean')
        self.assertEqual(api.SOURCE_PATHS['Axioms'], 'test/Axioms.lean')
        for suffix in ['', '#L0-L1', '#L2-L3', '#L10-L999', '#L10-L9', '#L10-L11?query']:
            altered = copy.deepcopy(records)
            info = row(altered)['info']
            info['sourceLink'] = info['sourceLink'].split('#')[0] + suffix
            with self.assertRaises(ValueError):
                api.render(altered, REV, sources)

    def test_parentless_committed_manifest_binding(self):
        records, sources = fixture()
        raw, manifest = api.render(records, REV, sources)
        with tempfile.TemporaryDirectory(prefix='graded-doc-binding-') as directory:
            root = Path(directory)
            def git(*args):
                return subprocess.check_output(['git', '-c', 'user.name=Test', '-c',
                    'user.email=test@example.invalid', *args], cwd=root, stderr=subprocess.PIPE)
            git('init', '-q')
            for path, value in sources.items():
                (root / path).parent.mkdir(parents=True, exist_ok=True)
                (root / path).write_bytes(value)
            (root / 'docs').mkdir()
            (root / 'docs/api-manifest.json').write_bytes(manifest)
            (root / 'docs/API.md').write_bytes(raw)
            git('add', '.')
            git('commit', '-qm', 'Synthetic parentless documentation fixture')
            head = git('rev-parse', 'HEAD').decode().strip()
            self.assertEqual(api.bind_sources(root, REV, sources, manifest), 'committed-release-manifest')
            self.assertEqual(api.bind_sources(root, head, sources, manifest), 'git-object')
            for changed in [manifest + b' ', manifest.replace(REV.encode(), b'b' * 40)]:
                with self.assertRaises(ValueError):
                    api.bind_sources(root, REV, sources, changed)
            blob = git('rev-parse', 'HEAD:docs/API.md').decode().strip()
            with self.assertRaises(ValueError):
                api.bind_sources(root, blob, sources, manifest)
            (root / 'docs/api-manifest.json').write_bytes(manifest + b' ')
            with self.assertRaises(ValueError):
                api.bind_sources(root, REV, sources, manifest)
            (root / 'docs/api-manifest.json').write_bytes(manifest)
            altered = dict(sources)
            altered[api.INPUTS[0]] += b'changed\n'
            for rev in [head, REV]:
                with self.assertRaises(ValueError):
                    api.bind_sources(root, rev, altered, manifest)
            git('rm', '--', api.INPUTS[0])
            git('commit', '-qm', 'Synthetic missing input')
            with self.assertRaises(subprocess.CalledProcessError):
                api.bind_sources(root, git('rev-parse', 'HEAD').decode().strip(), sources, manifest)

if __name__ == '__main__':
    unittest.main()
