"""Public downloads retain the exact original and selected selfcheck round."""
import hashlib
import json
from pathlib import Path
import tempfile
import unittest

from scripts.results_details import selfcheck_answer_markdown


class RoundEngineeringDownloadsTests(unittest.TestCase):
    def test_bound_relative_links_register_original_bytes_in_site_graph(self):
        with tempfile.TemporaryDirectory() as name:
            folder = Path(name)

            def retain(path, raw):
                target = folder / path
                target.parent.mkdir(parents=True, exist_ok=True)
                target.write_bytes(raw)
                return {'path': path, 'bytes': len(raw),
                        'sha256': hashlib.sha256(raw).hexdigest()}

            original = b'[Lean](./Main.lean) [Text](./Textbook.lean) [Map](alignment.json)\r\n'
            response = retain('answers/R1.md', original)
            files = {name: retain('engineering/R1/' + name, raw) for name, raw in {
                'Main.lean': b'import Textbook\r\n', 'Textbook.lean': b'-- original\n',
                'alignment.json': b'{"round": 1}\n'}.items()}
            manifest = {'schema': 'math-gauge.actual-round-engineering-archive/v1',
                        'round': 1, 'source_repaired': False, 'cross_round_union': False,
                        'original_response_sha256': response['sha256'], 'files': files}
            binding = retain('engineering/R1/manifest.json', json.dumps(manifest).encode())
            row = {'source': {'engineering_manifest': binding}}
            downloads = {}
            rendered = selfcheck_answer_markdown(folder, row, response, 1,
                                                'models/model/index.html', downloads)
            self.assertEqual(len(downloads), 3)
            for source in files.values():
                target = 'downloads/engineering/' + binding['sha256'] + '/' + Path(source['path']).name
                self.assertIn('../../' + target, rendered)
                self.assertEqual(downloads[target].encode(), (folder / source['path']).read_bytes())
            self.assertEqual((folder / response['path']).read_bytes(), original)
            with self.assertRaisesRegex(ValueError, 'exact original answer and round'):
                selfcheck_answer_markdown(folder, row, response, 3, 'models/model/index.html', {})
            legacy_downloads = {}
            self.assertEqual(selfcheck_answer_markdown(folder, {}, response, 1,
                'models/model/index.html', legacy_downloads), original.decode())
            self.assertEqual(legacy_downloads, {})
