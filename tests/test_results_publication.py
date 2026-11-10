"""Static publication preserves original text, dependency identity and ownership."""
import base64
import hashlib
import html
import json
import posixpath
from pathlib import Path
import re
import tempfile
import unittest

from scripts.results_publication import prepare_publication, write_publication


class PublicationTests(unittest.TestCase):
    def test_exact_public_text_and_original_svg_survive_versioned_deferred_output(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            logo = b'<svg xmlns="http://www.w3.org/2000/svg"><path d="M0 0"/></svg>'
            folder = root / 'site/assets/logos'
            folder.mkdir(parents=True)
            (folder / 'provider.svg').write_bytes(logo)
            uri = 'data:image/svg+xml;base64,' + base64.b64encode(logo).decode()
            text = '\ufeff中文 <script>not executed</script> &amp;\n' * 90
            payload = json.dumps({'models': [{'logo': {'data_url': uri}}]})
            page = ('<html><head><link href="../../assets/results.css"></head><body>'
                    '<img src="' + uri + '"><details><pre><code class="language-lean">'
                    + html.escape(text) + '</code></pre></details><pre><code>' + uri + '</code></pre>'
                    '<script id="data" type="application/json">' + payload + '</script>'
                    '<script src="../../assets/results-i18n.js"></script>'
                    '<script src="../../assets/results-core.js"></script></body></html>')
            original_data = '{"unmodified_archive":true}\n'
            files = prepare_publication({'models/example/index.html': page,
                'data.json': original_data, 'assets/results.css': 'body{}',
                'assets/results-i18n.js': 'window.I18n={};',
                'assets/results-core.js': 'window.Core={};', 'assets/records.js': '/* loader */'}, root)
            self.assertEqual(files['data.json'], original_data)
            rendered = files['models/example/index.html']
            deferred = re.search(r'data-lazy-record="([^"]+)"', rendered)[1]
            target = posixpath.normpath('models/example/' + deferred)
            self.assertEqual(files[target], text)
            self.assertIn('<code>' + uri + '</code>', rendered, 'Source literals must not be rewritten')
            self.assertNotIn('<script>not executed', rendered)
            scripts = re.findall(r'<script defer src="([^"]+)"', rendered.split('</head>')[0])
            self.assertIn('results-i18n.', scripts[0])
            self.assertIn('results-core.', scripts[1])
            self.assertIn('records.', scripts[2])
            self.assertIn('href="' + deferred + '"', rendered)
            for name, value in files.items():
                if name.startswith('assets/versioned/'):
                    raw = value.encode() if isinstance(value, str) else value
                    self.assertIn(hashlib.sha256(raw).hexdigest()[:12], name)
            self.assertIn(logo, [value for name, value in files.items() if name.endswith('.svg')])

    def test_publication_retains_unowned_files_and_rejects_escaping_old_manifests(self):
        with tempfile.TemporaryDirectory() as directory:
            dest = Path(directory) / 'site'
            dest.mkdir()
            (dest / 'notes.txt').write_text('Keep this operator file.')
            write_publication(dest, {'old.html': 'previous'})
            write_publication(dest, {'assets/new.js': 'new', 'index.html': 'current'})
            self.assertFalse((dest / 'old.html').exists())
            self.assertEqual((dest / 'notes.txt').read_text(), 'Keep this operator file.')
            (dest / 'generated-pages.json').write_text(json.dumps(['../outside.txt']))
            with self.assertRaisesRegex(ValueError, 'escapes'):
                write_publication(dest, {'index.html': 'must not replace current'})
            self.assertEqual((dest / 'index.html').read_text(), 'current')


if __name__ == '__main__':
    unittest.main()
