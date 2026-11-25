"""Own versioned display assets, existing public excerpts and atomic static-file writes."""
import base64
import hashlib
import html
from html.parser import HTMLParser
import json
import os
from pathlib import Path, PurePosixPath
import posixpath
import re
import tempfile
from scripts.results_presentation import display_model_names


def encoded(value):
    return value.encode("utf-8") if isinstance(value, str) else value


def digest(value):
    return hashlib.sha256(encoded(value)).hexdigest()


class DisplayAssets:
    def __init__(self, files):
        self.files = files
        self.versions = {}
        self.logos = {}

    def add(self, original, value):
        part = PurePosixPath(original)
        target = f"assets/versioned/{part.stem}.{digest(value)[:12]}{part.suffix}"
        if target in self.files and encoded(self.files[target]) != encoded(value):
            raise ValueError("Versioned display asset collision")
        self.files[target] = value
        self.versions[original] = target
        return target

    @staticmethod
    def relative(page, target):
        return os.path.relpath(target, PurePosixPath(page).parent).replace(os.sep, "/")

    def prepare(self, source_root):
        for name, value in list(self.files.items()):
            if name.startswith("assets/") and PurePosixPath(name).suffix in {".js", ".css", ".svg"}:
                self.add(name, value)
        for path in sorted((Path(source_root) / "site/assets/logos").glob("*.svg")):
            value = path.read_bytes()
            target = self.add("assets/logos/" + path.name, value)
            self.logos[base64.b64encode(value).decode("ascii")] = target

    def page(self, page, value):
        def logo(match):
            target = self.logos.get(match[2])
            return match[0] if target is None else match[1] + self.relative(page, target) + match[3]
        # Only image attributes and the named presentation payload own provider logos.
        # Original code or mathematical prose may also contain literal data URLs.
        value = re.sub(r'''(<img\b[^>]*?\bsrc=["'])data:image/svg\+xml;base64,([A-Za-z0-9+/=]+)(["'])''', logo, value)
        def payload(match):
            data = json.loads(match[2])
            for model in data.get("models", []) + ([data["model"]] if "model" in data else []):
                image = model.get("logo", {})
                source = image.get("data_url", "")
                if source.startswith("data:image/svg+xml;base64,"):
                    target = self.logos.get(source.partition(",")[2])
                    if target is None:
                        raise ValueError(f"Unbound provider logo in {page}")
                    image["data_url"] = self.relative(page, target)
            encoded_data = json.dumps(data, ensure_ascii=False).replace("<", "\\u003c").replace("&", "\\u0026")
            return match[1] + encoded_data + match[3]
        value = re.sub(r'(<script\b[^>]*\bid="(?:data|cost-reference-data)"[^>]*>)([\s\S]*?)(</script>)', payload, value)
        def resource(match):
            target = os.path.normpath(os.path.join(PurePosixPath(page).parent, match[2])).replace(os.sep, "/")
            if target not in self.versions:
                return match[0]
            return match[1] + self.relative(page, self.versions[target]) + match[3]
        value = re.sub(r'''(\b(?:src|href)=["'])((?:\.{1,2}/)*assets/[^"'?]+)(?:\?v=[^"']+)?(["'])''', resource, value)
        scripts = []
        def deferred(match):
            scripts.append('<script defer src="' + match[1] + '"></script>')
            return ""
        value = re.sub(r'<script\s+src="([^"]*assets/versioned/[^"?]+\.js)"></script>', deferred, value)
        if "data-lazy-record=" in value:
            scripts.append('<script defer src="' + self.relative(page, self.versions["assets/records.js"]) + '"></script>')
        return value.replace("</head>", "".join(scripts) + "\n</head>")

    def excerpts(self, page, value):
        if not page.startswith("models/") or not page.endswith("/index.html"):
            return value
        def excerpt(match):
            if len(match[3].encode("utf-8")) < 2048:
                return match[0]
            text = html.unescape(match[3])
            target = self.add("assets/record.txt", text)
            href = html.escape(self.relative(page, target), quote=True)
            return ('<pre' + match[1] + ' data-lazy-record="' + href + '" data-record-code-class="'
                    + match[2] + '"><code><a href="' + href + '" target="_blank" rel="noreferrer">'
                    '<span data-lang-content="zh">查看原始记录 ↗</span>'
                    '<span data-lang-content="en">View original record ↗</span></a></code></pre>')
        return re.sub(r'<pre\b([^>]*)><code class="([\w -]+)">([^<]*)</code></pre>', excerpt, value)


def prepare_publication(files, source_root):
    """Prepare the complete output graph before changing an existing publication."""
    files = dict(files)
    assets = DisplayAssets(files)
    assets.prepare(source_root)
    for page, value in list(files.items()):
        if page.endswith(".html"):
            files[page] = assets.page(page, assets.excerpts(page, value))
    return files


def atomic_write(target, value):
    value = encoded(value)
    if target.is_file() and target.read_bytes() == value:
        return
    target.parent.mkdir(parents=True, exist_ok=True)
    temporary = None
    try:
        with tempfile.NamedTemporaryFile(dir=target.parent, prefix="." + target.name + ".", delete=False) as stream:
            temporary = Path(stream.name)
            stream.write(value)
        os.replace(temporary, target)
    finally:
        if temporary is not None:
            temporary.unlink(missing_ok=True)


def write_publication(destination, files, *, retired=()):
    """Publish assets before pages; retire only paths owned by the prior manifest."""
    dest = Path(destination)
    manifest = dest / "generated-pages.json"
    previous = json.loads(manifest.read_text()) if manifest.exists() else []
    for name in set(previous) | set(files) | set(retired):
        part = Path(name)
        if part.is_absolute() or ".." in part.parts or not (dest / part).resolve().is_relative_to(dest.resolve()):
            raise ValueError("Generated page path escapes site directory")
    # Keep old dependencies available until every new document is atomically installed.
    order = sorted(files, key=lambda name: (name == "index.html", name.endswith(".html"), name))
    for name in order:
        atomic_write(dest / name, files[name])
    atomic_write(manifest, json.dumps(sorted(files), indent=2) + "\n")
    for name in (set(previous) | set(retired)) - set(files):
        target = dest / name
        if target.is_file():
            target.unlink()


def data_literal(value):
    return json.dumps(display_model_names(value), ensure_ascii=False, separators=(',', ':')).replace('<','\\u003c').replace('&','\\u0026').replace('\u2028','\\u2028').replace('\u2029','\\u2029')


class ProseBlocks(HTMLParser):
    """Find outer prose blocks; UI components remain owned by shared templates."""
    def __init__(self, source):
        super().__init__(convert_charrefs=False)
        self.source=source;self.offsets=[0];self.depth=0;self.start=None;self.blocks=[]
        for line in source.splitlines(keepends=True):self.offsets.append(self.offsets[-1]+len(line))
        self.feed(source)
    def source_position(self):
        line,column=self.getpos();return self.offsets[line-1]+column
    def handle_starttag(self,tag,attrs):
        if tag!='div':return
        if self.depth:self.depth+=1
        elif 'prose' in dict(attrs).get('class','').split():
            begin=self.source_position();self.start=(begin,begin+len(self.get_starttag_text()));self.depth=1
    def handle_endtag(self,tag):
        if tag!='div' or not self.depth:return
        self.depth-=1
        if not self.depth:
            begin,inner=self.start;end=self.source_position();self.blocks.append((begin,inner,end,end+len('</div>')))


def lazy_prose(page, source, files):
    for begin,inner,end,close in reversed(ProseBlocks(source).blocks):
        content=source[inner:end]
        if len(content.encode())<1200 or 'data-lazy-record=' in content or '<button' in content:
            continue
        # Links are stored relative to the shared content directory. The lazy
        # renderer rebases them before mounting; standalone reading also works.
        def rebase(match):
            value=html.unescape(match[2])
            if re.match(r'^[a-zA-Z][\w+.-]*:',value) or value.startswith(('/', '#','//')):return match[0]
            target=posixpath.normpath(posixpath.join(str(PurePosixPath(page).parent),value))
            return match[1]+html.escape(posixpath.relpath(target,'assets/content'),quote=True)+match[3]
        content=re.sub(r'''(\bhref=["'])([^"']+)(["'])''',rebase,content)
        digest=hashlib.sha256(content.encode()).hexdigest()
        target='assets/content/'+digest+'.html';script='assets/content/'+digest+'.js'
        files.setdefault(target,'<!doctype html><meta charset="utf-8"><div class="prose">'+content+'</div>')
        files.setdefault(script,'window.MGProseData('+data_literal(digest)+','+data_literal({'html':content,'source':target})+');\n')
        opening=source[begin:inner-1]+' data-lazy-prose="'+html.escape(DisplayAssets.relative(page,script),quote=True)+'" data-prose-key="'+digest+'">'
        placeholder=('<p class="lazy-prose-link"><a href="'+html.escape(DisplayAssets.relative(page,target),quote=True)+'" target="_blank" rel="noreferrer">'
             '<span data-lang-content="zh">阅读本节内容 ↗</span><span data-lang-content="en" hidden>Read this section ↗</span></a></p>')
        source=source[:begin]+opening+placeholder+source[end:]
    return source
