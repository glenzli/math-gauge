// Build-time, offline Markdown and MathML. Source answers are never rewritten.
import {createRequire} from 'node:module';
const require = createRequire(import.meta.url);
const MarkdownIt = require('./vendor/markdown-it.min.js');
const katex = require('./vendor/katex.min.js');
const md = new MarkdownIt({html: false, linkify: false, typographer: false});
md.inline.ruler.before('escape', 'evidence_math', (state, silent) => {
  const start = state.pos, source = state.src;
  const opener = ['$$', '\\[', '\\(', '$'].find(s => source.startsWith(s, start));
  if (!opener || (opener === '$' && /\s/.test(source[start + 1] || ' '))) return false;
  const closer = {'$$':'$$', '\\[':'\\]', '\\(':'\\)', '$':'$'}[opener];
  let end = source.indexOf(closer, start + opener.length);
  while (end > 0 && source[end - 1] === '\\') end = source.indexOf(closer, end + closer.length);
  if (end < 0 || (opener === '$' && /\s/.test(source[end - 1]))) return false;
  if (!silent) {
    const token = state.push('evidence_math', '', 0);
    token.content = source.slice(start + opener.length, end);
    token.meta = {display: opener === '$$' || opener === '\\['};
  }
  state.pos = end + closer.length;
  return true;
});
md.renderer.rules.evidence_math = (tokens, index) => katex.renderToString(
  // mathtools' parenthesized small matrix has an equivalent KaTeX construction.
  tokens[index].content.replaceAll('\\begin{psmallmatrix}', '\\left(\\begin{smallmatrix}')
    .replaceAll('\\end{psmallmatrix}', '\\end{smallmatrix}\\right)'), {
  output: 'mathml', displayMode: tokens[index].meta.display, throwOnError: false,
  trust: false, strict: 'ignore', maxExpand: 1000
});
// Reading archived evidence must not initiate third-party requests.
md.renderer.rules.image = (tokens, index) => '<span class="image-description">['
  + md.utils.escapeHtml(tokens[index].content || '图像：见原文件') + ']</span>';
let input = '';
for await (const chunk of process.stdin) input += chunk;
const sources = JSON.parse(input);
process.stdout.write(JSON.stringify(sources.map(s => md.render(s))));
