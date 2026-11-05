import re
from pathlib import Path
s = Path('FreshC003.lean').read_text()
names = re.findall(r'^(?:theorem|def|noncomputable def|structure) ([A-Za-z_][A-Za-z_0-9]*)', s, re.M)
mapping = {n: 'c%02d' % i for i, n in enumerate(names, 1)}
mapping['Chapter3Fresh'] = 'C3'
for old, new in sorted(mapping.items(), key=lambda p: -len(p[0])):
    s = re.sub(r'\b' + re.escape(old) + r'\b', new, s)
lines = []
for line in s.splitlines():
    n = len(line) - len(line.lstrip(' '))
    lines.append(line.rstrip())
s = '\n'.join(lines) + '\n'
Path('CompactC003.lean').write_text(s)
Path('CurrentNameMapC003.txt').write_text('\n'.join(f'{k} {v}' for k, v in mapping.items()))
print(len(s), len(s.encode()), len(names))
