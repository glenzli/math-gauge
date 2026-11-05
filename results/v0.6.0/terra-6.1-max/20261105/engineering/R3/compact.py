import re, json

s = open('MainReadable.lean').read()
names = re.findall(r'^(?:noncomputable )?(?:def|theorem|structure)\s+([A-Za-z][A-Za-z0-9_]*)', s, re.M)
names = [x for x in names if len(x) >= 15]
mapping = {x: 'z' + str(i) for i, x in enumerate(names)}
pat = re.compile(r'\b(' + '|'.join(sorted(map(re.escape, names), key=len, reverse=True)) + r')\b')
def ren(s): return pat.sub(lambda m: mapping[m.group()], s)
open('Main.lean', 'w').write(ren(s))
j = json.load(open('alignmentReadable.json'))
for e in j['items']:
    for d in e['declarations']:
        if d['file'] == 'Main.lean': d['name'] = ren(d['name'])
    e['representation'] = ren(e['representation'])
    if e['status'] == 'incomplete':
        e['representation'] = '该原文项的构造、分支或证明尚未完成。'
with open('alignment.json','w',encoding='utf-8') as out:
    out.write('{\n  "case_id": "MG-C003",\n  "version": "0.1.1",\n  "items": [\n')
    for i, e in enumerate(j['items']):
        out.write('    '+json.dumps(e,ensure_ascii=False,separators=(',',':')) + (',' if i+1<len(j['items']) else '')+'\n')
    out.write('  ]\n}\n')
print('names', len(mapping))
