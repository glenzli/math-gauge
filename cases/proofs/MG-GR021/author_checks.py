"""Exact supplementary author mathematics; not a model runner or universal proof."""
from collections import Counter
from datetime import datetime,timezone
from fractions import Fraction
from hashlib import sha256
from itertools import product
from pathlib import Path
import json
ROOT=Path(__file__).resolve().parent

class Ring:
    """Z/2^M, or (Z/2^M)[t]/(t^2+t+1), or t^2-2."""
    def __init__(self,kind,bits):
        self.kind=kind;self.bits=bits;self.modulus=2**bits
        self.rank=1 if kind=='base' else 2
        self.size=self.modulus**self.rank
    def pair(self,x):
        return (x%self.modulus,x//self.modulus) if self.rank==2 else (x%self.modulus,0)
    def encode(self,a,b=0):return a%self.modulus+(self.modulus*(b%self.modulus) if self.rank==2 else 0)
    def add(self,x,y):
        if self.rank==1:return (x+y)%self.modulus
        a,b=self.pair(x);c,d=self.pair(y);return self.encode(a+c,b+d)
    def mul(self,x,y):
        if self.rank==1:return (x*y)%self.modulus
        a,b=self.pair(x);c,d=self.pair(y)
        if self.kind=='unramified2':return self.encode(a*c-b*d,a*d+b*c-b*d)
        if self.kind=='ramified_minus1':return self.encode(a*c-b*d,a*d+b*c)
        return self.encode(a*c+2*b*d,a*d+b*c)
    def scalar(self,a):return self.encode(a)
    def reduce_to(self,x,other):return other.encode(*self.pair(x))
    def frobenius(self,x):
        assert self.kind=='unramified2'
        a,b=self.pair(x);return self.encode(a-b,-b)

def matrix_mul(a,b,ring):
    return (ring.add(ring.mul(a[0],b[0]),ring.mul(a[1],b[2])),
            ring.add(ring.mul(a[0],b[1]),ring.mul(a[1],b[3])),
            ring.add(ring.mul(a[2],b[0]),ring.mul(a[3],b[2])),
            ring.add(ring.mul(a[2],b[1]),ring.mul(a[3],b[3])))

def transpose(u):return (u[0],u[2],u[1],u[3])

def orthogonal_group(ring):
    previous=Ring(ring.kind,ring.bits-1)
    even=[ring.encode(2*a,2*b) for a,b in map(previous.pair,range(previous.size))]
    odd=[ring.add(1,x) for x in even]
    result=set()
    for a,b,c,d in product(odd,even,even,odd):
        if ring.add(ring.mul(a,a),ring.mul(c,c))!=1:continue
        if ring.add(ring.mul(b,b),ring.mul(d,d))!=1:continue
        if ring.add(ring.mul(a,b),ring.mul(c,d))!=0:continue
        result.add((a,b,c,d))
    return result

def block_condition(u,projection,ring):
    transformed=matrix_mul(matrix_mul(transpose(u),projection,ring),u,ring)
    original=(transformed[1]==0 and transformed[2]==0)
    matched=matrix_mul(u,(1,0,0,0),ring)==matrix_mul(projection,u,ring)
    assert original==matched
    return original

def enhanced_norm(u,ring):
    higher=Ring(ring.kind,ring.bits+1)
    raised=tuple(higher.encode(*ring.pair(x)) for x in u)
    gram=matrix_mul(transpose(raised),raised,higher)
    return gram[0]==1 and gram[3]==1


def conjugate(x,ring):
    a,b=ring.pair(x)
    return ring.encode(a,-b)


def gamma_base(u,bits):
    modulus=2**(bits+1)
    return tuple((((u[j]*u[j]+u[j+2]*u[j+2]-1)%modulus)//2**bits) for j in (0,1))


def first_order_dual_numbers():
    out=[]
    # x+y*eta, eta^2=0. This checks all block parity inputs, not only epsilon=0.
    for n in range(1,5):
        edges=[(a,b) for a in range(n) for b in range(a+1,n)]
        for parities in product(range(2),repeat=n):
            count=0
            for values in product(range(4),repeat=len(edges)):
                rhs=list(parities)
                for (a,b),v in zip(edges,values):
                    square=v&1
                    rhs[a]^=square;rhs[b]^=square
                if not any(rhs):count+=2**n
            expected=2*4**len(edges) if sum(parities)%2==0 else 0
            assert count==expected,(n,parities,count,expected)
            out.append({'n':n,'c':parities,'actual_first_order':count})
    return out


reports={'schema':'math-gauge.draft-author-checks/v1','human_review':'pending',
         'independent_review':False,'lean':'not-performed','candidate_calls':0}
reports['first_order_nonreduced_ring']=first_order_dual_numbers()
sets={};finite=[]
for kind,levels in [('base',range(2,6)),('ramified_minus1',range(2,4)),('ramified2',range(2,4))]:
    q=2 if kind=='base' else 4
    for bits in levels:
        ring=Ring(kind,bits);group=orthogonal_group(ring)
        for name,r,D,eps in [('single-block',1,1,False),('split-trivial',2,0,False),('split-obstructed',2,0,True)]:
            inv5=pow(5,-1,ring.modulus)
            projection=tuple(ring.scalar(x*inv5) for x in (1,2,2,4)) if eps else (1,0,0,0)
            values=group if name=='single-block' else {u for u in group if block_condition(u,projection,ring)}
            actual={u for u in values if enhanced_norm(u,ring)}
            expected_C=q**(D+2) if bits==2 else (0 if eps else 2**r*q**((bits-1)*D+2))
            expected_R=0 if eps else 2**r*q**((bits-1)*D)
            assert len(values)==expected_C,(kind,bits,name,'C',len(values),expected_C)
            assert len(actual)==expected_R,(kind,bits,name,'R',len(actual),expected_R)
            sets[kind,bits,name]=(ring,values,actual,r,D,eps)
            finite.append({'ring':kind,'M':bits,'case':name,'C':len(values),'R_by_norm_test':len(actual)})
reports['finite_ring_exhaustion']=finite

fixed_reports=[];fixed_sets={}
for (kind,bits,name),(ring,values,actual,r,D,eps) in sets.items():
    if kind=='base':continue
    base,base_C,base_R,_,_,_=sets['base',bits,name]
    for label,collection in [('C',values),('R',actual)]:
        fixed={u for u in collection if tuple(conjugate(x,ring) for x in u)==u}
        fixed_sets[kind,bits,name,label]=fixed
        predicted=set()
        for v in base_C:
            for binary in product(range(2),repeat=4):
                if binary[1]!=binary[2]:continue
                if D==0 and (binary[1] or binary[2]):continue
                if label=='R':
                    if binary[0] or binary[3]:continue
                    rho=int(kind=='ramified_minus1' and bits==2)
                    degree=(binary[2],binary[1])
                    if gamma_base(v,bits)!=tuple(rho*x for x in degree):continue
                u=tuple(ring.encode(a,2**(bits-1)*b) for a,b in zip(v,binary))
                predicted.add(u)
        assert fixed==predicted,(kind,bits,name,label,'fixed-set mismatch')
        expected=len(base_C)*2**(D+2) if label=='C' else len(base_R)*2**D
        assert len(fixed)==expected
        pending=set(collection);orbits=0
        while pending:
            u=pending.pop();other=tuple(conjugate(x,ring) for x in u)
            assert other in collection
            pending.discard(other);orbits+=1
        assert orbits==(len(collection)+len(fixed))//2
        fixed_reports.append({'ring':kind,'M':bits,'case':name,'set':label,
                              'fixed':len(fixed),'orbits':orbits,'matrix_classification_matches':True})
reports['fixed_sets_and_orbits']=fixed_reports

fibers=[]
for (kind,bits,name),(ring,values,actual,r,D,eps) in sets.items():
    if (kind,bits+1,name) not in sets:continue
    higher,hi_C,hi_R,_,_,_=sets[kind,bits+1,name]
    q=2 if kind=='base' else 4
    for label,source,target,expected_size in [('C',hi_C,actual,q**(D+2)),('R',hi_R,actual,q**D)]:
        image=Counter(tuple(higher.reduce_to(x,ring) for x in u) for u in source)
        assert set(image)==target
        assert set(image.values())==({expected_size} if target else set())
        fibers.append({'ring':kind,'M':bits,'set':label,'fixed':False,'image_size':len(image),'nonempty_fiber':expected_size if image else None})
        if kind=='base':continue
        fixed_source=fixed_sets[kind,bits+1,name,label]
        base_R=sets['base',bits,name][2]
        embedded={tuple(ring.scalar(x) for x in u) for u in base_R}
        image=Counter(tuple(higher.reduce_to(x,ring) for x in u) for u in fixed_source)
        assert set(image)==embedded
        expected_size=4**(D+(2 if label=='C' else 0))
        assert set(image.values())==({expected_size} if image else set())
        fibers.append({'ring':kind,'M':bits,'set':label,'fixed':True,'image_size':len(image),'nonempty_fiber':expected_size if image else None})
reports['all_reduction_images_and_fibers']=fibers

# Concrete classification difference at the exceptional precision.
for kind,expect in [('ramified_minus1',True),('ramified2',False)]:
    ring=Ring(kind,2)
    example=(ring.encode(1),ring.encode(2,2),ring.encode(2,2),ring.encode(1))
    assert example in sets[kind,2,'single-block'][1]
    assert (example in sets[kind,2,'single-block'][2])==expect
reports['M2_difference']={'constant_part':[[1,2],[2,1]],'imaginary_binary_part':[[0,1],[1,0]],
                         'actual_over_Q2i':True,'actual_over_Q2sqrt2':False}

# Uniform actual sharpness witness: exact binomial coefficients evaluated to a
# precision where the remaining tail is provably zero. Universal proof is P10.
sharp=[]
for kind in ['ramified_minus1','ramified2']:
    for bits in range(2,11):
        precision=bits+5;ring=Ring(kind,precision)
        h=ring.encode(1,1) if kind=='ramified_minus1' else ring.encode(0,1)
        b=ring.mul(ring.scalar(2**(bits-1)),h)
        # Keep exact integer coefficients before the divisions in binom(1/2,n).
        # Dividing a power already reduced modulo2^P would lose precision.
        negative=(0,-2**(2*bits-1)) if kind=='ramified_minus1' else (-2**(2*bits-1),0)
        mu=-1 if kind=='ramified_minus1' else 2
        a=1;power=(1,0);coefficient=Fraction(1)
        # term n>=precision has valuation >=n+1 since x is divisible by8.
        for n in range(1,precision):
            pa,pb=power;xa,xb=negative
            power=(pa*xa+mu*pb*xb,pa*xb+pb*xa)
            coefficient*=Fraction(3-2*n,2*n)
            ca,cb=(coefficient*v for v in power)
            assert ca.denominator==cb.denominator==1
            term=ring.encode(int(ca),int(cb))
            a=ring.add(a,term)
        u=(a,ring.mul(ring.scalar(-1),b),b,a)
        assert matrix_mul(transpose(u),u,ring)==(1,0,0,1)
        small=Ring(kind,bits);ubar=tuple(ring.reduce_to(v,small) for v in u)
        assert tuple(conjugate(v,small) for v in ubar)==ubar
        assert any(small.pair(v)[1] for v in ubar)
        low=Ring(kind,bits-1)
        assert tuple(ring.reduce_to(v,low) for v in u)==(1,0,0,1)
        sharp.append({'ring':kind,'M':bits,'tested_to_bits':precision,'orthogonal':True,'fixed_mod_M':True,'no_base_mod_M':True,'identity_mod_M_minus_1':True})
reports['uniform_actual_sharpness']=sharp

rubric=json.loads((ROOT/'diagnostic-rubric.json').read_text())
assert sum(item['points'] for item in rubric['criteria'])==100
assert all(sum(c['points'] for c in item['checks'])==item['points'] for item in rubric['criteria'] if 'checks' in item)
draft=json.loads((ROOT/'original-draft.json').read_text())
assert draft['candidate_files']==rubric['candidate_projection']==['task.md']
task=(ROOT/'task.md').read_text()
for forbidden in ['Artin','Schreier','Cayley','gamma','列范数','多一位','epsilon','幂等精确化','模4异常','二项式','Hensel','下降损失']:
    assert forbidden not in task,forbidden
reports['candidate_hint_audit']={'projection':['task.md'],'method_and_exception_terms_absent':True,
    'scope':'Final targets and exact definitions remain visible; no author proof route or expected answers provided.'}
reports['universal_argument_not_replaced_by_enumeration']=['All dimensions and positive block ranks','All M>=2','Actual infinite lifts','Fixed inverse limits','Sharp descent and exact D=0 boundary']
reports['checked_at']=datetime.now(timezone.utc).isoformat();reports['status']='passed'
reports['artifact_sha256']={p.name:sha256(p.read_bytes()).hexdigest() for p in ROOT.iterdir() if p.is_file() and p.name!='author-checks.json'}
(ROOT/'author-checks.json').write_text(json.dumps(reports,ensure_ascii=False,indent=2)+'\n')
print(json.dumps({'status':'passed','finite_ring_cases':len(finite),'fixed_class_cases':len(fixed_reports),'map_cases':len(fibers),'sharpness_cases':len(sharp)},ensure_ascii=False))

