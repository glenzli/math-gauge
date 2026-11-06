from itertools import product
import sys

def mul(a,b,L):
    c=[0]*L
    for i,x in enumerate(a):
        if x:
            for j,y in enumerate(b):
                if y and i+j<L:
                    c[i+j]^=1
    return tuple(c)

def add(a,b): return tuple(x^y for x,y in zip(a,b))

def count(n,M):
    L=2*M-2
    elems=list(product([0,1], repeat=L))
    zero=tuple([0]*L)
    total=len(elems)**(n*n)
    print('L',L,'elems',len(elems),'total',total, file=sys.stderr)
    if total>3_000_000: return None
    cnt=0
    for vals in product(elems, repeat=n*n):
        X=[vals[i*n:(i+1)*n] for i in range(n)]
        ok=True
        for i in range(n):
            for j in range(n):
                s=add(X[i][j],X[j][i])
                for k in range(n):
                    prod=mul(X[k][i],X[k][j],L)
                    sh=tuple([0,0]+list(prod[:-2])) if L>=2 else zero
                    s=add(s,sh)
                if s!=zero:
                    ok=False;break
            if not ok:break
        if ok:cnt+=1
    return cnt
if __name__=='__main__':
    n=int(sys.argv[1]); M=int(sys.argv[2]); print(count(n,M))
