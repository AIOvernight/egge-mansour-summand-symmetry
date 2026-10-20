# Brute-force test: is F_{tau_1 (+) ... (+) tau_k}(x,y) symmetric in the blocks for arbitrary (+)-indecomposable tau_i?
import itertools, sys
from collections import Counter
def involutions(n):
    def rec(p):
        i = next((j for j in range(n) if p[j] < 0), None)
        if i is None: yield tuple(p); return
        p[i] = i; yield from rec(p); p[i] = -1
        for j in range(i+1, n):
            if p[j] < 0:
                p[i]=j; p[j]=i; yield from rec(p); p[i]=p[j]=-1
    yield from rec([-1]*n)
def avoids(p, pat):
    m=len(pat); n=len(p)
    if m==0: return False
    for idx in itertools.combinations(range(n), m):
        vals=[p[i] for i in idx]
        ok=True
        for a in range(m):
            for b in range(a+1,m):
                if (vals[a]<vals[b]) != (pat[a]<pat[b]): ok=False; break
            if not ok: break
        if ok: return False
    return True
def avoid3412(p):
    n=len(p)
    for i,j,k,l in itertools.combinations(range(n),4):
        if p[k]<p[l]<p[i]<p[j]: return False
    return True
def dsum(*blocks):
    out=[]; off=0
    for b in blocks:
        out += [v+off for v in b]; off += len(b)
    return tuple(out)
def F(pat, N):
    c=Counter()
    for n in range(N+1):
        for p in involutions(n):
            if avoid3412(p) and avoids(p, pat):
                r=sum(1 for i in range(n) if p[i]>i)
                c[(n,r)]+=1
    return c
N=int(sys.argv[1]) if len(sys.argv)>1 else 8
blocks = {'1':(0,), '21':(1,0), '231':(1,2,0), '312':(2,0,1), '321':(2,1,0), '2413':(1,3,0,2), '3142':(2,0,3,1), '4231':(3,1,2,0), '2431':(1,3,2,0), '3421':(2,3,1,0)}
tests = [('231','21'),('312','21'),('2413','1'),('2413','21'),('3142','1'),('4231','321'),('2431','1'),('3421','21'),('231','312'),('231','1','21'),('2413','1','21'),('312','1','231')]
for t in tests:
    bs=[blocks[x] for x in t]
    results={}
    for perm in set(itertools.permutations(range(len(bs)))):
        pat=dsum(*[bs[i] for i in perm])
        results[perm]=F(pat,N)
    base=list(results.values())[0]
    same=all(v==base for v in results.values())
    print(t, 'SYMMETRIC' if same else 'DIFFER', 'n<=%d'%N)
    if not same:
        for perm,v in results.items():
            diff={k:(v[k],base[k]) for k in set(v)|set(base) if v[k]!=base[k]}
            if diff: print('   perm',perm,'first diffs', sorted(diff.items())[:4])
