# Exhaustive brute-force test of block symmetry: all ordered pairs (and sampled triples) of (+)-indecomposable
# permutations of size <=4, compare F_{t1 (+) t2}(x,y) with F_{t2 (+) t1}(x,y) for n <= N, by brute force from definitions.
import itertools, sys, json, time
from multiprocessing import Pool
import blocks as B
N=int(sys.argv[1]) if len(sys.argv)>1 else 9
def indecomposable(p):
    n=len(p)
    for t in range(1,n):
        if max(p[:t])==t-1: return False
    return True
blocks=[tuple(p) for m in range(1,5) for p in itertools.permutations(range(m)) if indecomposable(p)]
print('indecomposable blocks of size<=4:', len(blocks), flush=True)
# precompute all 3412-avoiding involutions up to N once
INV={n:[p for p in B.involutions(n) if B.avoid3412(p)] for n in range(N+1)}
def Fpat(pat):
    from collections import Counter
    c=Counter()
    for n,L in INV.items():
        for p in L:
            if B.avoids(p,pat):
                c[(n,sum(1 for i in range(n) if p[i]>i))]+=1
    return c
def test(pair):
    a,b=pair
    return (pair, Fpat(B.dsum(a,b))==Fpat(B.dsum(b,a)))
pairs=[(a,b) for i,a in enumerate(blocks) for b in blocks[i:]]  # unordered pairs incl. repeats
t0=time.time()
with Pool(16) as pool:
    res=pool.map(test,pairs,chunksize=4)
bad=[r for r in res if not r[1]]
print('pairs tested',len(res),'failures',len(bad),'time %.1fs'%(time.time()-t0), flush=True)
for r in bad[:20]: print('FAIL',r[0])
# triples: all triples of blocks of size<=3 (7 blocks), all 6 orders
small=[b for b in blocks if len(b)<=3]
def test3(tr):
    vals=set()
    for perm in set(itertools.permutations(range(3))):
        vals.add(tuple(sorted(Fpat(B.dsum(*[tr[i] for i in perm])).items())))
    return (tr, len(vals)==1)
triples=list(itertools.combinations_with_replacement(small,3))
with Pool(16) as pool:
    res3=pool.map(test3,triples,chunksize=2)
bad3=[r for r in res3 if not r[1]]
print('triples tested',len(res3),'failures',len(bad3),'time %.1fs'%(time.time()-t0), flush=True)
for r in bad3[:20]: print('FAIL3',r[0])
json.dump({'N':N,'blocks':len(blocks),'pairs':len(res),'pair_failures':[r[0] for r in bad],'triples':len(res3),'triple_failures':[r[0] for r in bad3]},open((sys.argv[2] if len(sys.argv)>2 else 'blocks_symmetry_n%d.json'%N),'w'))
