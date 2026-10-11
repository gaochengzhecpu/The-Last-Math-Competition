"""Basis-exchange discovery; every proposed witness has an exact determinant check."""
from itertools import combinations
from pathlib import Path
from random import Random
import json, time
import numpy as np

def det_exact(a):
    a=[list(map(int,row)) for row in a]; old=1; sign=1; m=len(a)
    for k in range(m-1):
        if a[k][k]==0:
            q=next((q for q in range(k+1,m) if a[q][k]),None)
            if q is None: return 0
            a[k],a[q]=a[q],a[k]; sign=-sign
        pivot=a[k][k]
        for i in range(k+1,m):
            for j in range(k+1,m):
                val=a[i][j]*pivot-a[i][k]*a[k][j]
                assert val%old==0
                a[i][j]=val//old
            a[i][k]=0
        old=pivot
    return sign*a[-1][-1]

def factor(n):
    out=[]; p=2
    while p*p<=n:
        if n%p==0:
            out.append(p)
            while n%p==0:n//=p
        p+=1
    if n>1:out.append(n)
    return out

rng=Random(421511); start=time.monotonic()
for n in [9,10,11,12]:
    es=list(combinations(range(1,n),2)); fs=list(combinations(range(n),3))
    r=len(es); ix={e:i for i,e in enumerate(es)}
    A=np.zeros((r,len(fs)),dtype=np.int64)
    for j,(a,b,c) in enumerate(fs):
        for e,s in [((b,c),1),((a,c),-1),((a,b),1)]:
            if 0 not in e:A[ix[e],j]=s
    best=0
    for restart in range(12):
        ids=list(range(r)); inv=np.linalg.inv(A[:,ids].astype(float)); determinant=1.0
        for iteration in range(1600):
            C=inv@A; C[:,ids]=0
            high=np.argwhere(abs(C)>1.01)
            choices=high if len(high) and rng.random()<0.8 else np.argwhere(abs(C)>0.51)
            if not len(choices):break
            k,j=choices[rng.randrange(len(choices))]; v=inv@A[:,j]
            determinant*=v[k]
            row=inv[k,:].copy()/v[k]
            inv-=v[:,None]*row[None,:]; inv[k,:]=row
            ids[k]=int(j)
            if iteration%100==99:
                inv=np.linalg.inv(A[:,ids].astype(float)); determinant=float(np.linalg.det(A[:,ids]))
            candidate=abs(round(determinant)); best=max(best,candidate)
            if candidate and any(p>n for p in factor(candidate)):
                exact=det_exact(A[:,ids]); assert abs(exact)==candidate
                out={'n':n,'faces':[fs[j] for j in ids],'det':exact,'primes':factor(abs(exact)),
                     'restart':restart,'iteration':iteration,'seconds':time.monotonic()-start}
                # The witness is printed; no submission files are modified.
                print(json.dumps(out),flush=True); raise SystemExit
        if time.monotonic()-start>100:break
    print(json.dumps({'n':n,'best':best,'seconds':time.monotonic()-start}),flush=True)
    if time.monotonic()-start>100:break
