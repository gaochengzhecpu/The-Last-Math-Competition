"""Independent exact integer verification; uses only the Python standard library."""
from ast import literal_eval
from fractions import Fraction
from itertools import combinations
from pathlib import Path
import json,re
FACETS = [[1, 5, 6], [1, 2, 8], [3, 5, 7], [0, 1, 3], [3, 6, 8], [1, 7, 9], [0, 1, 8], [1, 4, 9], [0, 1, 7], [0, 2, 4], [1, 4, 8], [3, 5, 8], [2, 5, 6], [2, 5, 8], [4, 6, 8], [0, 3, 4], [4, 7, 8], [2, 3, 6], [2, 4, 9], [2, 3, 9], [0, 3, 9], [3, 4, 5], [0, 1, 2], [0, 4, 7], [4, 5, 6], [4, 5, 9], [3, 6, 7], [0, 5, 7], [1, 2, 6], [0, 5, 9], [6, 7, 9], [0, 6, 8], [0, 6, 9], [2, 7, 8], [2, 6, 7], [0, 8, 9]]

def transpose(a):return [list(row) for row in zip(*a)]
def multiply(a,b):return [[sum(x*y for x,y in zip(row,col)) for col in zip(*b)] for row in a]
def identity(n,scale=1):return [[scale*int(i==j) for j in range(n)] for i in range(n)]
def inverse(a):
    n=len(a); a=[[Fraction(x) for x in row]+[Fraction(i==j) for j in range(n)] for i,row in enumerate(a)]
    for j in range(n):
        k=next(k for k in range(j,n) if a[k][j]); a[j],a[k]=a[k],a[j]
        t=a[j][j]; a[j]=[x/t for x in a[j]]
        for i in range(n):
            if i!=j:
                t=a[i][j]; a[i]=[x-t*y for x,y in zip(a[i],a[j])]
    return [row[n:] for row in a]

def determinant(a):
    a=[row.copy() for row in a]; n=len(a); previous=1; sign=1
    for k in range(n-1):
        if not a[k][k]:
            q=next((i for i in range(k+1,n) if a[i][k]),None)
            if q is None:return 0
            a[k],a[q]=a[q],a[k];sign=-sign
        pivot=a[k][k]
        for i in range(k+1,n):
            for j in range(k+1,n):
                x=a[i][j]*pivot-a[i][k]*a[k][j]
                assert x%previous==0
                a[i][j]=x//previous
            a[i][k]=0
        previous=pivot
    return sign*a[-1][-1]

def main():
    text=(Path(__file__).parent/'lean/Main/Certificate.lean').read_text(encoding='utf-8')
    def data(name):
        source=re.search(r'def '+re.escape(name)+r' : [^\n]* :=\n  (.*?)(?=\ndef )',text,re.S)
        assert source,name
        return literal_eval(source.group(1).strip().replace('![','['))
    edges=list(combinations(range(10),2)); faces=[tuple(t) for t in FACETS]
    assert len(faces)==36 and len(set(faces))==36 and all(0<=a<b<c<10 for a,b,c in faces)
    assert data('edge')==edges and data('face')==faces
    A=[[int(e==(b,c))-int(e==(a,c))+int(e==(a,b)) for a,b,c in faces] for e in edges]
    D=[[int(v==b)-int(v==a) for a,b in edges] for v in range(10)]
    B=A[9:]; assert determinant(B)==-11
    C=[[11*x for x in row] for row in inverse(B)]
    assert all(x.denominator==1 for row in C for x in row)
    C=[[int(x) for x in row] for row in C]
    H=[[0]*9+row for row in C]; assert data('recovery')==H
    T=[[11*int(a==0 and b==v) for v in range(10)] for a,b in edges]
    assert multiply(H,A)==identity(36,11)
    AH=multiply(A,H); TD=multiply(T,D)
    assert [[x+y for x,y in zip(a,b)] for a,b in zip(AH,TD)]==identity(45,11)
    assert all(x==0 for row in multiply(D,A) for x in row)
    L=multiply(A,transpose(A)); reduced=multiply(B,transpose(B))
    assert determinant(reduced)==121
    b=data('witness'); x=data('preimage'); w=data('detector'); v=data('detectorMultiple')
    assert multiply(D,[[t] for t in b])==[[0] for _ in range(10)]
    assert multiply(L,[[t] for t in x])==[[11*t] for t in b]
    assert multiply([w],L)==[[121*t for t in v]]
    pairing=sum(a*b for a,b in zip(w,b)); assert pairing==4081 and pairing%121!=0
    print(json.dumps({'id':'00000004215','vertices':10,'edges':45,'triangles':36,
      'reduced_boundary_determinant':-11,'reduced_laplacian_determinant':121,
      'chain_certificates':'PASS','torsion_prime':11,'detector_pairing':pairing,
      'detector_modulus':121,'nonzero_residue':pairing%121,'exact_torsion_certificate':'PASS'}))
if __name__=='__main__':main()
