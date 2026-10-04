"""Exact search and verification (SymPy over QQ, hence also over C).

Matrices M in this file use COLUMNS e_i^2. The papers use ROWS.
No floating-point arithmetic or probabilistic primality tests are used.
Run: python3 exact_search.py
"""
from pathlib import Path
from itertools import product
import json
import sympy as s

ROOT = Path(__file__).resolve().parent

def multiply(M, x, y):
    return M * s.Matrix([a*b for a, b in zip(x, y)])

def square_basis(M, B):
    columns = [multiply(M, B[:,i], B[:,j]) for i in range(B.cols) for j in range(i, B.cols)]
    return s.Matrix.hstack(*columns).columnspace() if columns else []

def derived_dimensions(M):
    B = s.eye(M.rows)
    dims = [B.cols]
    while True:
        columns = square_basis(M, B)
        C = s.Matrix.hstack(*columns) if columns else s.zeros(M.rows, 0)
        dims.append(C.cols)
        if C.cols == B.cols:
            return dims
        B = C

def idempotent_groebner(M):
    x = s.symbols('x0:' + str(M.rows))
    f = multiply(M, s.Matrix(x), s.Matrix(x)) - s.Matrix(x)
    G = s.groebner(list(f), *x, order='grevlex', domain=s.QQ)
    # If the ideal is (x0,...,xn), zero is the unique point over ANY QQ-extension.
    is_zero_only = all(G.reduce(xi)[1] == 0 for xi in x)
    return is_zero_only, [str(p.as_expr()) for p in G.polys]

def jordan_embedding(d):
    """V has basis u,w1,...,w_(d-1); ambient dimension 2d-1."""
    m, n = d-1, 2*d-1
    u = s.ones(n,1)
    W = []
    for i in range(m):
        w = s.zeros(n,1); w[1+2*i] = 1; w[2+2*i] = -1; W.append(w)
    B = s.Matrix.hstack(u, *W)
    columns = [4*u + 2*W[-1]]
    for i in range(m):
        c = W[i] + (W[i-1] if i else s.zeros(n,1))
        columns.extend([c,-c])
    return s.Matrix.hstack(*columns), B

def check_jordan(d):
    M,B = jordan_embedding(d)
    u = B[:,0]; W = [B[:,i] for i in range(1,d)]
    assert B.rank() == d and M.rank() == d
    assert multiply(M,u,u) == 4*u+2*W[-1]
    for i,w in enumerate(W):
        assert multiply(M,u,w) == 2*w + (2*W[i-1] if i else s.zeros(M.rows,1))
        for z in W:
            assert multiply(M,w,z) == s.zeros(M.rows,1)
    assert len(square_basis(M,B)) == d
    free,G = idempotent_groebner(M)
    assert free
    # Symbolic cyclic determinant certifies minimality in the written proof.
    m=d-1
    N=s.zeros(m)
    for i in range(1,m): N[i-1,i]=1
    z=s.Matrix(s.symbols('z0:'+str(m)))
    b=s.zeros(m,1); b[-1]=2
    cyclic=b+4*N*z
    determinant=s.expand(s.Matrix.hstack(*[N**i*cyclic for i in range(m)]).det())
    assert determinant == (-1)**(m*(m-1)//2)*2**m
    return dict(d=d, ambient_dimension=M.rows, matrix_rows=[list(M.row(i)) for i in range(M.rows)],
                derived_dimensions=derived_dimensions(M), groebner=G,
                cyclic_determinant=str(determinant))

def structured_search():
    """A bounded FAMILY search in ambient dimensions 3,4,5, not all matrices.

    In 3 and 4 dimensions we search one square-zero direction (padding in 4).
    In 5 we search two directions and a Jordan coupling. All matrix entries
    are integers; max |entry| <= 6. The minimality filter is justified in REPORT.
    """
    output=[]
    for n in [3,4,5]:
        u=s.ones(n,1)
        v=s.Matrix([0,1,-1]+[0]*(n-3))
        w=s.Matrix([0,0,0,1,-1]) if n==5 else None
        counted=free_count=minimal3_count=0
        first=None
        for a,b,p in product(range(-4,5),range(-2,3),[-1,0,1]):
            if a==0 or b==0 or p==0: continue
            if n<5:
                cols=[a*u+b*v,p*v,-p*v]
                if n==4: cols.append(s.zeros(n,1))
                M=s.Matrix.hstack(*cols); counted+=1
                # intrinsic u²=a u+b v, uv=2p v, v²=0
                free=(a==4*p)
                if free: free_count+=1
                continue
            for q,r in product([-1,0,1],repeat=2):
                if q==0: continue
                M=s.Matrix.hstack(a*u+b*w,p*v,-p*v,q*w+r*v,-q*w-r*v)
                counted+=1
                # Solve the triangular idempotent equations at x=1/a.
                free=(a==4*q or (a==4*p and r!=0))
                exact_free,_=idempotent_groebner(M)
                assert free==exact_free
                if free: free_count+=1
                # A nontrivial Jordan block at the resonant eigenvalue.
                minimal3=free and p==q and r!=0
                if minimal3:
                    minimal3_count+=1
                    if first is None:
                        verified,G=idempotent_groebner(M); assert verified
                        first=dict(parameters=[a,b,p,q,r],matrix_rows=[list(M.row(i)) for i in range(n)],groebner=G)
        output.append(dict(n=n,matrices_checked=counted,idempotent_free=free_count,
                           minimal3_in_this_family=minimal3_count,first_minimal3=first))
    return output

def classify_three(M):
    """Exact criterion for rational structure matrices over C, not over R/Q.

    Returns a witness for the normal form from the report when present.
    Enumerates all projective square-zero directions from ker(M).
    """
    M=s.Matrix(M)
    if M.shape != (3,3): raise ValueError('expected 3x3 column-square matrix')
    if M.rank()!=2: return dict(counterexample=False,reason='rank is not two')
    B=s.Matrix.hstack(*M.columnspace())
    if len(square_basis(M,B))!=2:
        return dict(counterexample=False,reason='square plane is not perfect')
    k=M.nullspace()[0]
    piv=next(i for i in range(3) if k[i]!=0)
    roots=[s.sqrt(k[i]/k[piv]) for i in range(3)]
    others=[i for i in range(3) if i!=piv and roots[i]!=0]
    for signs in product([-1,1],repeat=len(others)):
        v=s.Matrix(roots)
        for i,sgn in zip(others,signs): v[i]*=sgn
        if s.simplify(s.Matrix.hstack(B,v).det())!=0: continue
        u=next(B[:,i] for i in range(2) if s.Matrix.hstack(B[:,i],v).rank()==2)
        P=s.Matrix.hstack(u,v)
        ab=P.gauss_jordan_solve(multiply(M,u,u))[0]
        cd=P.gauss_jordan_solve(multiply(M,u,v))[0]
        a,b=map(s.simplify,ab); c,d=map(s.simplify,cd)
        if c==0 and s.simplify(2*d-a)==0 and a!=0 and b!=0:
            return dict(counterexample=True,u=list(u),v=list(v),a=str(a),b=str(b),c=str(c),d=str(d))
    return dict(counterexample=False,reason='no resonant nilpotent direction')

def main():
    barei=s.Matrix([[-2,0,0],[0,1,-1],[2,-1,1]])
    hu_wen=s.Matrix([[-1,-2,1],[0,2,0],[-1,0,1]])
    assert classify_three(barei)['counterexample']
    assert classify_three(hu_wen)['counterexample']
    checks=[]
    for lam in [-2,-1,1,2,3,4]:
        M=s.Matrix([[-1,-2,1],[0,lam,0],[-1,lam-2,1]])
        criterion=classify_three(M)['counterexample']
        free,G=idempotent_groebner(M)
        assert criterion==free==(lam==2)
        checks.append(dict(parameter=lam,criterion=criterion,groebner=G))
    results=dict(sympy_version=s.__version__,convention='columns are basis squares',
                 search=structured_search(),
                 jordan_family=[check_jordan(d) for d in range(2,6)],
                 barei_classification=classify_three(barei),
                 hu_wen_classification=classify_three(hu_wen),
                 classification_checks=checks)
    # Dimension-two counterexample over QQ: x=2y², y=x² -> x³=1/2.
    rational=s.Matrix([[0,2],[1,0]])
    results['rational_dimension_two']=dict(matrix_rows=[list(rational.row(i)) for i in range(2)],
                                          derived_dimensions=derived_dimensions(rational),
                                          groebner=idempotent_groebner(rational)[1],
                                          nonzero_condition='x0^3 = 1/2; no rational root')
    # Characteristic-two 3D example; Groebner over GF(2) also proves the claim
    # over the algebraic closure, not just by enumeration in the prime field.
    char2=s.Matrix([[0,0,1],[1,1,0],[1,1,1]])
    cu=s.Matrix([0,1,1]); cv=s.Matrix([1,1,0])
    mod2=lambda vector: vector.applyfunc(lambda a: int(a)%2)
    assert mod2(multiply(char2,cu,cu))==cv
    assert mod2(multiply(char2,cu,cv))==cu
    assert mod2(multiply(char2,cv,cv))==s.zeros(3,1)
    x=s.symbols('x0:3')
    equations=multiply(char2,s.Matrix(x),s.Matrix(x))-s.Matrix(x)
    G=s.groebner(list(equations),*x,domain=s.GF(2))
    assert all(G.reduce(xi)[1]==0 for xi in x)
    results['characteristic_two']=dict(matrix_rows=[list(char2.row(i)) for i in range(3)],
                                      groebner=[str(p.as_expr()) for p in G.polys],
                                      verified_products='u^2=v, uv=u, v^2=0 modulo 2; u,v independent',
                                      derived_dimensions_over_char2=[3,2,2])
    (ROOT/'exact_results.json').write_text(json.dumps(results,indent=2,default=str)+'\n')
    print(json.dumps(results,indent=2,default=str))

if __name__=='__main__': main()
