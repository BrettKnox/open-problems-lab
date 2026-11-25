"""Finite integer-complexity bounds via residue maxima.

For each cost c and residue r modulo q, retain only the greatest
constructible value M(c,r); zero denotes an unreachable state.
For a split c=i+j, combine reachable maxima by addition and
multiplication. Replacing either child by its residue maximum
preserves the parent's residue and cannot decrease its value.
Structural induction proves exactness; every retained value is
itself constructible. Padding with multiplication by 1 handles
expressions of cost at most c.

Thus M(2*n-1,0) < 2**n, when q divides 2**n, rules out every
expression cheaper than the known 2*n construction. This is a
computational certificate method, not a Lean proof or a record.
The existing full table covers n <= 32 and literature n <= 126.

Run: python computations/integer_complexity/residue_max.py
"""
def residue_max(q, max_cost):
    A = [[0]*q for _ in range(max_cost+1)]
    A[1][1%q] = 1
    for c in range(2,max_cost+1):
        for i in range(1,c//2+1):
            for a in filter(None,A[i]):
                for b in filter(None,A[c-i]):
                    for v in (a+b,a*b):
                        r=v%q
                        if v>A[c][r]: A[c][r]=v
    return A

def brute(max_cost):
    vals=[set() for _ in range(max_cost+1)]; vals[1]={1}
    for c in range(2,max_cost+1):
        for i in range(1,c//2+1):
            for a in vals[i]:
                for b in vals[c-i]: vals[c].update((a+b,a*b))
    return vals

if __name__=='__main__':
    vals=brute(12)
    for q in (2,3,5,8,16,32):
        A=residue_max(q,12)
        for c in range(1,13):
            for r in range(q):
                assert A[c][r]==max((a for a in vals[c] if a%q==r),default=0)
    A=residue_max(512,37)
    for n in range(10,20):
        assert A[2*n-1][0]<2**n
        print(n,A[2*n-1][0],2**n)
