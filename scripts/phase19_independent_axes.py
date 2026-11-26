"""Exact CRT and convolution checks for three distinct coefficient primes."""
from itertools import product
from math import comb, prod


def valuation(n, p):
    if n == 0:
        raise ValueError("valuation requires a nonzero integer")
    v = 0
    while n % p == 0:
        n //= p
        v += 1
    return v


def crt(congruences):
    a, modulus = 0, 1
    for r, q in congruences:
        a += modulus * (((r-a)*pow(modulus, -1, q)) % q)
        modulus *= q
    return a or modulus


def coefficients(primes, end):
    # Integer target residues suffice to test these particular polynomials.
    # The theorem uses independent p-adic targets for all polynomials at once.
    targets = [[11+3*i+j for j in range(len(primes))] for i in range(len(primes))]
    values = [[0]*len(primes) for _ in primes]
    weights = []
    for k in range(1, end+1):
        e, n = 5*k + k*k, 2**(k*k)
        row = []
        for j, pj in enumerate(primes):
            residues = [(1, pj)]
            for i, pi in enumerate(primes):
                if i == j:
                    continue
                q = pi**k
                den = pow(pj, e, q)*pow(2, n, q) % q
                residues.append((den*(targets[i][j]-values[i][j]), q))
            a = crt(residues)
            assert 0 < a <= pj**e and a % pj == 1
            row.append(a)
            for i, pi in enumerate(primes):
                if i != j:
                    modulus = pi**end
                    den = pow(pj, e, modulus)*pow(2, n, modulus) % modulus
                    values[i][j] = (values[i][j] + a*pow(den, -1, modulus)) % modulus
                    assert (values[i][j]-targets[i][j]) % pi**k == 0
        weights.append(row)
    return targets, weights


def check():
    primes = (3, 5, 7)
    targets, weights = coefficients(primes, 6)
    total = 0
    for i, pi in enumerate(primes):
        j, h = (i+1)%3, (i+2)%3
        # Leading coefficient in variable i has limiting valuation one.
        poly = [(1, (i,i,j)), (pi-targets[i][j], (i,i)), (-7, (i,h)), (3, (h,)), (4, ())]
        for k in (4, 5, 6):
            prev = 5*(k-1)+(k-1)**2
            depth = 5*k+k*k
            newest = 2**(k*k)
            for ell in (1, 2, 3):
                t = min(2, ell)
                nominal = 2*prev + t*(depth-prev)
                loss = 1 + valuation(comb(2,t), pi)
                mod = pi**(loss+1)
                cutoff = ell*newest + 3*2**((k-1)**2)+1
                scaled = 0
                for coeff, axes in poly:
                    for indices in product(range(1, k+1), repeat=len(axes)):
                        start = sum(2**(u*u) for u in indices)
                        if start > cutoff:
                            continue
                        pole = sum(5*u+u*u for var, u in zip(axes, indices) if var==i)
                        assert pole <= nominal
                        if nominal-pole > loss:
                            continue
                        unit = pow(2, start, mod)
                        for var, u in zip(axes, indices):
                            if var != i:
                                unit = unit * pow(primes[var], 5*u+u*u, mod) % mod
                        num = coeff * prod(weights[u-1][var] for var, u in zip(axes,indices))
                        scaled += num * pi**(nominal-pole) * pow(unit,-1,mod)
                assert scaled % mod != 0 and valuation(scaled % mod,pi)==loss
                total += 1
    print(f"CRT targets and exact surviving poles verified at {total} partially filled cutoffs.")


if __name__ == "__main__":
    check()
