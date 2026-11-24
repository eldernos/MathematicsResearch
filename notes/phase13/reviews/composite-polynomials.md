# Independent review of the composite Stoneham polynomial argument

**Verdict.** Let $b\ge2$ and $c>2$ be coprime integers, and let $\alpha_{b,c}=\sum_{j\ge1}c^{-j}b^{-c^j}$. The proposed proof establishes on paper that $P(\alpha_{b,c})$ is normal in base $b$ for every nonconstant $P\in\mathbb Q[X]$. The critical point is that all coordinates of one power use the *same* reflected sequence. This yields a monic polynomial in a single algebraic number. The argument even bounds the total cancellation in the integral model's common denominator, since it applies at every prime dividing $c$.

Reviewed against repository revision `944e0c466978dc636f348552058a4ef65c9ed8be`. The composite conclusion is a written deduction. The existing polynomial Lean theorem covers odd prime powers. [Lean statement](../../../NormalityChecker/StonehamPolynomial.lean#L112)

## The reflected sequence and the positive starting index

Write $e=v_p(c)$ for a fixed $p\mid c$. Let $x=b^{-1}$ in $\mathbb Z_p^\times$, and let $w$ lift its residue to a Teichmüller root of unity, with $w=1$ for $p=2$. On the finite residue group the map $a\mapsto a^c$ is a function, so the forward sequence $w^{c^j}$ has a preperiod ending at some $J$ and then a period $h\ge1$. Extend just this cycle to an $h$-periodic sequence $z_j$ on all integers, aligned so $z_j=w^{c^j}$ for $j\ge J$. The ratio $x/w$ belongs to $1+p\mathbb Z_p$. Modulo $p^L$ this group has order $p^{L-1}$, including at $p=2$. Consequently $x^{c^j}\equiv z_j\pmod{p^L}$ for $j\ge J$ with $ej\ge L-1$.

For $c^k\le n<c^{k+1}$ and a phase $s=k\bmod h$, use $u_i=z_{s-i}$ on every coordinate. The minus sign matters when the period exceeds two. If $R_d(n)$ is the shifted prefix of the ordered expansion of $\alpha_{b,c}^d$, its summands are $c^{-\sum j_a}b^{n-\sum c^{j_a}}$ for $j_a\ge1$ and $\sum c^{j_a}\le n$. Reflection $i_a=k-j_a$ gives the exact identity

```math
c^{dk} b^{-n} R_d(n)
=\sum_{\substack{i\in U_n\\ 0\le i_a<k\ \forall a}}
c^{|i|_1}\prod_{a=1}^d x^{c^{k-i_a}},
\qquad U_n=\left\{i\in\mathbb N^d:\sum_{a=1}^d c^{-i_a}\le n/c^k\right\}.
```

Here $\mathbb N$ starts at zero. Modulo $p^L$ only $|i|_1\le B=\lfloor(L-1)/e\rfloor$ matters. For example, $k\ge B+\max(1,J,\lceil(L-1)/e\rceil)$ suffices. Every surviving $i_a$ then gives a positive original index on the true cycle at the required precision. One can extend the sum to all of $U_n$ and replace its units by $u_{i_a}$ in this congruence. This bound is uniform in $n$, including exact insertion positions. The factor $b^{-n}$ is a $p$-adic unit. The ordinary integer whose cancellation determines the denominator is $c^{dk}R_d(n)$.

## Why every upper set has nonzero mass

Work in the number field $K=\mathbb Q(w)$ with the specified embedding into $\mathbb Q_p$. Write $\mathcal O_K$ for its ring of algebraic integers. For a fixed phase, the one-dimensional sum converges $p$-adically to

```math
S=\sum_{i\ge0} c^i u_i
 =\frac{\sum_{r=0}^{h-1}c^r u_r}{1-c^h}.
```

For each complex embedding of $K$, the last numerator term has modulus $c^{h-1}$ and all preceding terms have combined modulus at most $(c^{h-1}-1)/(c-1)<c^{h-1}$. Thus $S\ne0$. The triangle inequality on the entire numerator gives $|\sigma(S)|\le1/(c-1)<1$ for every embedding $\sigma$. Its field norm therefore has absolute value strictly between zero and one. This proves $S\notin\mathcal O_K$, even though $S\in\mathbb Z_p^\times$.

Let $A_t=\sum_{0\le i<t}c^iu_i\in\mathcal O_K$. The mass of the orthant based at $v$ is $\prod_a(S-A_{v_a})$. Factorization and regrouping are valid because only finitely many indices have $e|i|_1<L$ at any precision $L$. By Dickson's lemma a nonempty upper set $U\subset\mathbb N^d$ has finitely many minimal vertices $v_1,\ldots,v_m$, with $m\ge1$. The intersection for any nonempty subset $H$ of vertices is the orthant at their coordinatewise maximum $v_H$. Inclusion–exclusion expresses the mass of $U$ as $F_U(S)$, where

```math
F_U(X)=\sum_{\varnothing\ne H\subseteq\{1,\ldots,m\}}
 (-1)^{|H|+1}\prod_{a=1}^d(X-A_{(v_H)_a}).
```

Every product has leading coefficient one, and the signed sum of those coefficients is $1-(1-1)^m=1$. So $F_U$ is monic of degree $d$ over $\mathcal O_K$. A zero at $S$ would make $S$ integral over $\mathcal O_K$, hence integral over $\mathbb Z$ by transitivity. This contradicts the norm bound. Injectivity of $K\hookrightarrow\mathbb Q_p$ gives the required $p$-adic nonvanishing.

Choose $A$ with $d c^{-A}<1$. Every shell cut contains the anchor $(A,\ldots,A)$, even with a strict cut at its lower endpoint. Upward closure and anchor membership are closed coordinate conditions, so the family of upper sets containing the anchor is closed in the compact space $\{0,1\}^{\mathbb N^d}$. The mass is continuous since each residue depends on a finite simplex. Its compact image avoids zero, so some $L$ makes every mass nonzero modulo $p^L$. Take the maximum of these precisions over the finitely many phases. This argument includes both sides of every threshold and needs no uniform bound on the number of minimal vertices.

## Reduced denominators and normality

Let $Q(X)=\sum_{r=0}^d a_rX^r\in\mathbb Z[X]$, $a_d\ne0$, and put $R_Q(n)=\sum_r a_rR_r(n)$ with $R_0(n)=b^n$. A common denominator is $c^{dk}$. At the selected prime, the normalized top numerator $c^{dk}R_d(n)$ has valuation at most $L-1$ for all late shells. After multiplying by $a_d$, that bound is $L-1+v_p(a_d)$. Every lower-degree contribution to the same numerator is divisible by $p^{ek}$, since $c^{rk}R_r(n)$ is an integer for $r<d$. Once $ek>L-1+v_p(a_d)$, the top term alone determines the valuation. In particular $v_p(\mathrm{den}(R_Q(n)))\ge edk-(L-1+v_p(a_d))$ on those shells.

One prime gives denominator growth regardless of cancellations at other primes. Applying the proof separately at **all** $p\mid c$ bounds $\gcd(c^{dk}R_Q(n),c^{dk})$ by a fixed constant $C$. Thus $c^{dk}/C\le\mathrm{den}(R_Q(n))\le c^{dk}\le n^d$, and the reduced denominator divides $c^{dk}$. No estimate on primes outside $c$ is required for an integral polynomial.

For a cutoff $N$, split $[0,N)$ into blocks of length $T=\lfloor\sqrt N\rfloor$. Discard the first block, the possible last incomplete block, and each block containing an insertion. Up to $N$ there are $O_Q((1+\log N)^d)$ possible insertion positions by counting ordered tuples, so the discarded share tends to zero. On a retained block starting at $n$, $R_Q(n+i)=b^iR_Q(n)$ for $0\le i<T$. Since $n\ge T$, the reduced starting denominators grow uniformly. They divide powers of $c$ and are at most $N^d\le T^{3d}$ for sufficiently large $T$. For any fixed nonzero Fourier frequency $m$, multiplying the starting rational by $m$ cuts its denominator by at most $|m|$. The fixed-support orbit estimate therefore applies uniformly on every retained block. [Kernel orbit estimate](../../../NormalityChecker/SmoothOrbit.lean#L207)

For each monomial, the true shifted tail tends to zero. An omitted ordered tuple with insertion position $M>n$ has shifted size $c^{-\sum j_a}b^{n-M}\le c^{-\sum j_a}$. These majorants sum to $(c-1)^{-r}$ in degree $r\ge1$, and each individual tuple is eventually included. Dominated convergence and the finite sum of coefficients transfer the model's vanishing Fourier means to the radix shifts of $Q(\alpha_{b,c})$. Weyl's criterion gives normality. For rational $P$ choose a positive common coefficient denominator $D$ and apply the integral result to $Q=DP$. Normality is equivalent under multiplication by $D$, even when $D$ shares factors with $b$. This handles signs and the constant term. [Kernel transfer criterion](../../../NormalityChecker/ArithmeticCertificate.lean#L94) · [Integer scaling equivalence](../../../NormalityChecker/FourierTest.lean#L119)

## Attempts to break the proof

- **Endpoint $c=2$.** For odd $b$ the reflected dyadic units are all one. At degree two and $3/2\le n/2^k<2$, the upper set consists of all pairs except $(0,0)$. Its mass is $(1-2)^{-2}-1=0$. Here $S=-1$ is integral, and the proposed leading-denominator proof genuinely fails. The normality question at this parameter is separate.
- **Rational coefficient denominators.** Take $b=2$, $c=77$ and $P=X/2$. At $n=c^k$, multiplying $R_P(n)$ by $2c^k$ gives an integer congruent to one modulo both $2$ and $c$, since every earlier insertion term is divisible by $2c$. The reduced denominator is exactly $2c^k$. Applying the fixed-support theorem to $R_P$ directly with support dividing $77$ would already fail on infinitely many shells.
- **Cycling at every prime.** For $(b,c)=(2,77)$, the forward residues of $b^{-c^j}$ starting at $j=0$ cycle through $(4,2)$ modulo $7$ and $(6,8,2,7)$ modulo $11$. Neither prime meets the baseline's eventually constant residue hypothesis. This example tests a genuine extension. With $(b,c,p)=(7,93,31)$ the residues start with $9$ before the four-cycle $(16,4,2,8)$. A reversal of the preperiod with the periodic part would give an incorrect model.
- **Distinct coordinates.** For products with unequal phases, strides or dilation factors, different coordinates could supply different algebraic numbers $S_a$. A polynomial monic in the common variable above gives no general nonvanishing at such a tuple. The proposed theorem concerns a single generator with equal coordinates.

### Reproducible finite comparison

The following standard-library Python 3 check compares the entire step function modulo $p^L$ on each tested shell. One side expands all positive-index tuples, using the actual powers of $b^{-1}$. The other extends the reflected cycle to the whole relevant box. Terms are grouped at their exact integer insertion positions, with all contributions up to the left endpoint accumulated there. The check also tries reading the cycle forward.

```python
from collections import defaultdict
from itertools import product
from math import prod

def cycle(b, c, p):
    residues = []
    a = pow(b, -1, p)
    while a not in residues:
        residues.append(a)
        a = pow(a, c, p)
    j = residues.index(a)
    return j, residues[j:]

def jumps(nodes, d, lo, hi, modulus):
    out = defaultdict(int)
    for v in product(nodes, repeat=d):
        pos = sum(t for t, _ in v)
        if pos < hi:
            key = max(lo, pos)
            out[key] = (out[key] + prod(a for _, a in v)) % modulus
    return {n: a for n, a in out.items() if a}

def check(b, c, p, d, L):
    e = 1
    while c % p**(e + 1) == 0:
        e += 1
    j, units = cycle(b, c, p)
    h, modulus = len(units), p**L
    B = (L - 1) // e
    start = B + max(1, j, (L - 1 + e - 1) // e)
    worst = wrong = 0
    for k in range(start, start + h):
        lo, hi = c**k, c**(k + 1)
        inverse = pow(b, -1, modulus)
        actual = [(c**t, c**(k-t) * pow(inverse, c**t, modulus))
                  for t in range(1, k+1)]
        direct = jumps(actual, d, lo, hi, modulus)
        for direction in (-1, 1):
            reflected = []
            for i in range(B+1):
                a = units[(k + direction*i - j) % h]
                lift = pow(a, p**(L-1), modulus)
                reflected.append((c**(k-i), c**i * lift))
            frozen = jumps(reflected, d, lo, hi, modulus)
            if direction == -1:
                assert direct == frozen
            else:
                wrong += direct != frozen
        value = 0
        for n in sorted({lo, *direct}):
            value = (value + direct.get(n, 0)) % modulus
            order = next((t for t in range(L) if value % p**(t+1)), L)
            worst = max(worst, order)
    return j, h, worst, wrong

for case in [(2,77,7,3,8), (2,77,11,3,8), (7,93,31,2,7),
             (3,4,2,2,10), (3,2,2,2,10)]:
    print(case, check(*case))
```

The reflected step function agreed at every tested position. The largest observed valuation is capped at $L$. The last column counts phases where using $k+i$ changes the step function.

| Base, parameter, prime | Degree | Precision | Preperiod | Period | Largest valuation | Phases failing forward reading |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| 2, 77, 7 | 3 | 8 | 0 | 2 | 3 | 0 |
| 2, 77, 11 | 3 | 8 | 0 | 4 | 4 | 4 |
| 7, 93, 31 | 2 | 7 | 1 | 4 | 2 | 4 |
| 3, 4, 2 | 2 | 10 | 0 | 1 | 4 | 0 |
| 3, 2, 2 | 2 | 10 | 0 | 1 | 10 | 0 |

## Relation to prior work

Bailey–Crandall establish normality of individual coprime Stoneham generators. The baseline proves polynomial normality in Lean for odd prime powers and gives a paper argument for composite parameters having some eventually constant local phase. The new input reviewed here handles the cycling case for powers of a single generator. The local literature review discusses Wagner and Kano–Shiokawa on rings of normal numbers, the growth conditions of their constructions, and Vandehey's short-orbit estimates. Its comparisons establish neither a historical priority claim nor coverage of this specific polynomial family by those general theorems. Historical priority remains undetermined in this scoped review. [Baseline composite argument](../../stoneham-powers-products.md#related-parameters-and-the-limit-of-the-argument) · [Literature comparisons and primary references](../../../papers/01-stoneham-polynomials/REVIEW.md#literature-and-scope-of-priority-review)
