# Independent review of the dyadic Stoneham powers through degree fifteen

**Verdict on `ff74d4c`.** Fix an odd integer *b* ≥ 3 and let α be the sum of $2^{-j}b^{-2^j}$ over positive integers *j*. For every rational polynomial *P* of degree 3 through 15 inclusive, *P*(α) is normal in base *b*. Arbitrary rational quadratic, linear and constant coefficients are allowed. I reproduced the exact mass and denominator certificates in all 13 degrees. The new unconditional Lean normality theorem covers degree 4. The earlier odd prime-power theorem covers 3, 5, 7, 9, 11 and 13. The proofs for 6, 8, 10, 12, 14 and 15 use external finite arithmetic and the retained-denominator criterion. There is a minor empty-set qualification to a secondary estimate below. [Track B proof](../higher-degrees.md) · [Quartic theorem](../../../NormalityChecker/DyadicQuartic.lean) · [Odd prime-power theorem](../../../NormalityChecker/StonehamOddDegree.lean)

## What the cut counts

Let *n* ≥ 1 be an integer, put $k=\lfloor\log_2 n\rfloor$, and write $t=n/2^k$. The shifted prefix $R_{d,n}$ sums $2^{-\sum j_i}b^{n-\sum 2^{j_i}}$ over ordered positive-index tuples with $\sum 2^{j_i}\le n$. Every index satisfies $j_i\le k$. Reflecting to $v_i=k-j_i$ gives $0\le v_i<k$. If $w=\sum v_i$ and $\tau=\sum 2^{-v_i}$, inclusion is exactly $\tau\le t$. Write $M_d(t)$ for the infinite sum of $2^w$ over that weak cut with all deficits nonnegative. Each residue modulo a power of two uses only finitely many tuples.

To evaluate the exact integer mass, specify the *m* coordinates equal to zero. Shifting the other deficits down one doubles their insertion sum and removes one factor of two from each weight. Thus

```math
M_d(t)=\sum_{m=0}^d {d\choose m}2^{d-m}M_{d-m}(2(t-m)).
```

At dimension zero the weak cut contributes 1 precisely for $t\ge0$. In positive dimension it is empty for $t\le0$ and full for $t\ge d$, with full mass $(-1)^d$. The strict version uses $t>0$ in dimension zero and $t>d$ for the full-box shortcut. For fixed positive *t*, consecutive calls with *m* = 0 double the cutoff until it reaches a boundary. Every other recursive step lowers dimension. This proves termination for real cutoffs as well as dyadic ones.

I checked the recurrence by a different exact integer computation. At a test endpoint $t=A/2^p$, clip each deficit at $m=p+d$. To justify clipping, suppose *r* ≥ 1 letters reach that depth in an accepted word and let *s* be the insertion sum of the other letters. Then $t-s>0$. After binary carries, the fractional part of $2^p s$ has at most $d-r$ ones, so $t-s\ge 2^{-p-(d-r)}$. The *r* clipped letters add at most $r2^{-m}<2^{-p-(d-r)}$. Clipping preserves both the weak and strict tests. The signed weights on the clipped alphabet are $2^v$ for $v<m$ and $-2^m$ at the tail, by the geometric sum in the 2-adic integers.

In grid units of $2^{-m}$, subtract the insertion from $Q=2^m t$ for a weak cut, or from $Q=2^m t-1$ for a strict cut. Read the bits from low to high. At bit *i*, let *u* be the number of unused coordinates, *h* the incoming borrow, and *z* the bit of *Q*. Assigning *c* coordinates to deficit $v=m-i$ multiplies the signed weight by $\binom{u}{c}\lambda_v^c$, where $\lambda_v$ is the clipped weight. The next state has $u-c$ unused coordinates and borrow $\lfloor(h+c+1-z)/2\rfloor$. Start at $(d,0)$. After bit *m*, keep states with zero unused coordinates and borrow at most $\lfloor Q/2^{m+1}\rfloor$. This agreed with the recurrence as **integers** on 10,460 tests, using both inequalities at every reported residue change, the shell start and the endpoint 2 in all 13 degrees. For example, the weak quartic mass at 1 is 2304, the strict mass there is −4096 and the strict mass at 2 is −256.

## Finite proof over the whole shell

At precision *L*, set $S=2^{L-1}$. Start with the single coefficient 1 at position 0. In each of *d* passes, append one letter *v* with $0\le v<L$, advancing by $S/2^v$ and multiplying by $2^v$. Add coefficients at equal positions modulo $2^L$ and discard positions at or above $2S$ after each pass. All later advances are positive, and a letter with $v\ge L$ already has zero weight. This ordered convolution uses neither sorted tuples nor orbit pruning. After the last pass, add all coefficients at or below *S* for the value at 1 and accumulate the remaining changes in increasing order.

The resulting right-continuous function agrees with Track B at every residue cell. All ties enter together, including ties at 1. Each open interval between changes has the preceding residue at every real cutoff. The strict cut at 2 checks the last cell. At the integer position $n=2^{k+1}$ the next shell begins with its weak cut at 1. These endpoint conventions cover late positive-index positions on both sides of every insertion.

The table gives the number of nonzero **orbits** before jumps at equal positions are combined, the number of cumulative residue cells including 1, the range of $\ell=\nu_2(M_d(t))$, and a cutoff attaining the maximum. All weak residues are nonzero at $L=1+\max\ell$. At the witness the residue is $2^{L-1}$, proving that one less bit fails. The final column is a sufficient shell for transferring the entire residue table to the positive-index prefix.

| Degree | Surviving orbits | Residue cells | Loss range | Maximum-loss witness | First sufficient shell |
| ---: | ---: | ---: | ---: | ---: | ---: |
| 3 | 12 | 9 | 3–6 | 9/8 | 5 |
| 4 | 5 | 4 | 7–8 | 1 | 4 |
| 5 | 91 | 37 | 9–15 | 65/64 | 9 |
| 6 | 739 | 208 | 12–24 | 149/128 | 15 |
| 7 | 479 | 131 | 14–24 | 169/128 | 13 |
| 8 | 1694 | 340 | 20–33 | 1345/1024 | 17 |
| 9 | 1616 | 296 | 23–35 | 513/512 | 16 |
| 10 | 675 | 133 | 27–36 | 19/16 | 13 |
| 11 | 5430 | 632 | 30–45 | 561/512 | 19 |
| 12 | 1521 | 242 | 35–46 | 79/64 | 15 |
| 13 | 10716 | 977 | 38–55 | 257/256 | 21 |
| 14 | 10556 | 906 | 42–59 | 375/256 | 21 |
| 15 | 18098 | 1302 | 45–64 | 133/128 | 23 |

## Transfer to the exact denominator

For a sorted tuple of largest deficit *a*, let *C* be its multinomial multiplicity and $h=w+\nu_2(C)$. In $B=2^{dk}b^{-n}R_{d,n}$ the entire orbit contributes $C2^w b^{-2^k\tau}$ once $k\ge a+1$ and $t\ge\tau$. Permutations share the same radix unit. Odd squares are 1 modulo 8, so $b^{2^j}\equiv1\pmod{2^{j+2}}$ for every $j\ge1$ by repeated squaring. Every radix factor and its inverse are therefore 1 modulo $2^{k-a+2}$. For each orbit with $h<L$ and $\tau<2$ it suffices to take

```math
k\ge\max(a+1,\ a+L-h-2).
```

I independently maximized this bound over all sorted tuples of weight below *L*, discarding by position and order only after completing each tuple. For multiplicities $c_i$, I used $\nu_2(C)=\sum_i s_2(c_i)-s_2(d)$, where $s_2$ counts ones in binary. This reproduces every shell threshold in the table, including 23 from the 7,298,397 degree-15 candidates. Every other orbit has zero residue or lies beyond the shell. Thus $B\equiv M_d(t)\pmod{2^L}$ for every odd radix throughout the indicated shells. Since $\ell<L$ and $dk>\ell$ there, the reduced denominator is exactly $2^{dk-\ell}$. The common factor $b^n$ is odd.

As a check directly on positive indices, I repeated the ordered convolution with $v<\min(k,L)$ and letter weights $2^v b^{-2^{k-v}}\bmod 2^L$. For each degree the complete functions agreed for bases 3, 5 and 17 at its first sufficient shell, and for base 7 one shell later. For degree 4 the four consecutive weak residues modulo 512 are 256, 128, 384 and 256, beginning at 1, 3/2, 13/8 and 7/4. The middle two have the same order. For degree 15 all 26 maximal constant-order intervals agree with the published table, including its right-hand value 64 at 133/128. I also reran the source checker with `--audit`, including its early quartic and degree-15 tests. [Finite certificate and reproduction command](../../../scripts/phase14_dyadic_power_cells.py) · [Degree-15 interval table](../higher-degrees.md#complete-degree-fifteen-denominator-losses)

## The missing diagonal

In the box $1\le j_i\le k$, the largest insertion other than the all-*k* tuple is $(d-1/2)2^k$ for $k\ge2$. At cutoffs from there up to but excluding $d2^k$, the box omits only that tuple. Its frozen mass for even *d* is $(-1)^d-1=0$. Clearing the radix and the power of two gives $A_k^d-1$ up to an odd factor, with $A_k$ the cleared axis numerator. For $d=2r\ge2$, $k\ge2$, the square identity gives $\nu_2(A_k^2-1)=k+1$. Lifting the exponent yields $\nu_2(A_k^d-1)=k+1+\nu_2(r)=k+\nu_2(d)$. This proves the secondary order for every even box. [Kernel box identities](../../../NormalityChecker/DyadicMissingDiagonal.lean) · [Square identity](../../../NormalityChecker/ParameterTwoSquareArithmetic.lean)

The square realizes this box on its actual upper half-shell. For *d* ≥ 4 the fixed-box interval lies above the standard shell for *k*. For example, at *b* = 3, *d* = 4, *k* = 2 and *n* = 14, the box contributes 905/16. The true positive-index sum also contains the four permutations of $(3,1,1,1)$, adding 1/16. Its value is 453/8. The physical shell at 14 is 3, and extending the late quartic formula to that shell would incorrectly give denominator 16.

For a general fixed symmetric upper set, clipping at a depth containing all minimal generators preserves membership. Let *F* sum the products of clipped letters over the accepted words. Symmetry makes the derivative in letter *i* equal to *d* times the section mass $S_i$ at the frozen letters. If the frozen mass vanishes and the actual letters are $\lambda_i+2^k h_i$, expansion gives $F/2^k\equiv d\sum_i S_i h_i\pmod{2^k}$ for the actual value. The tail correction is odd and all short corrections are divisible by 4. Hence an odd tail section gives numerator order $k+\nu_2(d)$ once $k>\nu_2(d)$. The box identity above also handles the smaller $k\ge2$ for even degrees divisible by a large power of two.

There is one edge case in the separate estimate for an arbitrary fixed zero cut whose tail section and sum of short sections both vanish. For *d* = 1 the empty upper set satisfies both hypotheses. Its reduced denominator exponent is always 0, whereas $(d-2)k+O_m(1)$ tends to minus infinity. The stated upper bound holds for $d\ge2$. In all positive dimensions one can use $\max(0,(d-2)k+O_m(1))$ because a nonnegative numerator order beyond the clearing power leaves denominator 1. Every standard cut in the degree table is nonempty. [Secondary estimate](../higher-degrees.md#secondary-cancellation-for-an-arbitrary-fixed-zero-cut)

## From a leading pole to a polynomial

Clear all rational coefficients by one common denominator and call the resulting integer leading coefficient *A*. The leading pole at a late position has order at least $dk-(L-1)-\nu_2(A)$. Each lower-degree prefix has denominator dividing $2^{(d-1)k}$, including the constant term, which has integer prefix. Once $k>L-1+\nu_2(A)$ the leading pole survives their sum. In the formal criterion, reindexing each axis from zero to one identifies the degree-*d* model prefix with $2^d R_{d,n}$. This costs at most *d* more powers of two, a fixed loss allowed by the retention hypothesis. The retained-denominator normality theorem applies, and rational scaling recovers the original polynomial. This permits a quadratic lower term with any rational coefficients, regardless of what is known about that quadratic in isolation. The corresponding joint Weyl argument allows exponents 3 through 15 with either 1 or 2 adjoined. Adjoining both would also require controlling every projection supported on 1 and 2 alone. [Retained-denominator criterion](../../../NormalityChecker/StonehamPolynomialRetention.lean) · [Positive-index polynomial conversion](../../../NormalityChecker/DyadicQuartic.lean)

I re-elaborated the three new module sources at the reviewed commit with Lean 4.36.0 and ran `leanchecker` on the resulting modules. The quartic grid computation, the quartic polynomial theorem, the conditional polynomial theorem, the even-box order and the earlier odd prime-power theorem report only `propext`, `Classical.choice` and `Quot.sound` in their axiom dependencies. The internal zero-index quartic uses the axis $2\alpha$. On its grid every contributing deficit is at least one. Subtracting one from each gives the physical cut and removes a factor $2^4$ from the mass. The four internal residues modulo $2^{13}$ are therefore sixteen times the four physical residues modulo $2^9$. The formal retention proof uses $k\ge26$ for this grid. The sharper start $k=4$, the exact physical denominator profiles and the six new nonquartic degree certificates are established by the arithmetic above. [Kernel grid computation](../../../NormalityChecker/DyadicMassCells.lean) · [Kernel grid-to-normality implication](../../../NormalityChecker/DyadicQuartic.lean)
