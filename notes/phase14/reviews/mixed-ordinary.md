# Review of ordinary joint failure density for the mixed Stoneham product

For the binary shifts of $x=\alpha(2,3)\alpha(2,5)$, let $F(N)$ count positions below $N$ where both first-precision denominator tests fail, and put $\rho=\limsup_N F(N)/N$. An independent exact calculation confirms the enclosure in commit `4a5dd43`.

$$
0.575523806608492 < \rho < 0.575523806608494.
$$

For the actual product, the consequence is the one-sided bound $\limsup_N D_N(x)\le\rho$ on extreme interval discrepancy. The lower endpoint applies to the count of joint failures. A failed test allows the corresponding orbit segment to make a smaller discrepancy contribution. The proof also leaves open whether the exhibited phase attains the maximum. [Reviewed proof](../mixed-flow.md) · [Uniform discrepancy transfer](../../../NormalityChecker/ProductThreeFiveCoverage.lean)

## Logarithmic coordinates and forward breakpoints

Write $A=81^k$, $Ar=25^\ell$ and $y=Az$. Then $\log_3 y=4k+\log_3 z$ and $\log_5 y=2\ell+\log_5(z/r)$. On a normalized row starting at $p=3^i$, the physical offset has logarithm $2\ell+\log_5((z-p)/r)$. On a normalized column starting at $rq$ with $q=5^j$, its logarithm is $4k+\log_3(z-rq)$. The two integer shifts preserve the respective residues modulo two and four. Thus a row fails for $r25^m\le z-p<5r25^m$ before $3p$, and a column fails for $81^h\le z-rq<3\cdot81^h$ before $5rq$, with all indices integral.

Every change comes from a shell boundary or an opposite power added to the current shell start. Advancing to the next shell clips the old bands even when the other axis stays in its shell. At a tie, both updates take effect on the cell to the right. For example, the cell starting at $106=81+25$ already has the two updated counts. Away from a shell start, physical offsets on an integer cell are at least one and all relevant thresholds are integers. At a shell start the discrete empty count charges that axis, and the continuous charge is at most one. Including the initial cell, the total prefix error is $O(1+\log N)$.

For $T=N/A$, the ordinary integral is normalized length on $[0,T)$ divided by $T$. For each fixed $r$, the shell boundaries and translated powers form a countable set. At any other positive $z$ both shell indices and both offset tests are locally constant under a small change of $r$. Dominated convergence on $[0,81]$, also excluding the single point $T$, gives joint continuity of the normalized integral $M(r,T)$. The forward phases $r=25^{\lceil k\log_{25}81\rceil}/81^k$ approach every point of $[1,25]$ along arbitrarily late indices by irrationality of $\log_{25}81$. On each chosen scale, $\min(81A-1,\lfloor AT\rfloor)/A$ approaches the specified $T$, including $T=81$. This proves $\rho=\max M$ on the entire closed rectangle.

## Independent rational certificate

In the original depth-$d$ enclosure, omitted shells lie below $81^{-d}$ on the row axis or $b25^{-d}$ on the column axis. Within a retained shell, an omitted offset lies within the other axis's cutoff of its start. There are $4d+5$ retained rows and $2d+4$ retained columns. Adding these strips and both initial shells gives the stated uniform error, using $b\le25$ and $T\ge1$. For a retained pair the lower endpoint is the larger of the two starts. The upper endpoint is the least of the two band ends, the two shell ends, and $T$. Cutting along all pairwise equalities includes each change of active endpoint and every crossing where a piece first acquires positive length. The resulting polygonal cells have rational vertices and an affine length numerator, so a maximum of the ratio occurs at a vertex.

The verifier bounds failures from above by removing intervals on which one test passes for **every** phase $a\le r\le b$. The following half-open intervals are protected. An endpoint order giving an empty interval contributes zero.

| Passing axis | Powers | Left endpoint | Right endpoint |
| --- | --- | --- | --- |
| Row | $p=3^i,\ q=25^m$ | $p+5bq$ | $\min(3p,p+25aq)$ |
| Column | $q=5^j,\ p=81^h$ | $bq+3p$ | $\min(5aq,aq+81p)$ |

For example, the column interval stays inside the actual column and its offset lies in $[3p,81p)$, covering the three consecutive passing residues. Omitting any protected interval makes the upper bound conservative. At a single witness phase the verifier instead retains failure intervals and counts the length with two active intervals. Each axis has disjoint failure intervals there, so the count gives a lower bound.

The sweep starts at zero and carries the full accumulated length into $T=1$. It tests every distinct endpoint, inserts both cutoff limits, and clips at $81$. Between consecutive events covered length is affine and its ratio to $T>0$ is monotone or constant. Simultaneous events have one common coordinate. Integer arithmetic with a common denominator makes every endpoint and comparison exact.

The calculation retained ternary powers from exponent $-48$ and quinary powers from $-30$. At $r=1250/81$ the inner maximum occurs at $T=493/81=r/5+3$ and exceeds $0.57552380660849217$. This cutoff ends a row band with start $3+r/25$ and a column band with start $r/5+1$. Trisecting the phase interval until each bracket passed gave 1,591 terminal brackets covering $[1,25]$. The largest upper bound was below $0.57552380660849399$. The original calculation, which encloses failing intervals on both axes, also reproduced its stated 1,304 terminal brackets. Both scripts print their exact rational bounds. [Independent verifier](check_mixed_ordinary.py) · [Original certificate](../../../scripts/phase14_mixed_flow.py)

## Finite cutoffs and the Lean conclusion

Put $H=81^5=3486784401$. For any $N\ge H$, choose $B=81^k$ with $HB\le N<81HB$ and a power $25^\ell=rB$ with $1\le r\le25$. The independent finite check uses the same passing intervals with nonnegative exponents. It rounds their left endpoints up and right endpoints down in units of $B$. After multiplication by the integer $B$, the length of each complete protected window equals its count of integer positions. For an integer cutoff inside a window the clipped length also equals the count. Sweeping the complement from zero and testing the endpoints, $H$ and $81H$ in scaled coordinates bounds **every** cutoff, including the first admissible one and the final gap. Across 395 phase brackets the largest certified upper bound was $12213793247/21222039871<143881/250000$.

I re-elaborated the reviewed module with Lean 4.36.0 and counted 660 leaves in its finite cover proof. The declaration `joint_cost_bound` gives $250000F(N)\le143881N$ for every $N\ge H$. The declaration `mixed_product_discrepancy` names `StonehamStatements.stoneham 2 3 * StonehamStatements.stoneham 2 5` and bounds its binary asymptotic discrepancy by $143881/250000$. Both declarations report only `propext`, `Classical.choice` and `Quot.sound` under `#print axioms`. The finer decimal enclosure is a paper deduction supported by the rational computation. [Lean declarations and window proof](../../../NormalityChecker/ProductThreeFiveOrdinary.lean) · [Discrepancy definition](../../../NormalityChecker/BinaryDiscrepancy.lean)

Run `python3 notes/phase14/reviews/check_mixed_ordinary.py` from the repository root to reproduce the independent bounds.
