# Removing full rectangles from the mixed-product discrepancy bound

Let $x=\alpha_{2,3}\alpha_{2,5}$, and let $R_n$ be its positive-index shifted rational prefix. Set $K=\lfloor\log_3 n\rfloor$, $L=\lfloor\log_5 n\rfloor$, $P=3^K$, $Q=5^L$. Let $F$ be the simultaneous first-precision failure set from the mixed-flow theorem. Let $E$ consist of $n\in F$ for which $n<P+Q$. Then
```math
D_N(x;2)\le \#(E\cap[0,N))/N+o(1).
```
An exact rational enclosure of the **ordinary upper density of $E$** is
```math
0.37047223953692 < \overline d(E) < 0.37047223953703 .
```
Consequently the upper binary interval discrepancy of the product is at most $0.37047223953703$. The lower endpoint bounds a failure count and gives no lower bound for the discrepancy. [Full first-precision failure density](mixed-flow.md) · [Deep failures on nonrectangular regions](mixed-interpolation.md)

## Why a failed full rectangle is usable

The condition $n\ge P+Q$ means that every pair from $1\le i\le K$, $1\le j\le L$ has entered $R_n$. The ternary pole supplied by the single-axis sum has order $K$. In its opposite factor $\sum_{j=1}^L5^{-j}2^{-5^j}$ the ternary loss is zero for odd $L$ and exactly $1+v_3(L/2)$ for positive even $L$. Thus throughout all sufficiently late full rectangles the denominator retains at least $K-1-\lfloor\log_3 L\rfloor$ ternary layers. This tends to infinity uniformly with $n$. The binary shift is a unit at 3. The estimate concerns the full reduced denominator even when the top ternary and quinary layers have both disappeared. [Rectangle valuation proof](../phase13/independent-axes.md#exact-loss-on-full-rectangles)

For a prefix of length $N$, use blocks of length $B=2^{\lfloor\log_4 N\rfloor}$. Discard the first and unfinished blocks, and those meeting an insertion. Their total length is $O(B(1+\log N)^2)=o(N)$. On every other block the prefix follows a rational doubling orbit, its denominator stays fixed and divides $3^K5^L\le N^2$, and the real tail tends uniformly to zero. If any sample in the block is outside $E$, either one first-precision test passes, or the sample belongs to a full rectangle. In both cases the common reduced denominator grows uniformly. The fixed-support short-orbit estimate and a finite mesh of interval endpoints give uniformity on these blocks. Every remaining block is contained in $E$. Summing centered interval counts gives the displayed assertion, including when an endpoint of a good region falls within the last shell. [Original coverage argument](../../NormalityChecker/ProductThreeFiveCoverage.lean) · [Fixed-support estimate](../../NormalityChecker/SmoothOrbit.lean)

## Finite enclosure of the ordinary upper density

Use the same normalized ternary, quinary and cutoff scales as in the [coupled phase-flow proof](mixed-flow.md). The row powers are $3^i$, the column powers $r5^j$ with $1\le r\le25$, and the ordinary cutoff varies over $1\le T\le81$. At a **fixed** phase the additional condition for a pair of active powers $p=3^i$, $q=r5^j$ selects the half-open interval
```math
[\max(p,q),\ \min(3p,5q,p+q)).
```
This follows from $p\le x<3p$, $q\le x<5q$, $x<p+q$. Intersect the union of these intervals with the two failed-band families. The normalized covered length divided by $T$ gives the limiting subsequence score. Away from a discarded interval $[0,\tau)$, both active powers are bounded below, and the added test has finitely many moving endpoints. The difference in its length tends to zero under a small phase displacement. Letting $\tau$ tend to zero gives continuity for the unrestricted score as in the original proof. The dense phase subsequences approach every allowable pair $(r,T)$. Omitting finitely many initial exponent indices and rounding cutoffs has zero limiting cost. Therefore maximizing the score gives the ordinary upper density.

For an outer phase bracket $l\le r\le u$, replace $q$ by $q_{\rm lo}=l5^j$ at the left endpoint and $q_{\rm hi}=u5^j$ at both appearances on the right. Include $[0,\max(p_{\min},q_{{\rm hi},\min}))$ to cover points where an active power is below the retained grid. For a lower bound use one fixed phase and omit unresolved intervals. The other two failure covers and the ordinary-cutoff maximization are shared with the original checker. The final coverage ratio can attain its supremum among the right edges of covered intervals and the cutoff endpoints.

At truncation depth 12, the point $r=25/2,T=11/2$ supplies the lower certificate. The upper certificate comprises 1,117 rational phase brackets. It bounds every phase, independently of whether the witness is an exact optimizer. Direct integer cell comparisons were also made through position 531,440, with the isolated shell boundaries treated separately as in the original proof. Run `python3 -B scripts/phase14_nonrectangular.py` to reproduce both fraction comparisons. [Certificate](../../scripts/phase14_nonrectangular.py) · [Phase bracketing and cutoff maximization](../../scripts/phase14_mixed_flow.py)

The bound uses the written valuation and finite rational enclosure. The original first-precision code and the certificate for its ordinary upper density are preserved. A one-missing-corner witness shows that, at every fixed pair of depths, simultaneous failures on nonrectangles can have ordinary upper density at least $4/11$. This leaves a genuine distinction between fixed-depth failure density, loss comparable to the entire shell exponent, and discrepancy of the real number.
