# Independent audit: Phase 17 → Phase 18 transfer note

Target: `notes/phase18/phase17-transfer.md`, uncommitted in the Phase 18 parent worktree (head `95f369f`). It was read twice; the second read includes the "Exact finite control" paragraph, the Erdős–Borwein paragraph and the recognition-obstruction paragraph. Comparison base: Phase 17 at `17e5770` (`notes/phase17/classical-approximants.md` §§3–6, `multiplicative-lambert.md` §5, `mixed-product-orbits.md` D3 and the `liminf` paragraph, `limitations-and-undecidability.md`). Also read: Phase 18 `translations.md` (sharp translation), `algebra.md` E3, and the Lean modules `SharpTranslation.lean`, `ComputableNormalityUndecidability.lean` and `Phase17DiscrepancyBounds.lean` (statements only; I did not run `lake build`). The independent exact computation is in [phase17-transfer-check.py](phase17-transfer-check.py). It uses exact rationals throughout and needs `sympy` only for the period comparison.

## Verdict

Every mathematical statement in the note that I checked is **correct as stated**. I found no false inequality, sign error or quantifier error. There are three substantive objections, all about presentation and scope:

1. **(Main) The π "linear shadowing window" carries no digit information.** The note should import the Phase 17 circularity verdict explicitly instead of the softer "can coincide".
2. The recognition-obstruction paragraph calls its input "already kernel-verified". The Lean reduction takes the endpoint properties as hypotheses, and its composition with the sharp translation theorem is a paper deduction.
3. The Erdős–Borwein paragraph credits the strict bound $D^+(E)<1$ to the wrong source and leaves its proof route ambiguous.

The remaining notes are wording nits.

## A. All-shift π-free even-Legendre odd-grid construction

### Line-by-line verification (all pass)

| Step | Check | Result |
| --- | --- | --- |
| $H_D(y)=P_{2D}(\sqrt y)$ has degree $D$; $h_{i,D}=P_{2D}(ia_i)$ is real and nonzero | $P_{2D}$ is even with real coefficients, and its zeros lie in $(-1,1)$ | ✓ |
| Quotients $(H_D(y)-h_{i,D})/(y+a_i^2)$ are polynomials of degree $D-1$ | Factor theorem | ✓ |
| Identity $\pi+\int_0^1R_D(x^2)\,dx=\sum_i\frac{c_ia_i}{h_{i,D}}\int_0^1\frac{P_{2D}(x)}{x^2+a_i^2}dx$ | Expand: $\int_0^1\frac{H_D(x^2)-h}{x^2+a^2}=\int\frac{P_{2D}}{x^2+a^2}-\frac{h}{a}\arctan\frac1a$; multiply by $c_ia_i/h$ and sum | ✓ |
| Laplace form $\lvert P_{2D}(ia)\rvert=\pi^{-1}\int_0^\pi(a+\sqrt{a^2+1}\cos\theta)^{2D}d\theta$ | $\sqrt{z^2-1}=i\sqrt{a^2+1}$ at $z=ia$, giving the factor $i^{2D}=(-1)^D$. The integrand is a nonnegative even power. Continuation to complex $z$ is valid because only even powers of $\sqrt{z^2-1}$ survive. | ✓ |
| Growth: $\lvert h\rvert^{1/(2D)}\to\rho_a$, with upper bound $\rho_a^{2D}$ | The maximum $\rho_a$ is at $\theta=0$; the value at $\theta=\pi$ is $\rho_a^{-1}$. An interval near $0$ gives the lower bound. | ✓ |
| First crossing: $D/n\to 1/(2\log_2\rho)$ | Apply the two-sided asymptotics at $D$ and $D-1$. $D(n)$ is nondecreasing and tends to infinity. | ✓ |
| Poisson/Chebyshev expansion of $1/(x^2+a^2)$ with $r=\rho_a^{-2}$ | $x^2+a^2=(b+\cos2\theta)/2$ with $b=2a^2+1$. The Poisson kernel at $-r$ gives $1/(b+\cos\phi)=\frac{2r}{1-r^2}(1+2\sum(-r)^j\cos j\phi)$ when $r+r^{-1}=2b$. Then $r=b-\sqrt{b^2-1}=(\sqrt{a^2+1}-a)^2=\rho_a^{-2}$. | ✓ |
| Orthogonality on $[0,1]$ | The truncation has even degree $\le2D-2$. It is orthogonal to $P_{2D}$ on $[-1,1]$, and by evenness the integral over $[0,1]$ is half of that, hence zero. The tail is $\le\frac{4r}{1-r^2}\cdot\frac{2r^D}{1-r}$, and $\lvert P_{2D}\rvert\le1$ on $[0,1]$. | ✓ |
| Error $\lvert2^n\pi-Y_n\rvert\le\frac1{2L_D}+C\rho^{-2D}$ with $C=\sum\lvert c_i\rvert a_iC_{a_i}$ | Uses $2^n/\lvert h_{i,D}\rvert\le1$ and $\rho_{a_i}\ge\rho$ | ✓ |
| $q_n\mid L_D$, $L_D$ odd, $\log L_D=2D+o(D)$ | The odd lcm equals $\mathrm{lcm}(1,\dots,2D-1)$ divided by its 2-part, since odd prime powers $\le 2D-1$ are themselves odd entries. Then apply the PNT. | ✓ |
| Grid claim: $\gcd_j L_D/(2j+1)=1$ | Take $2j+1$ equal to the largest power of $p$ that is $\le2D-1$ | ✓ |
| Both limits | $\log q_n\le 2D(1+o(1))=\frac{n\log2}{\log\rho}(1+o(1))$. Also $\log\rho>1$ for $a_*\ge2$ (here $\log(2+\sqrt5)=1.4436$), so the grid term dominates and $-\log_2\text{err}\ge\log_2L_D-O(1)=\frac{n}{\log\rho}(1+o(1))$. | ✓ |
| Doubling window | The error after $k$ doublings is $\le2^{k-T}$. For $k\le(\tau-\epsilon)n$ this is $2^{-\epsilon n+o(n)}$, exponentially small (better than the stated $o(1)$). | ✓ |
| Window–denominator barrier transfer | $\lvert x-A/(2^nq)\rvert\le2^{-T-n}$ and $\lvert x-p/Q\rvert\ge cQ^{-\mu}$ with $Q\le2^nq$ give $T\le(\mu-1)n+\mu\log_2q+O(1)$. For π, $\mu(\pi)\le7.103$ (Zeilberger–Zudilin) is finite. | ✓ |
| Nearest-grid identification | $L_D(-2^n\int R)$ differs from $L_D2^n\pi$ by $\le CL_D\rho^{-2D}\to0$, so the rounding agrees away from half-integers. This is the analogue of Phase 17 Proposition 4. | ✓ |

### Independent exact computation

[phase17-transfer-check.py](phase17-transfer-check.py) is written from the note's algorithm only, without consulting `scripts/phase18_classical.py`. It uses exact `Fraction` arithmetic for $H_D$, synthetic division, the moments and the rounding. The reference value of π is computed separately, by an integer Machin series with 40 guard bits.

| identity | $n$ | $D$ | $\log_2L_D$ (bits) | reduced $q_n$ (bits) | $\log_2\lvert2^n\pi-Y_n\rvert$ | analytic part $\log_2\lvert2^n(\pi+\int R)\rvert$ | equals $\mathrm{round}(L_D2^n\pi)/L_D$? |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | --- |
| Machin $(16,5),(-4,239)$ | 600 | **91** | 260 | **257** | **−261.1** | −612.0 | yes |
| Størmer $(24,8),(8,57),(4,239)$ | 600 | **76** | 212 | **212** | **−213.4** | −615.5 | yes |
| Euler $(4,2),(4,3)$, $a_*=2$ | 600 | 146 | 416 | 404 | −416.8 | −614.7 | yes |

This reproduces the note's finite claims exactly: Machin gives $D=91$, a 257-bit denominator and error $\le2^{-261}$; Størmer gives $D=76$, a 212-bit denominator and error $\le2^{-213}$. Over $n=1,\dots,300$, for all three identities:

* $L_DY_n$ equals the nearest integer to $L_D2^n\pi$ in **300 of 300** cases.
* $-\log_2\text{err}-\log_2L_D\ge1.04$, so the error is always at the grid floor $\approx1/(2L_D)$.

The Legendre analytic remainder is about $2^{-n}$, roughly 350 bits finer than the grid at $n=600$. The grid discards that extra precision.

### Objection A1 (main): the window is the trivial rounding window and carries no digit information

The note's own "Where distribution enters" paragraph shows that $Y_n$ is, generically, **exactly** $\mathrm{round}(L_D2^n\pi)/L_D$; the computation above confirms this on every row. So:

* **Nothing beyond trivial rounding.** Round any rational approximation of $2^n\pi$ to the grid $\frac1M\mathbb Z$, for any odd $M$ computable from $n$: an odd denominator dividing $M$ and a window $\log_2M-O(1)$ follow by Theorem 5 of Phase 17. The approximation can be computed π-free, for example from a truncated Machin series in rational arithmetic. Choosing $M=3^{\lceil\kappa n\rceil}$ gives *any* linear window slope at the same 1:1 trade between window bits and $\log_2 q$. The even-Legendre kernel adds only an explicit integral representation and the fact that the scalar remainder lies below the grid. "π-free" describes the algorithm, not the number it outputs. Phase 17 makes exactly this point for $\ln2$ (Corollary "circularity" in §4: "The numerator carries no arithmetic beyond the digits of $\ln2$ themselves").
* **The grid structure is generic.** The sentence "Every point of this grid is a moment of an integer polynomial in $x^2$…" holds for every point of $\frac1{L_D}\mathbb Z$, by the gcd fact. The integer polynomial is not tied to $R_D$; none is constructed, in contrast to Phase 17's Bezout $Q$. Calling this "the odd-denominator form of the correlated rounding" is fair only in that weak sense.
* **Digit consequence.** Digits $n+1,\dots,n+T-O(1)$ of π equal the leading digits of $Y_n$, up to carry runs. That is a restatement of a $T$-bit approximation of π. It gives no frequency or periodicity information, because the window is a vanishing fraction of a single period of $Y_n$. Exactly: for Machin at $n=600$ the window is about 261 doublings, while $\mathrm{ord}_{q_n}(2)\approx2^{73.0}$. For Euler at $n=600$ it is about 417 against $2^{106.5}$; for Machin at $n=100$, about 44 against $2^{14.8}$. In general $\mathrm{ord}_{q}(2)\ge\log_2q$, and for $q_n$ near $L_D$ the order is superpolynomial in $D$.
* **Smaller poles are not an improvement.** The ratio of window bits to $\log_2q_n$ is $\ge1-o(1)$ for every identity. Increasing $a_*$ lowers the denominator rate and the window slope by the same factor $1/\log\rho$. The sentence "The small-rate assertion is across fixed identities…" should say that the trade is exactly 1:1, so a small rate buys nothing.

**Requested change.** Replace the bolded "**linear shadowing windows**" framing in the opening paragraph with an explicit statement:

> The output is generically the nearest point of $\frac1{L_D}\mathbb Z$ to $2^n\pi$. Any odd grid gives the same window-to-denominator trade, and the window covers a vanishing fraction of one period of $Y_n$. The result therefore has no consequence for the digits of π (compare the Phase 17 circularity corollary).

Then add the exceptional-set remark from Phase 17 Proposition 4. The rounding agrees with the nearest grid point unless $L_D2^n\pi$ lies within $CL_D\rho^{-2D}$ of a half-integer, and $CL_D\rho^{-2D}$ is exponentially small.

### Nits for §A

* "For Machin choose $a_*=5$, and for Størmer choose $a_*=8$": $a_*$ is determined by the identity, not chosen. Name the identities explicitly. Størmer's is $\pi=24\arctan\frac18+8\arctan\frac1{57}+4\arctan\frac1{239}$; his other formula, with poles 57, 239, 682, 12943, has $a_*=57$.
* The slopes are worth stating: Machin $1/\log(5+\sqrt{26})=0.4324$, Størmer $1/\log(8+\sqrt{65})=0.3602$, and the best possible $a_*=2$ (Euler/Hutton) gives $0.6929$.
* "For **each** sufficiently large $n$": the algorithm runs for every $n\ge1$; only the limits are asymptotic.
* "This avoids any assumption about the monotonicity of a rounding operation" is unclear. Delete it, or say that the minimal crossing $D(n)$ is nondecreasing in $n$ but no monotonicity of $\lvert h_{i,D}\rvert$ in $D$ is used.
* "Along a subsequence with $\log q\gg n$": say "$\log q\ge cn$". The conclusion is $T=O(\log q)<q^\eta$, and it needs that hypothesis because with $\log q=o(n)$ the bound $(\mu-1)n$ can exceed $q^\eta$.
* "$o(1)$ circle error": it is in fact $2^{-\epsilon n+o(n)}$.

## B. Sharp Lambert translation rate

| Claim | Source | Result |
| --- | --- | --- |
| $\max_x\lvert D_N(x+z)-D_N(x)\rvert=1-D_N(z)$, attained at $x=0$, for all $N>0$ | `SharpTranslation.lean`: `sharp_translation`, `sharp_translation_zero`, `sharp_translation_isGreatest`. `radixDiscrepancy 2` is definitionally `binaryDiscrepancy` over half-open subintervals of $[0,1]$, matching the Phase 17 normalization in `multiplicative-lambert.md` §1. The file contains no `sorry`. | ✓ (maximum, not just supremum) |
| $1-D_N(L_f)\asymp\frac{\log\log N}{(\log N)^{1-\delta}}$ | Phase 17 `multiplicative-lambert.md` (10), with $\kappa=1-\delta$ and both directions (9) and the matching lower bound | ✓ |
| Every $\delta\in(0,1)$ is admissible | Phase 17 §1, "The harmonic hypothesis also permits every real δ" | ✓ |
| Preservation of $\liminf$ and $\limsup$ of $D_N$ for every input; cubic example: error at most the sum of the two rates | Triangle inequality and uniformity in $x$ | ✓ |

Nits:

* The implied constants also depend on $c$ and $p_0$. Phase 17 lists $c,S,q_0,p_0,\delta$, so write $\asymp_{c,S,q_0,p_0,\delta}$.
* "Sparse word occurrences … would give no such rate": state the comparison precisely. One-frequency zero alone gives $D_N\to1$ with no rate. Disjunctivity alone gives no translation invariance, since normal numbers are disjunctive.

**Erdős–Borwein paragraph (Objection B1).** The weak-limit argument is correct. By the fixed-point classification in `translations.md`, $D_N(L_f)\to1$ forces mean circle displacement $\to0$. Then for Lipschitz test functions the two empirical averages differ by at most $\mathrm{Lip}(g)$ times that mean. Two problems remain:

1. "This transfers the strict upper discrepancy conclusion for $E$". The input $D^+(E)<1$ does **not** come from Phase 17, whose Erdős–Borwein note is about certifying statistics. It is the external Mira Cult word-density theorem (audited in Phase 13, implication via Phase 15; see `notes/phase18/sources.md` and `classical.md`). Cite that source and its audit status, not "Phase 17 Erdős–Borwein tests".
2. The transfer of $D^+$ follows **directly** from the sharp theorem: $D^+(E+L_f)=D^+(E)$. Weak convergence alone would not give it, because discrepancy is not weak-* continuous where there are atoms. Make clear that the sharp theorem is the route; weak convergence handles only the measure statement.

## C. Mixed product, synthetic product, undecidability, echelon degrees

* **$Z=\alpha(2,3)\alpha(2,5)$** ✓. Phase 17 D3 proves $D^+(Z)\le4/11\iff C_0\le4/11$, and the D4 paragraph proves $\liminf D_N(Z)=0$. With the sharp maximum, $\liminf_N\max_x\lvert\Delta\rvert=1-D^+(Z)$ and $\limsup_N\max_x\lvert\Delta\rvert=1-\liminf D_N(Z)=1$. Both stated conclusions follow. *Optional strengthening:* Phase 17 also gives $D^+(Z)=C_0$ whenever either exceeds $4/11$. So in that case the lower limit of the worst change is exactly $1-C_0$.
* **Synthetic $XY'$** ✓. `algebra.md` E3 has $Y'=aY+(1-a)b^{-m_1}$, so $XY=a^{-1}XY'-a^{-1}(1-a)b^{-m_1}X$. The removed term is a nonzero rational multiple of the normal $X$, hence normal. A normal $t$ is never a universal normality preserver: take $x=-t$, which is normal, and $x+t=0$. By the sharp theorem it is not even a discrepancy preserver, since $D_N(t)\to0\ne1$. The conclusion is correctly limited ("cannot be removed using …"). It says nothing about normality of $XY$ itself, and the note does not claim otherwise.
* **Undecidability** ✓ as a description of Phase 17.
* **Echelon lemma** ✓. `jointUniform_of_echelon_degrees` needs normality of every nonzero integer polynomial whose degree lies in the echelon degree set. The "Phase 18 supplies that input…" sentence points to `algebra.md` (factorial schedule: every nonconstant rational polynomial). I did not re-audit that Phase 18 result; it is outside this brief.

**Objection C1: the recognition-obstruction paragraph.** The logic is correct. On the promise ($D_N\to0$ or $D_N\to1$), translation-preservation, even pointwise at $x=0$, is equivalent to $D_N\to1$ by the sharp maximum and attainment. That is the complement of normality. A recognizer or corecognizer would then contradict `no_re_nonnormality_recognizer_on_names` or `no_re_normality_recognizer_on_names`. The scope wording is inaccurate in two places:

1. Those Lean theorems take as **explicit hypotheses** the existence of a computable transcendental normal endpoint and a computable transcendental endpoint with $D_N\to1$. Phase 17 (`limitations-and-undecidability.md`, lines 89 and 101) states that unconditional instantiation (Mahler for $C_2$, Liouville for $L_2$, or the elementary Liouville–normal substitute) is a paper proof. It says that "An unconditional endpoint instantiation requires formal proofs of these inputs".
2. The composition (sharp translation + reduction) is not in Lean.

Replace "already kernel-verified" with: "the kernel-verified reduction, whose endpoint hypotheses are discharged by the paper proofs in Phase 17; the composition with the sharp theorem is a paper deduction".

## Summary of requested edits

1. §A: state the circularity and identification with the nearest grid point explicitly, and drop or qualify the bolded "linear shadowing windows" as a consequence for π's digits (A1).
2. Recognition paragraph: give the correct scope of the Lean evidence (C1).
3. Erdős–Borwein paragraph: cite the correct source for $D^+(E)<1$ and route the transfer through the sharp theorem (B1).
4. Nits: the $a_*$ wording, the slope values, "each sufficiently large", "$\log q\gg n$", the subscripts on the constants, and the optional $1-C_0$ strengthening.

No mathematical error was found in the inequalities, constants or quantifiers. The finite claims at $n=600$ reproduce exactly from an independent implementation.
