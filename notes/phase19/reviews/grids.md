# Independent review of the Phase 19 all-prime grid construction

Review of `notes/phase19/grids.md`, `scripts/phase19_grids.py` and `NormalityChecker/SurvivingGrid.lean` at Track C commit `1d0c1dd` (branch `t3/exact-crt-grid-normality`, on top of `b96bcbd`). Read on 25 November 2026. The reviewed files were not edited. The reviewer derived each claim separately before comparing it with the draft, and ran exact controls that the draft does not contain.

**Verdict.** No mathematical error was found in the draft or in the Phase 18 statements it touches. Every claim in the audit scope survives: the exact stride order, the real versus CRT grid discrepancy, the binary $O(1/\log N)$ rate for every prefix, the Liouville property, the unbounded limsup of $G(L)/L$ beside the lower bound $G(L)>L/9$, the thresholds for general radices and depth profiles, the Ford–Luca–Pomerance step, and the accelerated exponents. There are two points to fix before integration (R1, R2) and four optional clarifications. Nothing blocks the Track C claim of scope.

## Scope and evidence classes

| Claim | Status here |
|---|---|
| Exact stride order, lifts of a residue class | Hand proof (below) and kernel text read; Lean build **not** re-run (see R2) |
| CRT classes, full-period discrepancy $\le 1/G$ | Hand proof and random exact controls |
| All-prefix bound $D_N(Y;2)\ll 1/\log(2N)$ | Hand derivation from the prefix estimate |
| Prefix estimate | Hand proof and 228 exact random runs with no violation |
| Liouville property | Hand proof |
| $G(L)>L/9$, $\limsup G(L)/L=\infty$ | Hand proof, brute-force orbit check for $L\le19$, formula check to $L=3^{14}$ |
| General radices, depth profiles, schedules | Hand derivation of each exponent |
| Sieve step | Statement of the cited lemma read in the paper |
| Maximal-denominator construction | Hand proof and exact order checks, five $(b,p)$ pairs, $j\le8$ |

## 1. Stride order and the real versus CRT discrepancy

Derived independently. Let $q=p^eQ$ with $p$ odd, $g=b^t$ and $t=\operatorname{lcm}(\operatorname{ord}_pb,\operatorname{ord}_Qb)$. Then $g\equiv1\bmod pQ$, so $v_p(g^k-1)=w+v_p(k)$ by odd-prime lifting, and $g^k\equiv1\bmod q$ iff $p^{\max(0,e-w)}\mid k$. Any return of $b$ fixes $p$ and $Q$, so it is a multiple of $t$. The period is $tG$, and the class of $Ab^i$ is the subgroup of lifts of $1$ translated, namely $x\equiv Ab^i\bmod q/G$, because $g$ has exact order $G$ in a group of exactly $G$ lifts. Each class is an equally spaced grid of $G$ points on the circle. A half-open arc contains $\lfloor G|I|\rfloor$ or $\lceil G|I|\rceil$ of them. Hence the union of $t$ classes has discrepancy strictly below $1/G$. The Lean statements `return_iff` and `stride_order` match this derivation, including the truncated subtraction when $e\le w$.

The *real* discrepancy of the shifted point $2^nY$ differs from the rational model by the tail $\le Bb^{-H}/(b-1)$, which costs $2Bb^{-H}/(b-1)$ after expanding the arc. The draft's accounting of this is correct, and so is the count of discarded buffer shifts.

Controls run (exact integers, Python):

- **Stabilizer test.** For 1,683 random pairs $(b,q)$ with $b\in\{2,3,4,5,6,7,10,11,12,26\}$ and $3\le q\le4000$, $\gcd(b,q)=1$ (even $q$ included), the set of $h\mid q$ for which the orbit is invariant under $x\mapsto x+q/h$ was computed by brute force. The order-ratio test $P=h\operatorname{ord}_{q/h}b$ agreed with it in every case, the set of $h$ was always the set of divisors of its maximum, and the odd part of the maximum equalled $\prod_{p\mid q,\,p\ \mathrm{odd}}G_p$. The identity $w=a+v_p(\operatorname{ord}_Qb)$ held in every case. This confirms the "Combining primes" paragraph, including the even-$q$ remark.
- **Counting inequality.** For 228 random runs (random $b,q$, unit start $A$, run length up to $3P+5$) the exact worst arc error (computed over all closed and open-left arcs between support points) never exceeded $h/G+\min\{r,(1+1/G)(P-r)\}$, where $G$ is the largest single-prime grid.
- **Brute force against the formula for $G(L)$.** For $3\le L\le19$ the actual prefix denominator $q(L)=3^{2J_3}\prod_{\ell>3}\ell^{J_\ell}$ was built, the orbit of $2$ computed, and the largest 3-power equally spaced subset found by testing invariance. It matched $3^{\max(0,2J-1-M(L))}$ for all $L$, including the drop at $L=19$ where $\operatorname{ord}_{19}2=18=2\cdot3^2$ forces $G=3$.

## 2. The binary series and the rate

Derived independently from the prefix estimate. At shift $n$ with $L=\lfloor\log_{16}n\rfloor$ every odd-prime-power label $u\le L$ has inserted, so $v_\ell(R_n)=-s_\ell J_\ell$ exactly (earlier terms on an axis have shallower poles, other axes are $\ell$-integral, $2^{n-m}$ is an $\ell$-unit). The bound $M(L)\le J$ follows from $\ell-1<L<3^{J+1}$, and with $a=1$ this gives $G\ge3^{J-1}>L/9$. After discarding $n<\sqrt N$ one has $L\ge\frac12\log_{16}N-1$, so the mesh is $O(1/\log N)$. There are $O(\log N)$ runs, each with period at most $q(L)\le N^{1/\log16+o(1)}$, and $O(\log^2N)$ buffer shifts. All three costs are $O(N/\log N)$. The prefix estimate for every $N\ge2$ follows.

The finite certificate was re-derived by hand: the events $(3,3,2),(5,5,1),(7,7,1),(9,3,4),(11,11,1)$ are exactly the odd prime powers up to $11$; labels $4,6,8,10$ are not labels; the guard sum counts $[16^u-H,16^u)\cap[\sqrt N,N)$; and the dominant term is the last run with $G=9$. The script's four bounds were reproduced by running it.

## 3. Liouville property

Correct. The CRT step produces $z$ with every $z+i$ ($1\le i\le h$) having two distinct prime factors, hence not a prime power, so the gap between consecutive labels exceeds $h$. (The shorter route $(h+1)!+i=i\bigl((h+1)!/i+1\bigr)$ with two coprime factors also works.) The truncation at $16^u$ has denominator at most $2^{16^u}q(u)$ with $\log_2q(u)=O(u)=o(16^u)$, and error below $2^{1-16^v}$, giving exponent about $16^{v-u}$. Irrationality follows from normality.

## 4. Why $G(L)/L$ is unbounded, and why it stays above $1/9$

Correct. The lemma that $mp^k+1$, $1\le m\le C$, are all composite along an arithmetic progression of $k$ was re-derived: with $r_m\mid p^h+m$, $r_m\ne p$, one has $p^h\equiv-m$ and $p^{k+h}\equiv1\bmod r_m$, so $mp^k\equiv-1$. The step $L=3^{k+j}$, $C=3^j$ gives $M(L)\le k-1$ and $G(L)/L\ge3^j$.

Numerical corroboration (all primes up to $3^{14}$, exact orders):

- $\min_L 9G(L)/L=1.0041$, attained near $L=726$, so the constant $1/9$ is sharp to within $0.5\%$ for $L\le3^{14}$.
- $G(3^J)/3^J$ equals $1,1,3,1,1,3,9,3,3,9,3,9,27$ for $J=2,\dots,14$. At $J=14$, $M=10<12$, so the ratio is $27\ge3$ as the lemma requires.
- Heuristically $M(L)\approx J-\log_3\log L$, which suggests $G(L)\approx L\log L$ for typical $L$. This is a heuristic only. The draft's upper bound $G\ll L^2/\log L$ was re-derived and is correct, and the claim "no linear upper bound" needs nothing more.

The Phase 18 review's statement that no prime-5 grid survives is not established by Dirichlet's theorem alone, because $\ell\equiv1\bmod5^k$ does not force $5^k\mid\operatorname{ord}_\ell2$ and depth grows too. The draft's criticism is accurate. The draft's own conclusion is also correctly weak: along $L=5^{k+j}$ the grid is large, and nothing is claimed for other $L$.

## 5. Radices, depth profiles, schedules, exponents

- **Threshold.** $G\ge U$ iff $E_p(J_p)\ge a+M_b(L)+\lceil\log_pU\rceil$ (for $U>1$), by the exact formula. The worst $L$ in a layer is $p^{j+1}-1$ for nondecreasing $U$. Since $M_b\le J_p$ for every support, $E_p(j)=sj$, $s\ge2$, gives $G\ge p^{-a-s+1}L^{s-1}$ uniformly in the complement. The value $s=1$ cannot be made uniform: at $b=2,p=3$ the prime $19$ already gives $G=1$ on $19\le L\le26$.
- **Order valuation.** $v_p(\operatorname{ord}_{\ell^f}b)=v_p(\operatorname{ord}_\ell b)$ for $\ell\ne p$, so complementary depths never change $M_b$. They change only the period.
- **Exponent $\beta$ schedule $F(u)=u^KP(u)$.** The dyadic sum is correct: shifts with $L(n)<2v$ number at most $F(2v)\le N(2v/L)^K$ because $P$ is monotone under divisibility, the sum is geometric since $K>\beta$, and the buffer is $O(L\log L)$ against $N\ge L^K$ with $K>\beta+1$.
- **Accelerated exponents.** Inverting $F(u)=u+\lceil\exp(u/(\log(2+u))^\alpha)\rceil$ gives $L(n)\sim\log n(\log\log n)^\alpha$, and $\log P(L)=O\bigl(L\log\log L\log\log\log L/\log L\bigr)=o(L/(\log L)^\alpha)$ for $\alpha<1$, so the residual sum is $N^{o(1)}$. The claimed rate follows.
- **Ford–Luca–Pomerance.** I read Lemma 5.1 in the published paper (*The image of Carmichael's $\lambda$-function*, Algebra & Number Theory 8 (2014), section 5). Its hypotheses are $3<y\le2\min x_i$, and it bounds $\#\{n_i\in(x_i,2x_i]:P^-(n_1\cdots n_h)>y,\ b_jN_j+1\text{ prime}\}\ll_{h,k}x_1\cdots x_h(\log y)^{-h-k}(\log\log3b_1\cdots b_k)^k$. With $h=k=1$, $y=x^{1/12}$ every prime $r>x$ qualifies, the implied constant is independent of $m$, and the draft's dyadic sum over $L/\log L<r\le L/m$ and $m<\log L$ gives $\sum_m\log\log(3m)/m\asymp\log\log L\,\log\log\log L$. The cited statement is accurate. This is the classical twin-prime-type upper bound with singular series $m/\varphi(m)\ll\log\log3m$.
- **Maximal denominators.** $q\le G(b^{P/G}-1)$ is correct. The construction $q_j=(b^{t_j}-1)p^j$ with $t_j=d\,j!$ was checked exactly for $(b,p)\in\{(2,3),(2,5),(3,5),(10,3),(7,3)\}$ and $j\le8$: the order is $t_jp^j$ in every case, and $Q_j>b^{t_j/2}-1$ holds for all but the case $j=1$ with $b=2$ (the draft says "eventually"). The telescoping rational example in section 6 was re-checked: coefficients lie in $(0,1]$, the truncations telescope to $b^{-n_1}-b^{-n_j}p^{-e_j}$, and the late fragment is far shorter than the period.

## Points to fix or clarify

**R1. Formula for $q(L)$ (grids.md, Section 3).** The displayed $q(L)=3^{J_3}\prod_{3\le\ell\le L}\ell^{J_\ell}$ is correct only because the product includes $\ell=3$, which supplies the second factor $3^{J_3}$. A reader who takes the product over $\ell>3$ gets $e=J_3$, contradicting $e=2J_3$ stated next. Write $q(L)=3^{2J_3}\prod_{5\le\ell\le L}\ell^{J_\ell}$. The identity $\log q=\psi(L)-J_2\log2+J_3\log3$ then reads off directly.

**R2. The Lean evidence is not reproducible from the repository (grids.md, Section 7).** The text says the module was built "in a disposable overlay of the Phase 18 checkpoint" with 8,748 jobs and 1,596 declarations. `NormalityChecker/SurvivingGrid.lean` is not imported from `NormalityChecker.lean`, is not in `Audit.lean`, and is not in the generated theorem directory, so `lake build` on `1d0c1dd` alone does not compile it. This machine has no Lean toolchain (`lake`, `lean` and `elan` are all absent), so the build and the axiom audit were **not** re-run here. I read the proof text only. The three statements match the prose, and no `sorry` or non-Mathlib axiom is visible in the source. Before the module is cited as kernel-verified in the README, import it in the library root, run `lake build`, and refresh the declaration index with `NORMALITY_UPDATE_THEOREM_INDEX=1 lake env lean scripts/readme_theorems.lean`. Until then, "have Lean proofs" should read "have Lean proofs in a disposable build".

**R3 (optional). Maximality statement.** "Among all equally spaced subsets of the orbit whose size is a power of $p$" is correct. The next paragraph gives the stronger and exactly verified statement for arbitrary sizes. Moving the first sentence of "Combining primes" up as a corollary would let the headline "largest equally spaced ternary grid" be quoted without qualification.

**R4 (optional). Section 7 sources.** I checked the cited statements. Kano's Theorem 1 is for coprime integers $a,b>1$ (not necessarily prime) and a denominator $a^{\cdot}$; Vandehey's Theorem 7.4 is for a finite prime set coprime to $b$ with $c_k\mid c_{k+1}$. Both descriptions in the draft are accurate in spirit. The wording "powers of a fixed denominator base" should say "integer $a$ coprime to $b$". Hadamard's DOI resolves to Bull. SMF 24 (1896), 199–220. I could not retrieve the BBP paper (the publisher returned a web page rather than the PDF), so "formula (1.2)" in section 6 is unchecked and should be confirmed against the text.

**R5 (optional). Portal check.** `python scripts/portal.py check` already fails at `1d0c1dd` with `figures: stale or missing: assets\figures\data\proof-dependency-map.json`, independent of this review. It needs `PYTHONUTF8=1` on Windows to run at all. Registering the major result in `docs/registry/` is still to do. The README survey has not been updated for this result.

## Phase 18 statements touched

- `summation.md`, the original construction (prime 3 and primes $\equiv2\bmod3$, rate $O((\log N)^{-1/2})$): re-derived, correct. The grid size is $3^{e-1}$ because $v_3(2^t-1)=1$ and the order modulo $Q$ is prime to $3$.
- `reviews/translation-summation.md`, "Scope of the grid theorem": the $p=5$ assertion that "no grid survives" is unsupported as argued. The Phase 19 draft already corrects it. It should be amended in the Phase 18 review to "not established".
- `prime-delay.md`: not re-audited in full. The statement quoted by the draft, odd denominator $\log=N+o(N)$ at the original cutoffs, matches the text of the note.

## Hash and scope

This review adds only `notes/phase19/reviews/grids.md`. The branch `t3/audit-phase19-prime-construction` was fast-forwarded to `1d0c1dd` to read the files, and the review commit sits on top. Track C files are untouched.
