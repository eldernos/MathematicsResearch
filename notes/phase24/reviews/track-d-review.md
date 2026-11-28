# Referee report on Phase 24, Track D

**Recommendation: ACCEPT AFTER REVISION.** I rederived every theorem in the note and found no Critical error. The four headline results survive line by line:

* the metric $\{1,2\}$ continued-fraction theorem, including the transfer through Hochman–Shmerkin;
* the computable growing-cap construction with $q\|qx\|\gg1/(1+\log\log(3q))$;
* the exact low-numerator law at the selected fractional arrivals and its scaled-phase equidistribution;
* the deterministic full-density shell family.

One finding is Major. The headline bullet for §§1–2 carries the plain label "Paper proof", although two of its conclusions depend on external inputs. The remaining findings are Minor. They cover citation precision, attribution, two clarity points, and verifier hygiene and disclosure.

This cross-provider referee review was written by Claude Opus 5.5 about work by Codex `gpt-6.2-astra`. **Cross-model review is not independent human peer review.** Line numbers refer to the [note](../nonlinear-boundaries-and-approximation.md) (SHA-256 prefix `c9394b30b108e0a8`) and the [verifier](../../../scripts/phase24_nonlinear_approx.py) (SHA-256 prefix `fe880b215d38fb19`).

## Method

* **Line-by-line rederivation** of every displayed formula and inequality. This includes (1)–(12), the theorem in §2, the effective measure estimates in §3, and Phase 23 Lemma 5, on which (9) and (11) depend.
* **External inputs checked against source text.** I extracted the text of the linked Hochman–Shmerkin preprint and of Ghidelli's arXiv:1910.05076v1 and compared the statements actually used. Details are in D1 and D3.
* **Verifier run twice** with `python -B scripts/phase24_nonlinear_approx.py` (Python 3.13.13, Windows host, no Lean or LaTeX involved). Both runs exited 0 in about 2 s, and their outputs were byte-identical. Every count printed matches line 273 of the note: 529, 4608, 648, 124 and 192.
* **Instrumented copy** (scratch only, repository untouched) to confirm that the conditional assertions actually fire. The two-word gap assertion fired 1545 times and the exact-block assertion 1252 times. The window recurrence (4) was checked at 3260 consecutive fractional arrivals. The height-bound check fired 448 times out of 1152 shell steps and the depth check 1024 times. The full-period histogram ran in 4 of the 6 arrival fixtures.
* **Independent reimplementation** (my own modular-arithmetic code, not derived from the verifier) of the theorem in §2 on four fixtures absent from the script: $(d,p,s,b,a,h)=(2,7,1,2,3,2)$, $(3,7,2,2,2,2)$, $(2,5,1,2,3,2)$ and $(3,5,2,2,2,2)$. All 13 468 window positions satisfy (4) with exact denominator $p^E$ and $A_M\equiv1\bmod p$. All 21 selected arrivals have the predicted innovation depth $s(d-1)a-v_p(d)$. A brute-force triple count confirms the $d=p=3$ depth $2sa-1$ for $(a,s)=(1,1),(2,1),(2,2),(3,1)$, with no diagonal triples. Sampling 2000 random $\{1,2\}$ continued fractions gives a minimum of $q\|qx\|$ over $q<200$ equal to $0.267950$, matching the exact infimum $2-\sqrt3$ (attained at $q=1$). These are finite checks only.

## Summary of findings

| ID | Severity | Location | Issue |
|---|---|---|---|
| D3.1 | **Major** | note l. 11, 46, 57 | Headline labelled "Paper proof" but depends on DEKKM and Ghidelli (External input); square irrationality restates Phase 23 Thm 1 |
| D3.2 | Minor | l. 48–57 | Ghidelli tail bound is an intermediate step in the proof of his Thm 1.1, not a stated theorem; pointer and constant provenance should be exact |
| D3.3 | Minor | l. 44 | Negative literature claim about Żmija unverified; soften |
| D3.4 | Minor | l. 88 | "Its residue modulo $p$" has an ambiguous referent |
| D3.5 | Minor | l. 82, 103 | $J\asymp p^{a-dh/s}$ only up to $p^{d}$ and a floor; $J=0$ in small cases, including the $s=1$ cube fixture |
| D1.1 | Minor | l. 139 | Cite the published Hochman–Shmerkin version and confirm theorem numbering |
| D1.2 | Minor | l. 141 | Phrase the non-arithmeticity check in the source's own form |
| D2.1 | Minor | l. 178, 267 | A computable example with *bounded* partial quotients is left unstated; add an Open item |
| D2.2 | Minor | l. 207 | State the explicit modulus used to compute $\nu$ of intervals with computable endpoints |
| D4.1 | Minor | l. 234–265 | §4 is the $h_k\equiv1$ case of Phase 23 Thm 7's regrouping with $\lambda_k=a_k/(b-1)$; say so |
| D4.2 | Minor | l. 259 | "Uniformly in the choices" is asserted without listing the constants that must be uniform |
| D5.1 | Minor | script l. 290–293 | Vacuous assertion with a misleading comment |
| D5.2 | Minor | script l. 117–135; note l. 273 | Undocumented checks; escape witnesses are trivial finite measurements |
| D5.3 | Minor | script l. 420–425 | Fixture coverage not disclosed: one fixture has 0 selected arrivals, two skip the histogram |
| D5.4 | Minor | script l. 96, 324, 405–407 | Analytic input encoded as an assertion; synthetic digits; one partial-sum check |
| D5.5 | Minor | note l. 271; `scripts/verify.sh` | Label word coverage as a finite measurement; verifier is not wired into the harness |

## D1. Bad approximation and polynomial normality in every base (§3, l. 137–151)

**Verdict: correct, given Hochman–Shmerkin Theorem 1.4. No hidden gap.**

*The note does not use Fourier decay.* The task brief asked whether the argument needs Kaufman, Queffélec–Ramaré, Bourgain or Sahlsten–Stevens-type Fourier decay, or Davenport–Erdős–LeVeque Weyl sums, for every degree. It needs neither. The note invokes Hochman–Shmerkin's EFD/CP-chain theorem, which gives pointwise normality for $g_*\mu$ for **every** $g\in\mathrm{diff}^1(\mathbb R)$. The degree of $P$ enters only through the countable cover of $\{P'\ne0\}$ by compact intervals. This route avoids the real gap that a Fourier argument would face: polynomial decay of $\widehat{P_*\mu}$ for all degrees, which is not supplied by the dimension bound $\dim C_{\{1,2\}}\approx0.531>1/2$. The dimension threshold plays no role here. Hochman–Shmerkin Theorem 1.12 explicitly covers sets $C_\Lambda$ of dimension below $1/2$.

*Hypotheses checked against the preprint text.*

* **Regularity.** The preprint requires strictly contracting, orientation-preserving $C^{1+\epsilon}$ injections $f_i:I\to I$ with the intervals $f_i(I)$ disjoint except possibly at endpoints. On $I=[0,1]$ the four maps $f_i\circ f_j$ have images $[1/3,2/5]$, $[2/5,3/7]$, $[1/2,2/3]$ and $[2/3,3/4]$, so they touch only at endpoints. Their derivative is $(f_i\circ f_j)'(x)=(i(j+x)+1)^{-2}\le1/4$. The maps are real-analytic and increasing.
* **Quasi-product measure.** The preprint's property (1) asks that cylinder masses be multiplicative up to a constant $C$. The fair Bernoulli measure on the four symbols satisfies it with $C=1$, and the law of $x$ is the pushforward of this measure.
* **Non-arithmeticity.** Theorem 1.4 requires some $f\in I$ with $\lambda(f)\not\sim b$, where $\lambda(f)=f'$ at the fixed point and $a\sim b$ means $\log a/\log b\in\mathbb Q$. Here $\lambda(f_1\circ f_1)=\rho^4$ with $\rho=(\sqrt5-1)/2$, which I confirmed numerically. Since $\rho$ is a unit of $\mathbb Q(\sqrt5)$, $\rho^{4m}=b^n$ forces $b^{2n}=1$ by taking norms, so $n=0$ and then $m=0$.
* **Diffeomorphism.** Continuing $\pm P$ by its endpoint tangent lines yields a strictly increasing $C^1$ bijection of $\mathbb R$, as Theorem 1.4 requires. Negation preserves uniform distribution modulo one. The critical points are null because $\mu$ is nonatomic. The countable intersection over intervals, polynomials and bases is valid.
* **Source description.** The note says "§1.3.3 treats the regular continued-fraction system of pairs of digits" (l. 139). The preprint says exactly this: "$C_\Lambda$ is the attractor of a regular IFS, namely $\{f_i\circ f_j\}$ … (the reason for the compositions is that, although $f_1$ is not a strict contraction, all the compositions $f_i\circ f_j$ are)."

*Bad approximation.* The identity $q_i|q_ix-p_i|=(\alpha_{i+1}+q_{i-1}/q_i)^{-1}$ holds with $\alpha_{i+1}\le1+\sqrt3<3$ and $q_{i-1}/q_i\le1$. The edge case $q=1,\ a_1=1$ is handled correctly by "the last such $i$", which gives $1-x\ge2-\sqrt3$. The unimodular best-approximation argument, including $u\ne0$ and opposite signs, is the standard Lagrange proof. The claim "> 1/4 for all $q$" is valid with margin; the exact infimum is $2-\sqrt3$.

*Encoding (6) and the forward choice.* I verified the following:

* $Z=S+\{x-S\}=x-\lfloor x-S\rfloor$ with $\lfloor x-S\rfloor\in\{-1,0\}$.
* The shifted-prefix denominator is exactly $\prod\ell_n$.
* The coefficients lie in $(0,b)$.
* Normality of $d_n$ follows from the translation diffeomorphism.
* Uniformity of the forward choice on $[S,S+1]$, the Borel–Cantelli bound for $\mu(Z)=2$, and the remark that bounded partial quotients do not follow are all correct.

**Minor D1.1: Citation version.** Lines 139 and 141 link the author's preprint. Cite the published version, Invent. Math. 202 (2015), 427–479, and confirm that the theorem numbers 1.4 and 1.12 and the subsection 1.3.3 agree there. Quote the hypothesis in the source's own notation: "there exists an $f\in I$ with $\lambda(f)\not\sim\beta$".

**Minor D1.2: Phrasing at line 141.** The sentence "no nonzero power of $\rho^4$ is a rational power of $b$ with nonzero rational exponent" is correct but roundabout. Replace it with "$\log\rho^4/\log b\notin\mathbb Q$, i.e. $\lambda(f_1\circ f_1)\not\sim b$ in the notation of Hochman–Shmerkin". Also state the interval $I=[0,1]$ and the bound $(f_i\circ f_j)'\le1/4$, so that the regularity check is self-contained.

## D2. The computable growing-cap construction (l. 169–211)

**Verdict: correct. The $\log\log$ bound holds for every $q$, with no exceptional subsequence. Polynomial absolute normality and a new persistent prime at every position hold simultaneously.**

The bound $q\|qx\|\gg1/(1+\log\log(3q))$ does **not** use determinant folding or pole retention. It follows from choosing the continued fraction directly under the caps. Folding appears only in §4, for the weaker bound (11). Checks:

* **The bound (7).** For $q_i\le q<q_{i+1}$, $q\|qx\|\ge q_i|q_ix-p_i|>(A_{i+1}+2)^{-1}$, because $\alpha_{i+1}<a_{i+1}+1\le A_{i+1}+1$. Every $q$ lies in such a range, so no subsequence of convergents can escape. From $q_i\ge2^{(i-1)/2}$ we get $i+1\le\lfloor2\log_2q\rfloor+2$, so the index $\lfloor2\log_2q\rfloor+3$ is valid (with one to spare). For $A_i=\max(2,\lceil\log_2(i+1)\rceil)$ this gives the stated $\log\log$ bound.
* **Retained length.** The retained relative length $A/(A+1+y)$ follows from the telescoping sum of the child lengths $((jq+q')((j+1)q+q'))^{-1}$. Hence $\nu(I)\le L_m|I|$, since $(A+1+y)/A\le1+2/A$. Every depth-$m$ cylinder, whatever its digits, has length at most $2^{1-m}$. Inequality (8) follows by covering, and the effective modulus $\log L_m\le2j+2m/A_j$ is correct.
* **Word frequencies.** The tail bound $2k\exp\{-2\epsilon^2\lfloor(N-k+1)/k\rfloor\}$ is Hoeffding's inequality applied to each residue class of starts. Each class consists of disjoint blocks, hence i.i.d. under Lebesgue measure. The overall frequency is a weighted average of the class frequencies, so some class must deviate.
* **Preimages.** The preimage-length bound $C_Pu^{1/r}$ is correct. Use $ru/\eta$ where $|P'|\ge\eta$, and the root-proximity bound $(\eta/(r|\mathrm{lc}P|))^{1/(r-1)}$ elsewhere, with $\eta=u^{(r-1)/r}$. Because the bad sets are open arcs of the circle "allowing wraparound", the map $x\mapsto P(x)\bmod1\in\mathbb R/\mathbb Z$ is continuous. So the $E_N$ are genuinely open even where $P(x)\in\mathbb Z$.
* **Depth choice.** With $m=2\lceil\log_2b_0\rceil(N+2)$ the endpoint term is $O_P(b_0^{-N})$, and $\log L_m=o(N)$ effectively. Hence $\nu(E_N)\le2^{-\delta N}$ for computable $N_0$ and $\delta$.
* **Selection.** $F$ is closed and $\nu(F)\ge3/4$. $\nu(F\cap I)$ is computable from both sides with explicit tail budgets. Positivity is semi-decidable, and some child always has positive mass. The limit point lies in $F$ because $F\cap\overline{I_m}\neq\varnothing$ for nested compact sets of shrinking diameter. It is the irrational $[0;a_1,a_2,\ldots]$ with $a_i\le A_i$.
* **Simultaneity.** $P(Z)=P(x+k)$ with $k\in\{0,1\}$ is again a nonconstant rational polynomial in $x$, so it is in the enumerated test list. The prime structure of (6) does not depend on $x$, and the base-$b$ normality of $x-S$ is one of the tests. All conclusions therefore hold for the same computable point.

**Minor D2.1: Missing Open item.** Line 178 notes that the fixed cap 2 suffices for *metric* existence. The construction, however, needs $A_i\to\infty$ to make $L_m=e^{o(m)}$, and the Hochman–Shmerkin theorem is ineffective. Add an explicit **Open** item to §4 or to the scope section: whether a *computable* $x$ with bounded partial quotients has $P(x)$ absolutely normal for every nonconstant $P\in\mathbb Q[X]$. Before asserting novelty, check the literature for the case $P(X)=X$, where effective Fourier decay of Kaufman / Queffélec–Ramaré type measures may already give a computable example.

**Minor D2.2: Effective modulus in Step 3.** Line 207 says that masses of intervals with computable endpoints are computable "by non-atomicity". Make the modulus explicit. A depth-$m$ cylinder meeting an endpoint has mass at most $L_m2^{1-m}$, and the $j$-bound after (8) makes this quantity effectively tend to zero. The argument is then uniform, as claimed.

## D3. Equality-boundary numerators (§§1–2, l. 18–133)

**Verdict: the mathematics is correct. The headline label is not.**

Checks:

* **The lattice condition (1)** follows from $QB^MX=Q(R_M+T_M)\in\mathbb Z$, which forces $Qq_MT_M\equiv-QA_M\pmod{q_M}$, together with positivity of the tail. The threshold for a single gap, the denominator-only liminf criterion and its stated "equivalence" are correct. The note correctly limits that equivalence to the denominator-only test.
* **Denominator and coefficient bounds.** AM–GM gives $\prod x_i\le m/d$, so the denominator divides $p^{s\lfloor\log_p(M/d)\rfloor}$, with equality at $M=dp^{da}$. The exponents are correct: $\alpha=(d-1)/d$ in general; $\alpha=0$ for squares via $r_2\le4\tau$; and $\alpha=1/3$ for cubes, since $y+z\mid m-x^3$ and $yz=((y+z)^3-(m-x^3))/(3(y+z))$. Also $M+g=O_d(M)$ via $x^d+(d-1)$. These give criterion (2). For $(b,p,s)=(2,3,1)$ and the cube, the threshold is $(4/3)/\log4=2/(3\log2)$, as stated.
* **Digit blocks for the square** (l. 46). The next grid point above $\{R_M\}$ lies at distance at least $1/(q_Mb^L)$. On the DEKKM subsequence, $q_Mb^LT_M\ll M^{s+\lambda\log b+\epsilon}B^{-g}\to0$ whenever $\lambda\log b<(390/449)\log B-s$. The Morse–Hedlund remark (complexity at least $L+1$ for aperiodic one-sided sequences) is correct; for one-sided sequences every factor has a right extension.
* **Cubic two-word prediction** (l. 57). At $M=n-1$, $T_M=B^{-K-1}\sum_jc_{n+K+j}B^{-j}\le B^{-K-1}\cdot60(\log T)^{C}$, because $c_m\le r(m)$ and $B\ge2$. With $L=\lfloor(1-\epsilon)tK\rfloor$ we get $b^LT_M\le60(\log T)^CB^{-\epsilon K-1}\to0$, since $K\gg\sqrt T/(\log T)^2$. The conditional remark using residues bounded below is also correct.
* **Ghidelli input checked.** Ghidelli's Definition 3.2 defines a mild gap point $n$ by $a_{n+k}=0$ for $0\le k<K$ and $\sum_{i\ge0}|a_{n+K+i}|2^{-i}\le E$, which is exactly the note's indexing. His §8.1 sets $N=M^{\sigma_3}$, $\xi_3=(\log T)^{C_3}$ and $E=60\xi_3$. Lemma 7.1(i)–(ii) give $\log M\asymp T$ and $K_1\ge C_2\sqrt T/(\log T)^2$. His §8.2 obtains $B\subset[0,N-K_2)$ with $B\subseteq\mathrm{MildGap}(f;K_1,E)$ via Proposition 6.1 and Lemma 4.2. His $r_{3,3}$ counts ordered tuples in $\mathbb N^3$ with $0\in\mathbb N$, so the bound $c_m\le r(m)$ is valid.
* **The recurrence (3)** follows from $R_v=B^{v-u}R_u+\sum B^{v-i}c_i$ multiplied by $p^e$. The hypothesis that $e$ dominates the intervening depths makes every term integral.
* **Theorem (4).** Before $M$ the level is $<da$. At $M$ only the tuple $(U,\ldots,U)$ attains level $da$, so $A_M\equiv1\bmod p$. Every coordinate in the window is $<(d+1)^{1/d}U\le2U$, so its valuation is at most $a$. A tuple that survives modulo $p^h$ has loss at most $v-1$, so all its coordinates are divisible by $p^{a-v+1}$ and $G$ divides its position. Only $M$ is such a position in the window. Hence the denominator is exactly $p^E$ throughout $[M,(d+1)U^d)$ for every $h\ge1$.
* **Selected arrivals.**
  * Position: $m_j-M\le d(2U)^{d-1}J\le G/2$, so $m_j$ lies in the window.
  * Top level: $m_j\equiv j^d\not\equiv0\pmod p$, so some coordinate is a unit and the top level $(d-1)a$ forces the remaining coordinates to equal $U$. This gives exactly $d$ ordered tuples.
  * Depth for $d=p=3$: no tuple is diagonal, every level count is divisible by 3, and the depth is $2sa-1$.
  * Exponent: since $(U+j)^d-U^d\equiv j^d\pmod{p^a}$ and $a\ge k$, $A_{m_j}\equiv A_MB^{j^d}\pmod{p^h}$.
* **Residue count (5)** follows from cyclicity of $(\mathbb Z/p^k)^\times$ for odd $p$ and the fact that $B$ has order $p^k$ modulo $p^h$, by the lifting-the-exponent lemma. With $h=\lfloor\gamma a\rfloor$ and $\gamma<s/(s+d)$, $J/p^k\ge p^{a-dh/s-h}\to\infty$. There are therefore $M^{\gamma/d+o(1)}$ distinct residues.
* **Scaled phases.** We have $(1+p\mathbb Z_p)^d=1+p^{u}\mathbb Z_p$ with $u=1+v_p(d)$, and $B^{p^u}$ generates $1+p^{w+u}\mathbb Z$ modulo $p^h$. Each period is therefore a uniform mixture of translated grids of spacing $p^{w+u-h}$. The discrepancy $O(p^{-h}+p^k/J)$ is correct.
* **Localized criterion.** Integrality gives $Q\cdot\{p^{E-h}R\}\in[-Q\eta,0)\bmod1$. The pullback under $y\mapsto Qy$ preserves measure and has at most $Q+1$ pieces. The lowered threshold $\lambda>(s+\alpha-\gamma/d)/\log B$ follows. For the flagship cube it tends to $(5/4)/\log4\approx0.902$ as $\gamma\to1/4$, compared with $0.962$. The note correctly says that the required frequency of gaps at the selected arrivals is not supplied by either cited theorem.
* **Finite-window bridge.** If $\|B^mQX\|\le c<1/(B+1)$ eventually, then the errors satisfy $\epsilon_{m+1}=B\epsilon_m$ and must vanish. The two-cycle at $1/(B+1)$ shows the constant is optimal. This "if and only if" is in substance a reformulation of irrationality, and the note's last sentence at line 133 says as much.

**Major D3.1: Headline evidence label and attribution.** Line 11 labels the whole bullet "Paper proof, §§1–2". Two of its sentences rest on external inputs:

* "irrationality for $s<(390/449)\log B$" requires DEKKM Theorem 1 (body l. 44);
* "arbitrarily long digit blocks determined up to a single carry" requires Ghidelli §8.2 (body l. 48).

The body labels them correctly, but the repository's evidence-label policy applies at the claim level, and these bullets feed the registry. Split the bullet. The numerator law, the scaled equidistribution, the localized criterion and the bridge are a "Paper proof". The square irrationality and the cubic two-word prediction are a "Paper proof using external input". In addition, the square irrationality at line 46 is Phase 23 Theorem 1, restated with $B=b^t$. Credit it as such. Only the refinement to digit blocks of length $\lfloor\lambda\log M\rfloor$ is new.

**Minor D3.2: Precision about the Ghidelli input.** Lines 48–55 present the weighted tail bound as a published conclusion. In the source it is not a numbered theorem. It is an intermediate step inside the proof of Ghidelli's Theorem 1.1 (§8.2: $B\subseteq\mathrm{MildGap}(f;K_1,E)$, with $E=60\xi_3$ from §8.1). The exponent $C=C_3$ is an unspecified constant that comes through Lemma 7.1 from Ghidelli's Waring paper. Revise as follows:

* cite arXiv:1910.05076**v1**, or its published version if one exists;
* point to Definition 3.2, Lemma 7.1(i)–(ii) and §§8.1–8.2;
* note that the gap starts lie in $[0,N-K_2)$;
* note that §8.2 needs only $T$ larger than a threshold independent of $q$ and $J$, as the preprint says before Proposition 9.1.

The deduction itself is correct.

**Minor D3.3: Unverified negative literature claim.** Line 44 asserts that Żmija's bound "does not improve this special constant at discriminant $-4$". I did not verify this, and nothing depends on it. Write "to our knowledge" or delete the sentence.

**Minor D3.4: Ambiguous referent at line 88.** "Its residue modulo $p$ is nonzero" refers to $m_j$, not to the innovation. Write "$m_j\equiv j^d\not\equiv0\pmod p$, so at least one coordinate is a unit."

**Minor D3.5: Size of $J$.** By definition $J=\lfloor p^{a-d(v-1)}/(d2^d)\rfloor$. So "$J\asymp p^{a-dh/s}$" (l. 103) holds only up to a factor at most $p^d$ and the floor. In particular $J=0$ for small $a$. The verifier's flagship-type fixture $(d,p,s,a,h)=(3,3,1,3,2)$ has $J=0$ and no selected arrivals at all, and even the exact maximal range is empty there. State $J\ge p^{a-dh/s}/(d2^d)-1$ and note that the $s=1$ cube needs fairly large $a$ before any arrival is selected. (Optional: the theorem and its proof hold for every $d\ge2$, not only $d\in\{2,3\}$. Only the $p\mid d$ depth computation needs the orbit argument in general.)

## D4. The deterministic full-density family (§4, l. 232–267)

**Verdict: correct. The exact regrouping is disclosed where it is used (l. 257, 265).**

Checks:

* **Coefficients and occupancy.** CRT gives $0<c_k\le\mathrm{rad}(b)$, with $u_k$ the least positive solution modulo $p^k\mathrm{rad}(b)\mu_k$. Every $n\ge2$ is occupied, and the coefficients lie in $(0,\mathrm{rad}(b)+2]$, the maximum occurring at $n=2^{k+1}$.
* **Regrouping (12).** $\sum_{2^k<n\le2^{k+1}}b^{-n}=(b^{-2^k}-b^{-2^{k+1}})/(b-1)$, which gives $d_k=c_k+(a_k-a_{k-1})/(b-1)$ with $a_0=0$.
* **Depth and units.** $p^kb^{-2^k}c_k\equiv1\pmod{p^k}$, and the correction has valuation at least $k-v_0$. Hence the depth is exactly $k$ for $k>v_0$, and $p^kb^{-2^k}d_k\equiv1\pmod{p^{k-v_0}}$. Early indices have bounded depth, so their depth defect tends to infinity.
* **Pole retention.** Pole retention comes from the anchored upper-set sum modulo $p^L$, with $L=L(p,r)$ uniform. The complementary denominator divides the prime-to-$bp$ part of $((b-1)\prod_{j^2\le k}\ell_j)^r$. Its order is $N^{o(1)}$, and the $(b-1)$ part has bounded order because $b\equiv1\pmod{b-1}$.
* **The bound (11).**
  * Integrality: $E_k=(b-1)D_k$ clears all $d_i$ with $i\le k$.
  * Numerator: the numerator is congruent to $E_kd_k$ modulo $b^{2^{k-1}}$, so the radix valuations agree once $\log|E_kd_k|=O(k)$.
  * Heights: $q_k/b^{2^k}$ has both heights $\exp(O(k))$, and so does $z_k=d_{k+1}(q_k/b^{2^k})^2$.
  * Lemma 5: I rederived Phase 23 Lemma 5, covering the cases $L=0$, $|L|\ge2|z|w$, and the inverse test with denominator $|cL|$. It gives $H_k=O(k^2)$.
  * Approximation: choosing the first $2^k\ge4\log_bq$ gives $q_k\ge q^4e^{-O(k)}>q$ and a tail of $O(q^{-8})$.
  * Small $q$: compactness of $\{1,2\}^{\mathbb N}$ handles the finitely many small $q$, using the irrationality already proved.
* **Irrationality and distinctness.** The filler minus the rational baseline has shell digits $a_k-1$. If both values recur, the constant runs are unbounded and changes occur infinitely often, which rules out eventual periodicity. Distinct choices give distinct values because $b^{-2^k}-b^{-2^{k+1}}>b^{-2^{k+1}}$, which is equivalent to $b^{2^k}>2$. Continuum many classes modulo rationals follow.

**Minor D4.1: Attribution.** Phase 23 Theorem 7 regroups $V=\sum(c_k+\lambda_k-\lambda_{k-1})b^{-2^k}$ with $\lambda_k=1/(b^{h_k}-1)$. Section 4 is the case $h_k\equiv1$ with shell multipliers, $\lambda_k=a_k/(b-1)$. State this. It shortens the normality reduction at line 259 and clarifies what is new: full occupied density, a free binary choice at every shell, and an irrational perturbation.

**Minor D4.2: List the uniform constants.** "$D_N\ll_{P,b,p}N^{-\eta_P}$, uniformly in the choices" (l. 259) is plausible but asserted without detail. List the quantities that must be uniform in $a$:

* the anchored-set precision $L(p,r)$;
* the depth threshold $k\ge2L+v_0$;
* the coefficient bound $|d_k|\le\mathrm{rad}(b)+2/(b-1)$, which fixes the buffer constant $C_P$;
* the bounded depth of the early indices;
* the complementary order, which depends on $a$ only through the fixed $(b-1)$ factor.

Each item is immediate. Listing them turns the reduction into a checkable proof.

## D5. Verifier, reproducibility and evidence separation

The run reproduces exactly (see Method). The script uses only integers and `Fraction`, has no randomness and imports only the standard library. The finite exclusion of rationals is sound: `Fraction.limit_denominator` returns the *closest* fraction with bounded denominator, so a distance greater than the half-width excludes every such fraction from the enclosure. The note keeps finite certificates separate from asymptotic proofs, labels External input and Open items, and states at line 273 that cross-model review is not independent human peer review.

**Minor D5.1: A vacuous assertion.** Script lines 290–293 claim in a comment to bound the irrationality constant "for every allowed next digit and every tail in $(0,1)$, via two rational endpoints". The assertion `1/(next_cap+1+q0/q1) >= 1/(next_cap+2)` is identically true because $q_0\le q_1$. It tests nothing about the cylinders. Either implement the stated endpoint check, evaluating $q_1|q_1y-p_1|$ at both cylinder endpoints of each allowed child, or delete the assertion and its comment.

**Minor D5.2: Undocumented checks.** The escape witnesses in `check_flagships` (script l. 117–135) are not mentioned in the note. They fire at $m\le2$ for every $Q\in\{1,2,3,5,7\}$, which carries no information about the limsup in the bridge criterion. Either delete them or document them as a *finite measurement* that "implies nothing about $\limsup$". Line 273 also omits the 54 scaled-grid unions, the 7 exact reciprocal folds, the 120 individual-site prefixes and the 4096 binary word tests. List them.

**Minor D5.3: Fixture coverage.** Of the six arrival fixtures (script l. 420–425), $(3,3,1,4,3,2)$ has **0** selected arrivals and $(2,3,2,4,4,3)$ has 3 selected against $\varphi(p^k)=6$. Only four fixtures test the histogram equality (5) over a full period. Disclose this in the note. The $s=1$ flagship cube needs $a\gtrsim6$ before any arrival is selected, which is beyond a quick convolution, and saying so is sufficient.

**Minor D5.4: Small hygiene points.**

* Script line 96 encodes $(390/449)\log4>1$ through the analytic input $\log2>2/3$. Mark it in the code as an analytic input, not a finite certificate.
* `check_dense_metric` uses synthetic digits $(n^2+\lfloor n/3\rfloor)\bmod b$ (l. 324), not digits of $\{x-S\}$. It certifies the denominator structure only, and its printed name "Individual-site encoding" overstates this.
* Script lines 405–407 check the denominator at $m=2^{k+1}$ *before* $c_{k+1}$ is added. That is a partial sum, not a real prefix. Add a comment.

**Minor D5.5: Labels and harness.** Line 271 files the coverage of all 256 eight-bit words under "Finite certificate". The enclosure certifies it, but it is a digit statistic. The project rules treat these as finite measurements, so label it "Finite measurement (certified)". Separately, `scripts/verify.sh` runs only `test_*.py`, `portal.py check`, the citation and the site checks, so this verifier is never executed by the harness. If the Phase 23 convention applies, add a `test_phase24_*.py` wrapper.

## Verdict

**ACCEPT AFTER REVISION.** There are no Critical findings. The single Major finding, D3.1, is a mislabelled headline and a missing attribution; the fix is a one-paragraph edit. The Minor findings concern citation precision, attribution, clarity and verifier disclosure. None of them affects the truth of a stated theorem.

The deepest claim is the probability-one polynomial normality in every base for $\{1,2\}$ continued fractions. It is sound as a deduction from Hochman–Shmerkin Theorem 1.4, whose hypotheses I checked against the source text. It uses no Fourier-decay or Weyl-sum input, and no dimension threshold. The computable $\log\log$ construction and the deterministic shell family are elementary and complete.

**Cross-model review is not independent human peer review.** This report is a model-to-model audit. It does not substitute for an expert human referee, and in particular for one familiar with Hochman–Shmerkin's EFD machinery and Ghidelli's mild-gap method.

## Post-Repair Verification

Checked on 2026-11-27 against the working tree, which was not committed.

* **Major D3.1: closed.** The headline at line 12 and the §1 statements at lines 47 and 58 now read **Paper proof + External input**. The square result is described as a restatement of [Phase 23 Theorem 1](../../phase23/nonlinear-multivariate-and-denser-mu.md) obtained from the DEKKM two-square gap bound. The cube result names Ghidelli's weighted mild gaps as its external input.
* **Citations: addressed.**
  * Hochman–Shmerkin is cited at line 140 by Theorem 1.4, the "$\lambda(f)\not\sim\beta$" hypothesis, the pushforward under a fixed $C^1$ diffeomorphism and §1.3.3. Line 164 reuses the same theorem for the translation $y\mapsto y-S$.
  * Ghidelli is cited at line 56 by Definition 3.2, Lemma 7.1 and §§8.1–8.2 of arXiv:1910.05076v1. The note keeps the theta-series tail input separate from the cubic gap theorem.
* **Phase 23 Theorem 7 attribution: addressed.** Line 258 states the case $h_k\equiv1$ with $\lambda_k=a_k/(b-1)$ and lists the constants that must be uniform in the labels (D4.2).
* **Open problem: present.** Line 268 asks for a computable $x$ with bounded partial quotients such that every nonconstant $P(x)$ is absolutely normal.
* **Endpoint assertion (D5.1): fixed.** Script lines 319–324 now evaluate $q_1|q_1y-a_1|\ge1/(\text{cap}+2)$ at both cylinder endpoints of every allowed child. The note says this at line 279.
* **Escape witnesses (D5.2): documented.** Line 276 labels them a finite measurement and states that they "give no lower bound on the limsup". The extra check counts (54 unions, 7 folds, 120 prefixes, 4096 strings) are listed at lines 278–280.
* **Arrival fixtures (D5.3): disclosed.** Line 278 says that four fixtures cover a full unit period, that $(2,3,2,4,4,3)$ covers three of six units and that the flagship cube has no selected arrivals. It adds a separate $a=6$ depth check.
* **Hygiene and labels (D5.4, D5.5): addressed.**
  * The script marks the analytic input $\log2>2/3$ at line 96 and comments on the partial sum at line 437.
  * The note labels the 8-bit word coverage "Finite measurement (certified)" and describes the individual-site test as using synthetic digits.
  * The `scripts/verify.sh` wrapper is deferred to the final Phase 24 consolidation, as agreed.
* **Reproducibility.** `python -B scripts/phase24_nonlinear_approx.py` exits with code `0`.

**Verdict: ACCEPT.** D3.1 is closed and the applicable Minor findings are resolved. Only the harness wrapper remains, and it is scheduled for consolidation.

**Cross-model review is not independent human peer review.**
