# Phase 25 Track C — cross-provider adversarial referee review

**Audited files.** [`notes/phase25/euler-square-and-theta-powers.md`](../euler-square-and-theta-powers.md) (273 lines) and [`scripts/phase25_euler_theta.py`](../../../scripts/phase25_euler_theta.py) (272 lines), authored by Codex `gpt-6.2-astra`, on branch `research/phase-25-carry-correlations`.

**Reviewer.** Claude `claude-opus-5-5`, a different provider from the author. The audit was read-only: no audited file was modified, and nothing was committed.

> **Cross-model review is not independent human peer review.** This report is a second machine reading by a model from another provider. It does not replace refereeing by human specialists in sieve theory, modular forms or uniform distribution. None of its conclusions may be used to change a benchmark status.

## Verdict: **ACCEPT WITH MINOR POLISH**

| Severity | Count |
|---|---|
| Critical | 0 |
| Major | 0 |
| Minor | 14 |

The headline improvement from $1/26$ to $1/(3\pi)$ survives adversarial checking. That covers the sign-conditioned sieve, the source of the factor $2$, the constant $K=3\pi/4$, uniformity in $h$, the order of limits, and the rational certificate. I found no double counting and no missing factor of $2$. The theta-cube and fourth-power theorems and the prime-subseries theorems are correct as stated. Every finite number in the note was reproduced by the shipped verifier and by independent reviewer code. The minor findings concern wording, notation, attribution precision and labels.

---

## 1. Verifier run and script/note agreement

`python -B scripts/phase25_euler_theta.py` was run from the repository root on Windows. It printed `All exact checks passed.` and exited with code `0`. Output:

```
Finite certificate: old bound > 1/26; new bound 106103/10^6 < 1/(3 pi) < 106104/10^6.
Finite measurement: N=6000, signed complete-gap sum/N = 61/6000
Finite measurement: theta^3, k=1, 1024 blocks, ones=515/1024.
Finite measurement: theta^3, k=2, 1024 blocks, ones=1039/2048.
Finite measurement: theta^3, k=4, 1024 blocks, ones=1783/4096.
Finite measurement: theta^3, k=30, 1024 blocks, ones=2249/30720.
Finite measurement: theta^4, k=1, 1024 blocks, ones=527/1024.
Finite measurement: theta^4, k=2, 1024 blocks, ones=1003/2048.
Finite measurement: theta^4, k=4, 1024 blocks, ones=2043/4096.
Finite measurement: theta^4, k=30, 1024 blocks, ones=4110/30720.
All exact checks passed.
```

**Exact and floating-point arithmetic are separated.** The script uses only `int` and `fractions.Fraction`. There is no floating-point arithmetic anywhere. Certificate lines (`Finite certificate`) are printed separately from measurement lines (`Finite measurement`).

**Agreement with the note.** Every constant and count in note §4 (lines 269–271) and line 33 matches the output: $106103/10^6<1/(3\pi)<106104/10^6$, $8K_*<25.431<26$, $61/6000$, $515$ and $527$ at $k=1$, and $2249$ and $4110$ at $k=30$.

**Independent reproduction.** I wrote my own code in a scratch directory and shared nothing with the verifier.
- The Euler square was computed by direct expansion of $\prod(1-q^j)$ followed by squaring, not by the pentagonal convolution. It gives $61/6000$.
- For the theta powers, $r_3$ came from brute-force lattice enumeration, $r_4$ from convolving $r_3$ with $r_1$, and the tail from a separate crude enclosure. This reproduces all eight one-counts ($515, 1039, 1783, 2249$ and $527, 1003, 2043, 4110$).
- An `mpmath` evaluation at 40 digits gives $K=\Gamma(7/4)\Gamma(1/4)4^{3/4}/4=2.35619449\ldots=3\pi/4$ and $1/(4K)=1/(3\pi)=0.10610329\ldots$. It also gives $K_*=3.17844697\ldots$, $8K_*=25.42757\ldots<25.431$ and $1/(8K_*)=0.03933$. The improvement is therefore by a factor of about $2.70$.
- Extended arithmetic checks pass for $n\le 20{,}000$: $v_2(r_4(n))$, $v_2(r_3(n))$, the genus divisibility $2^{\max(0,\omega_{\rm odd}(d)-1)}\mid r_3(n)$, and the Pall/Hirschhorn–Sellers prime-square formula, with zero mismatches. The CM eta-power prime checks (inert vanishing and $a(p)^2\le 4p^{w-1}$) pass through index $3000$.

**Script certificate logic was checked line by line.**
- Machin enclosure, lines 59–60: an odd final index gives a lower bound, so the outward direction is correct.
- Γ(1/4) bound, line 63: the degree-80 Taylor polynomial is an upper bound for $e^{-x}$ on $x\ge0$ because the next term is negative. The tail satisfies $\int_{16}^\infty x^{-3/4}e^{-x}\,dx\le e^{-16}/8<2^{-16}$. Integrating gives exactly $\sum_j 8(-16)^j/(j!(4j+1))$.
- Product tail: $2/((p-1)(p^2+1))<1/(4j^3)$ for $p=2j+1$, and $\sum_{j\ge50}j^{-3}<1/4802$.
- Guard-block carry, lines 239–242: $\sum_{h\ge1}(h+1)^2 2^{-h}=11$ exactly, and the bound decreases as $B$ grows.

---

## 2. Euler's square: the $1/(3\pi)$ bound (Theorem 1)

### 2.1 The factor of two

Write $S$ for the number of support points in $(0,N]$, $\rho=S/N$ asymptotically, and $H=\lfloor t/\rho\rfloor$.

| | Gain | Pair deduction | Optimum |
|---|---|---|---|
| Phase 24 (GF-37) | $H\,S_\sigma\approx tN/2$ | all pairs: $K_*\,(H^2/2)\,S\,\rho = K_*t^2N/2$ | $\max(t/2-K_*t^2/2)=1/(8K_*)$ |
| Phase 25 (Thm 1) | $H\cdot(\tfrac12-\eta)S\approx tN/2$ | pairs whose **right endpoint has sign σ** only: $K\,(H^2/2)\,(S/2)\,\rho = Kt^2N/4$ | $\max(t/2-Kt^2/4)=1/(4K)=1/(3\pi)$ |

The factor $2$ is legitimate. In the old inequality $W_\sigma\ge HS_\sigma-H-\sum(H-h)P_h$, the term $P_h$ counted all pairs, but only pairs whose right endpoint has sign σ can create a deficit in $W_\sigma$. The old two-dimensional sieve on pairs of integers could not detect the sign. The new proof counts the right endpoint exactly through its multiplicative structure $l=v^2pm$. The sign enters only through the endpoint mass $\sum_v M_v\le(1/2+o(1))N\rho$, line 50. The predecessor sieve imposes no condition on the predecessor's sign. So nothing is counted twice and no sign factor is missing. Each deficit $(H-g)_+$ belongs to one right endpoint and is bounded by the pair at distance $g$. That pair lies among the sieved pairs at weight $H-g$. Predecessors with square part $>V$ are charged at most once each, because the immediate-predecessor relation is injective.

**Finite consistency check (finite measurement only).** At $N=4\cdot10^6$ the sign-conditioned predecessor-pair ratios
$\sum_{s(m)=\sigma}\sum_{h<H}(H-h)\mathbf 1[m-h\in U]\,/\,(S_\sigma\rho H^2/2)$ agree to three decimals for σ = + and σ = −:

| H | + | − |
|---|---|---|
| 2 | 0.464 | 0.463 |
| 8 | 0.831 | 0.830 |
| 32 | 0.949 | 0.949 |

All values lie far below $K=2.356$. So the halving of the pair mass by sign has no visible bias. The asymptotic ρ → 0 regime is not reachable numerically: ρ ≈ 0.29 at this N.

### 2.2 Constant $K=3\pi/4$

I rederived the constant independently and obtained the same result.
- **Sieve density.** The local density relative to units $u$ is $g(\ell)=1/(\ell-1)$ for $\ell\in\mathcal P$, $T<\ell<\xi$, $\ell\nmid h$. Then $g/(1-g)=1/(\ell-2)$ gives $G_T$, line 89.
- **Wirsing step.** Wirsing applied to $h(\ell)=\ell/(\ell-2)$ on $\mathcal P$, with mean $\delta=3/4$ by the prime number theorem modulo 12, followed by partial summation, gives $G_T^{-1}\sim e^{\gamma\delta}\Gamma(1+\delta)\prod(1-1/(\ell-1))$, lines 97–98.
- **Support normalization.** Wirsing at mean $1/4$ for $1_{\mathcal N}$ gives $\rho\sim\frac{4e^{\gamma\delta}}{\Gamma(1/4)}\prod_{\mathcal P}(1-\ell^{-2})^{-1}\prod_{\ell\le N}(1-1/\ell)$. The factor $4$ arises because every $\mathcal P$-free integer coprime to $6$ lies in the class $1\bmod 12$. That is a genuine concentration, and it is correctly carried from GF-29.
- **Local cancellation.** $(1-\frac1{\ell-1})(1+\frac1{\ell(\ell-2)})=1-\frac1\ell$ is exact. With $b_*\to\prod\ell/(\ell+1)$ and $\beta\uparrow1/4$, the ratio is $\Gamma(1+\delta)\Gamma(1-\delta)\beta^{-\delta}/4=\frac{\pi\delta}{\sin\pi\delta}4^{\delta-1}=3\pi/4$.
- **Sanity.** $K>1$, as an upper-bound sieve requires; a sieve bound below the truth would have signalled an error.

### 2.3 Equidistribution input (1) and level

- Bilinear large sieve: $\sum_{r\asymp R}\varphi(r)^{-1}\sum^*|A_\chi B_\chi|\ll PM/R+PM/\sqrt P+PM/\sqrt M+R\sqrt{PM}$, lines 64–67. This expands correctly. Summed up to $Q\le X^{1/2-\kappa}$ and over the $(\log X)^{2D+2}$ boxes, it is admissible.
- Small conductors use Siegel–Walfisz for primes in a Frobenius class twisted by $\chi\bmod r$, with $r\le(\log X)^F$. The ring class field ramifies only at $2,3$. Since $(q,6)=1$, it is disjoint from $\mathbb Q(\zeta_q)$; Minkowski's argument is correct.
- **Murty–Petersen Theorem 0.2 was checked against the source.** For a Galois $K/M$ and a class $C$, let $E$ be the fixed field of the largest abelian subgroup meeting $C$. The theorem gives level $x^{1/\theta-\epsilon}$ with $\theta=\max\{[E:\mathbb Q]-2,2\}$ and arbitrary saving $(\log x)^{-A}$, for moduli with $K\cap\mathbb Q(\zeta_q)=\mathbb Q$. Here the classes are the central singletons $\{1\},\{r^2\}$ of $D_4$, and $E=\mathbb Q(i)$, so $\theta=2$. The note's use (line 60) is correct and needs only the small-modulus consequence.
- **Level arithmetic.** The Selberg remainder uses moduli $M_0[d_1,d_2]<M_0\xi^2$ with $\xi=N^\beta$ and $\beta<1/4$, which lies inside $X^{1/2-\kappa}$. Each lcm repeats at most $3^{\omega}$ times, and the $3^{\omega(q)}$-weighted form of (1) follows by Cauchy–Schwarz with the trivial bound $X\tau(q)/q$ (line 70). Both are correct.

### 2.4 Uniformity in $h$ and limit order

- **Remainder.** The error $O_{A,T,J_0,V}(X/(\log X)^A)$ is uniform in $h$: (1) is uniform over residue classes, and $h$ enters only through which primes are omitted and which classes are admitted. Summed against the weights $H-h$, it costs $H^2X/(\log X)^A=o(N)$.
- **Main term.** The triangular mean of $b_v(h)R_T(h)$ is justified by dominated convergence. Each fixed $d$ is coprime to $M_0$; the mean over multiples of $d$ is at most $1/d$; $b_v\le1$; and $\sum r(d)/d<\infty$ (line 92).
- **Order of limits.** $N\to\infty$ comes first with $V,T,J_0,\beta,b,e$ fixed. Then $J_0\to\infty$, then $T\to\infty$ with $T\ge V$, then $\beta\uparrow1/4$, $V\to\infty$, $b\to0$ and $e\to0$. Every estimate is used only at fixed parameters, so no hidden uniformity is required (line 118 states this correctly).
- **Selection loss.** The second-moment bound $\Pr(\omega_I=0)\le(1-b)^{-\delta}/J+(1-2b)^{-\delta}-1$ (line 48) is correct. It uses the uniform ratio $S_0(X/d)/S_0(X)$ for $d\le X^{2b}$ with $2b<1/2$.

### 2.5 Matomäki–Radziwiłł and carry-flip negligibility

Theorem 1 uses MR only through the GF-29 identity $f_{0^L}-f_{1^L}=N^{-1}\sum s(m_i)g(m_i)+o(1)$, which is inherited and was not reproven here. I checked the citation against arXiv 2007.04290 (*Multiplicative functions in short intervals II*). Corollary 1.2(ii) gives $\sum(n_{i+1}-n_i)^\gamma\asymp X\delta(\mathcal N;X)^{1-\gamma}$ for $\gamma\in[1,3/2)$, under the hypothesis $\sum_{w<p\le z,p\in\mathcal N}1/p>\alpha\sum1/p-O(1/\log w)$ for $w\le z\le X^\alpha$. The note's range $1<\gamma<3/2$ and the hypothesis verification in GF-29 §1 agree with this. The last uncompleted gap is $O(\sqrt N)$, because $(6j+1)^2=12(3j^2+j)+1$ is supported (line 22). The direction of the correspondence, with $W_+$ giving zeros, is correct: a positive tail produces runs of zeros.

---

## 3. Theta cube and fourth power (Theorems 2 and 3)

- **Four squares** (lines 153). The selection $n=mp$ with $\sqrt X<p\le X^{3/4}$ is valid: each such $n$ has a unique representation because $pp'>X$. The selected set has size $\gg X$, the multiplicity is at most $\sqrt X$ (one $p$ per $m$), and the entropy count gives $O(X^{1/4})$ values with $w\le c\log X$. So $\sum w(r_4)\asymp X\log X$. Correct.
- **Three squares** (lines 155–176). Correct.
  - For squarefree $n\equiv1\bmod8$, $-4n$ is fundamental with $w=2$, so $r_3=12h(-4n)=(24/\pi)\sqrt n\,L(1,\chi_{-4n})$. This matches Pollack Prop. 3(i), which writes $h(-n)$ for the class number of $\mathbb Q(\sqrt{-n})$, and the reduced-forms check in the script.
  - The mean-square approximation (2) is correct. The truncation is $Y=\sqrt X(\log X)^3$ with Pólya–Vinogradov, the diagonal terms are those with $ij=\square$, and the off-diagonal terms are bounded by $O(Y^{1+o(1)}/X)$.
  - The positive first moment follows from local equidistribution of nonzero classes under the squarefree condition.
  - The anti-concentration argument with a moving scale $j_X$ is sound. The derivative of $B\sqrt y$ is at least $a/8$ wherever the function lies in $[a/2,2b]$, and the bound is uniform in $B$.
  - No lower bound of Siegel type is used, so no ineffectivity enters.
- **2-adic valuations** (lines 199–210). $b_p(e)=v_2(p+1)+v_2(e+1)-1$ for odd $e$, by the lifting-the-exponent lemma (LTE). For $p\nmid d$, the Pall factor is $\equiv(a+1)\mp a\equiv1\pmod2$. For $p\mid d$ the Legendre symbol vanishes. Verified numerically through $20{,}000$.
- **Hirschhorn–Sellers/Pall attribution checked against the source.** Their equation (2) is the displayed formula. Equation (4) is the referee's recursion. The authors state that (3) and (4) "were given by G. Pall".
- **Genus divisibility.** $2^{s-1}\mid h(D)$ is correct. The note's $2^{\max(0,\omega_{\rm odd}(d)-1)}$ is weaker than what genus theory gives, $2^{\omega_{\rm odd}(d)+2}\mid r_3(d)$ for $d>3$, but it is correct and suffices.
- **Theorem 3.**
  - The density-one argument (independent $p\parallel n$ events, Chebyshev) is correct.
  - The carry bound $t\,o(M)+O_t(1)$ holds, since every coefficient is less than $2^t$ and the tail is at most $(2^t-1)/(2^k-1)$.
  - The $M_2$ group argument and the transfer of empirical measures via uniform continuity are correct.
  - The column identity $\sum d_i=\sum b_i+\sum u_i$ is exact. The script checks it by explicit column addition at $k=1,2,4,30$.
- **BBCP attribution checked against the source.** p. 509: "Theorem 9.4. Almost all bits of z² are 0's; … asymptotic behavior … for an absolute constant C₀ ≈ 0.7996". BBCP then say the asymptotic density "also holds for z′²", and that "higher powers such as z³, z⁴ are likely 2-normal. Indeed, all such higher powers will involve interfering carries … r₃(n) > 0 for a limiting fraction 5/6 of all n". BBCP define $z=\sum_{n\ge0}2^{-n^2}$, so $z'=2z-1$ is correct. The note's paraphrase (line 138) is accurate and correctly labelled as conjectural.

---

## 4. Higher modular values and prime subseries (§3, Theorem 4)

- **CM identifications.** $\eta(6\tau)^4$ has weight 2 and CM by $\mathbb Q(\sqrt{-3})$; $\eta(4\tau)^6$ has weight 3 and CM by $\mathbb Q(i)$; $\eta(3\tau)^8$ has weight 4 and CM by $\mathbb Q(\sqrt{-3})$. Their supports, $\equiv1\bmod6,4,3$, coincide with the split primes. Inert vanishing and $|a(p)|\le2p^{(w-1)/2}$ hold and were checked through 3000.
- **NAF bound.** At most $\tfrac12\log_2A+O(1)$ nonzeros, since the lower positions sum to at most $2^j/3$. Correct.
- **Thresholds.**
  - Prime index: $(w-1)/(4k\log2)<1/2$ holds for $k\ge1,2,3$.
  - Euler index: multiply by $6,4,3$, giving $k\ge5,6,7$.
  - $D(E^2)$: ceiling $3/(k\log2)$, so $k\ge9$.
  - $D(\Theta_3^2)$ single digit: $1/(4k\log2)<1/2$ for all $k\ge1$.

  All were recomputed. The script certifies each with the rational lower bound $\log2>56/81$, used in the correct direction.
- **Transition cylinders and the $K_2$ criterion.** The cylinders for $01$ and $10$ make up $[1/4,3/4)$. The $K_2$ criterion (lines 230–236) is consistent with GF-27 Corollary D4.9′.

---

## 5. Required research-note contents and labels

Checked against the Phase 25 brief §5, items 1–10. **All ten are present**:

1. exact definitions: §1 line 7, §2 line 136;
2. precise statements: Theorems 1–4 and Cor. 1.1;
3. complete proofs or explicit missing steps, with the Open items marked;
4. prior art: BBCP 2004, GF-29, GF-37 and GF-27;
5. external inputs with hypothesis checks: Serre/CM, Wirsing, MR, Murty–Petersen, Pólya–Vinogradov, large sieve, Gauss, Pall;
6. evidence labels;
7. reproduction instructions, §4;
8. exact finite tests;
9. open questions, at lines 132, 224, 236 and 273;
10. objective numbers on each result.

The labels are kept separate. "Finite measurement" follows earlier phase notes and the AGENTS.md rule that finite digit statistics are measurements only. The note correctly says that cross-model review is not independent human peer review (line 273).

---

## 6. Findings

### Critical
None.

### Major
None.

### Minor

| # | Lines | Finding | Concrete fix |
|---|---|---|---|
| m1 | 14 | "Wirsing's theorem give[s] $S_\sigma\sim S/2$." Wirsing's nonnegative theorem does not by itself give the *relative* statement $\sum s(l)=o(S)$ for a signed function. | Cite a comparison theorem for real multiplicative functions dominated by $1_{\mathcal N}$, such as Hall–Tenenbaum or Halász–Wirsing; $\sum_{p:\,s(p)=-1}1/p\to\infty$ suffices. Alternatively cite the Phase 22 §4 proof, or note that Corollary 1.1 with $q=1$, $\Phi\equiv1$ reproves it. |
| m2 | 60 | "Their parameter $\max(2,[\mathbb Q(i):\mathbb Q]-2)$" leaves unsaid where $\mathbb Q(i)$ comes from. The link is a personal-archive PDF. | Write: "θ = max{[E:ℚ]−2, 2} with E = ℚ(i), the fixed field of the cyclic subgroup of order four (an abelian subgroup meeting the class)". Add the journal citation (Trans. Amer. Math. Soc., 2013; confirm volume and pages). |
| m3 | 106–110 | For finite $T$ the displayed constant contains $\prod_{\ell>T}(1-\ell^{-2})<1$, which is *smaller* than $3\pi/4$. Readers may find this puzzling. | Add one sentence. Restricting to predecessors with square part $\le V\le T$ is what permits sieving each $\ell>T$ completely. The excluded predecessors are charged separately at cost $O(tN/V)$, so only the limit $T\ge V\to\infty$ gives the stated $K$. |
| m4 | 46, 50, 72, 199, 214, 228; also 136–155 | Symbols are heavily overloaded. $e$ is a band exponent, a prime exponent, and appears in $e^{\gamma\delta}$. $D$ is a mesh exponent, a discriminant and $q\,d/dq$. $b$ is a band parameter and appears in $b_p(e)$, $b_v(h)$ and $b_i$. $M$ appears as $M_v$, $M_0$, $M_2$ and $M$ blocks. $K$, $K_2$ and $K_M$ also collide. | Rename locally, for example: band exponents $\epsilon_1<\epsilon_2$, mesh exponent $D_1$, the additive group $\mathcal M_2$, the carry total $\kappa_M$, and $\beta_p(e)$ for the valuation increments. |
| m5 | 130 | The "Conditional" label covers an unconditional equivalence, the GF-29 identity (5), as well as a conditional implication. | Split it: the equivalence is a prior Paper proof (GF-29 (5)); "Conditional" applies only to the missing approximation estimate. |
| m6 | 136 | The statement that the NAF attains $w$ has no attribution. | Cite Reitwiesner (1960), already recorded in `historical-provenance-lambert.md` Entry 5.1. |
| m7 | 155 | "The three-square theorem" is unattributed. | Add "(Legendre 1798; Gauss 1801)". |
| m8 | 180 | Theorem 3 is labelled "objectives 1–4". Its unconditional content advances objectives 2–4; objective 1 enters only as an equivalence or reduction. | Change to "objectives 2–4 (objective 1: reduction only)". |
| m9 | 188 | "squarefree kernel" usually means the radical $\mathrm{rad}(n)$, while the note means the squarefree *part*. | Replace with "squarefree part (the unique squarefree $d$ with $n/d$ a square)". |
| m10 | 222 | "Theorem 2 shows … total carry per block tend to infinity." Theorem 2 alone shows only the input mass. | Say: "by Theorem 2 together with the column identity, since the left side is at most $kM$". |
| m11 | 228 | The orders $\asymp M\sqrt{\log M}$ and $\asymp M(\log M)^{1/4}$ carry the label "Paper proof, objective 4" as if they were new, but they are inherited from GF-27 Cor. D4.15. | Label them as a prior result (GF-27 D4.15). Keep "Paper proof" for the restated $K_2$ criterion and note that it follows GF-27 Cor. D4.9′. |
| m12 | 240 | "normalized Fourier coefficient" could be read as the Deligne-normalized $a(p)/p^{(w-1)/2}$, which is not an integer. That reading would make $y_{f,k}$ and NAF weights meaningless. | Write "the (integer) Fourier coefficient of the normalized eigenform, $a_f(1)=1$". |
| m13 | 246, 259 | The terms "lower extreme interval discrepancy" and "lower discrepancy" are not defined in the note. | Use the repository notation $D^-=\liminf D_N$ from `docs/research-objectives.md` line 28. |
| m14 | 269; script 110–114 | The note says the verifier checks "the finite predecessor inequality". The script tests the charging inequality only with a *toy* selection ($b\not\equiv0\bmod3$) and a toy eligibility test ($b\not\equiv0\bmod5$), not the actual band selection or sieve. "Against an independent pentagonal convolution" is also backwards: the script builds the series by pentagonal convolution and compares it with the CM formula. | Reword: "a toy instance of the charging inequality", and "compares the CM coefficient formula with the pentagonal convolution through 6,000". Optionally add a script comment saying the same. |

**Integration note (not a defect of the note).** Theorem 1 supersedes the GF-37 constant. Before the Euler-square summary in `docs/benchmarks/arithmetic-families.toml` is updated, the result should be registered under the next GF identifier, or recorded as a strengthening of GF-37, following `docs/registry/SCHEMA.md`, and `python3 scripts/portal.py build`/`check` should then be run. No benchmark status changes, since binary simple normality of $E_2^2$ remains Open.

---

## 7. Scope of this review and residual risk

- **Not independently re-derived; inherited from earlier phases and reviewed there:** the GF-29 carry identity and gap moment; Serre's CM identification of $\eta(12\tau)^2$ and its prime-sign rule (the script checks the formula through 6,000); GF-27 Corollaries D4.9′ and D4.15.
- **Citations checked against the primary text:** Murty–Petersen Thm 0.2, Matomäki–Radziwiłł Cor. 1.2(ii), BBCP Thm 9.4 and p. 509, Hirschhorn–Sellers (2) and (4) with the Pall attribution, and Pollack Prop. 3.
- **Not checked:** Voight Thm 30.1.3 (paywalled) and the Kedlaya large-sieve page. Both support classical statements whose content I verified directly.
- **Platform.** The verifier was re-run on Windows only. The note's statement that it also passed on Hail (line 273) was not re-executed by this reviewer. No Lean or LaTeX artefacts are involved in Track C.
- **Numerical scope.** All reviewer numerics are finite certificates or finite measurements. In particular, the pair-correlation table in §2.1 is a finite measurement, not evidence for any limit.
- **Cross-model review is not independent human peer review.**
