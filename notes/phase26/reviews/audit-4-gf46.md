# Phase 26 Stage 0.2 — Priority Publication-Level Independent Analytic Audit IV (`GF-46`)

**Audited targets** (worktree at `c06c97d`, branch `research/phase-26-arithmetic-amplification`):
- [`notes/phase25/nonlinear-and-badly-approx.md`](../../phase25/nonlinear-and-badly-approx.md) (663 lines, SHA-256 `3cd8e700…9e37de`, blob `f4d4817`, identical to `HEAD`)
- [`scripts/phase25_nonlinear_approx.py`](../../../scripts/phase25_nonlinear_approx.py) (1 088 lines, SHA-256 `1ce94387…f403c`, blob `4ba1722`, identical to `HEAD`)
- [`docs/registry/GF.toml`](../../../docs/registry/GF.toml), entry `GF-46` (lines 829–839; this entry is byte-identical in `HEAD` and in the uncommitted working tree)
- [`notes/phase25/historical-provenance-lambert.md`](../../phase25/historical-provenance-lambert.md) §9 (Topic 9, blob `e114788`)
- Also inspected because it states `GF-46` conclusions: [`docs/benchmarks/arithmetic-families.toml`](../../../docs/benchmarks/arithmetic-families.toml), line 380 (text present in `HEAD`)
- Read for context only: [`notes/phase25/reviews/track-f-review.md`](../../phase25/reviews/track-f-review.md). I reconstructed every step below myself before comparing with that review. Where I agree with it, I say so; none of my conclusions rests on it.

> **Cross-model review is not independent human peer review.** This report is a machine audit by one AI model (Claude Opus 5.5) of work drafted and previously reviewed by AI models. It does not replace refereeing by human specialists in metric number theory, Fourier analysis of fractal measures and computable analysis. It cannot change any benchmark or registry status on its own.

---

## Verdict: **CONDITIONAL PASS.** The mathematics is sound, but GF-46 does **not** pass the Paper XVI gate as it stands. It passes once the four Major repairs G1–G4 in §6 are made.

| Severity | Count |
|---|---:|
| **Critical** | 0 |
| **Major** | 4 (G1 algorithm specification; G2 overstated framing; G3 classical folding lemma presented as new; G4 unverified prior art that blocks publication) |
| **Minor** | 11 |

**What survives.** I reconstructed the whole F2 chain independently. It consists of the elementary Kloosterman fourth-moment bound, the log-free modular-hyperbola rectangle bound, the block-i.i.d. Frostman measures, the Kaufman-type two-block large-sieve decay for *every* nonconstant $P\in\mathbb Q[X]$ with critical-point excision, the parameter system (2.5), the $L^2$ moment bound, the rational error budgets, the nested-cylinder selection, and the computability of both the continued fraction and the base-$b$ digits. I found **no false inequality**. Every printed constant is correct or conservative: 3√2 < 5, √2π²/6 < 5, ζ(7/4) < 2, ζ(3/2) < 2.8, √(π²/2 + π³) < 6, the "12" in $A_3$, and the thresholds 17/18 and 9/10. Hidden real-valued constants, uncertified rounding and circularity are all absent.

**What does not pass as written.**
- **G1.** The weight-search loop in Theorem 2.4, Step 3 halts with zero weights. Then $w(\mathbf a\mathbf u)=0$ and $\mathbb E[\Psi\mid I_{\mathbf a\mathbf u}]$ is undefined. This is demonstrated below and has a one-line fix.
- **G2.** The repository calls the reals "explicit" and says GF-46 "completely resolves the computable badly approximable frontier" (benchmark file, line 380). Both overstate the result.
- **G3.** The "zero-loss *c* = 1 folding identity" is the classical Folding Lemma. It is presented as an advance.
- **G4.** The literature comparison that Paper XVI needs is incomplete: Montgomery's primary text, the Hochman–Shmerkin *C*¹-image theorem, whether Kaufman or Queffélec–Ramaré already handle *C*² phases, and the mandated MathSciNet/zbMATH search.

**Montgomery's question (summary of §3).** As two independent secondary sources record it, Montgomery's 1994 question asks whether normal numbers with bounded partial quotients **exist**. That was settled by Kaufman (1980) through R. C. Baker's observation, which Montgomery's own lectures record, and for the alphabet {1, 2} by Queffélec–Ramaré (2003). GF-46 does **not** answer or strengthen that question. It addresses a *computable* form of the later remark by Queffélec (2006) that "no explicit normal numbers in BAD have been constructed yet". It does so at caps *M* ∈ {14, 42, 100}, far above the existence cap *M* = 2.

---

## 1. Independent reconstruction of the computable badly approximable construction (F2)

### 1.1 Lemma 2.1(1): elementary Kloosterman bound (note lines 178–209)

*Prime modulus.* Orthogonality gives $\sum_{a,b}|S(a,b;p)|^4 = p^2\,\#\{x_1+x_2=x_3+x_4,\ \bar x_1+\bar x_2=\bar x_3+\bar x_4\}$. I recounted the solutions:
- When $s=x_1+x_2=0$ there are $(p-1)^2$ solutions.
- When $s\ne0$, the second equation reads $s/(x_1x_2)=s/(x_3x_4)$, so $\{x_3,x_4\}=\{x_1,x_2\}$. There are $(p-1)(p-2)$ ordered pairs with $x_1+x_2\ne0$. The diagonal $x_1=x_2$ gives $p-1$ of them (*p* odd), each contributing 1. The other $(p-1)(p-3)$ pairs contribute 2 each.
- The total is $3(p-1)(p-2)$. This is confirmed **exactly** for all odd primes ≤ 37.

The orbit $(tu,t^{-1}v)$, $t\in\mathbb F_p^\times$, consists of $p-1$ distinct pairs with equal $|S|$ (substitute $y=tx$). Hence $|S|^4\le 3p^2(p-2)$ and $|S|\le3^{1/4}p^{3/4}$. The degenerate cases (*p* | gcd, or *p* dividing exactly one of *u*, *v*, which gives a Ramanujan sum of modulus 1) are handled correctly.

*Prime powers.* The gcd reduction $S(u,v;p^k)=p^rS(u/p^r,v/p^r;p^{k-r})$ is correct, since every unit mod $p^{k-r}$ has $p^r$ lifts. It costs exactly $p^{r/4}$ against $\gcd^{1/4}$. The stationary-phase identity holds with $2(k-m)\ge k$. If *p* divides exactly one of *u*, *v*, then $ux_0^2\equiv v\pmod{p^m}$ has no unit solution, so *S* = 0. Otherwise there are at most 2 square roots (odd *p*) or 4 (*p* = 2), each with $p^{k-2m}$ lifts. This gives $|S|\le c_pp^{\lceil k/2\rceil}\le c_pp^{3k/4}$.

*CRT.* I re-derived the twisted multiplicativity $S(u,v;q_1q_2)=S(u\bar q_2,v\bar q_2;q_1)\,S(u\bar q_1,v\bar q_1;q_2)$ from $x\equiv x_1q_2\bar q_2+x_2q_1\bar q_1$. The product of local constants is at most $2^{\omega(q)}\cdot2$ when $4\mid q$ and $2^{\omega(q)}$ otherwise, which is at most $2\tau(q)$. (2.1) is **correct**.

*Stress.* Over every $q\le300$ and every $u,v$, the largest value of $|S|/(2\tau g^{1/4}q^{3/4})$ is 0.2611 (float). On 16 prime powers up to $2^7$, $3^5$ and $13^2$, the largest value of $|S|/(c_pp^{\lceil k/2\rceil})$ is 0.9998. The prime-power bound is essentially tight but never violated.

### 1.2 Lemma 2.1(2)–(3): log-free modular-hyperbola rectangle bound (lines 182–231)

- **Trapezoid.** The trapezoid is (1/*L*)·1<sub>[−*L*+1, 0]</sub> ∗ 1<sub>[*a*, *a*+2*L*−1]</sub>. Its support has length 3*L* − 1 < *q* when *L* < *q*/4, so there is no wraparound, and it equals 1 on *I*. Also $\widehat B(0)=2L$, and Jordan's inequality gives $|\widehat B(u)|\le\min(2L,q^2/(4Lu^2))$.
- **Split sums.** With $U_0=\lfloor q/(2\sqrt2Ld)\rfloor$ and $\sum_{n>U}n^{-2}\le1/U$, I get $\sqrt2\,q/d+2\sqrt2\,q/d=3\sqrt2\,q/d$ when $U_0\ge1$, using $\lfloor X\rfloor\ge X/2$. When $U_0=0$ I get $\sqrt2\pi^2q/(6d)$. Both are below 5*q*/*d*. *Stress:* 70 980 checks with *q* ≤ 300, *L* < *q*/4 and *d* | *q* give a largest ratio of 0.2533 (float).
- **Fourier expansion.** Each residue occurs at most once in *I*, *J* ⊆ [1, *q*], and $B_I(x)B_J(-\bar x)$ majorizes the count. I checked this pointwise on 300 random rectangles.
- **Main term.** $\widehat B_I(0)\widehat B_J(0)\varphi(q)/q^2\le16L_1L_2/q$.
- **Axis terms.** $\widehat B_I(0)\le q$ and $|c_q(v)|\le\gcd(v,q)$ give at most 5τ(*q*) per axis. The note's 20τ(*q*) is conservative (Minor m7, harmless).
- **Off-axis.** Grouping by $d=\gcd(u,v,q)$ gives $50\tau(q)q^{3/4}\sum_{d\mid q}d^{-7/4}$.
- **Zeta bounds.** I re-certified these with exact integer roots: ζ(7/4) ≤ 1.990494 < 2 and ζ(3/2) ≤ 2.616335 < 2.8. So (2.2) and (2.3) are **correct**.
- **External inputs.** The Estermann/Weil bound $|S|\le\tau(q)\gcd^{1/2}q^{1/2}$ holds for all moduli, including powers of 2. Its largest float ratio over *q* ≤ 300 was 0.9974 (at *q* = 211, consistent with Weil's sharpness at primes). The bound is used **only** in Regime B.

### 1.3 Lemma 2.2: computable block-i.i.d. Frostman measures (lines 233–266)

- **(1)** $a_N=\lfloor(D^Q/N^P)^{1/Q}\rfloor=\lfloor DN^{-2s}\rfloor$ is exact integer arithmetic, and $p_{\mathbf u}=a_N/T<a_N/D\le N^{-2s}$. The lemma requires $a_N\ge1$ for **all** *N*; see G1.
- **(2)** The retained child fraction is exactly $Mq/((M+1)q+q')=M/(M+1+y)\ge M/(M+2)$; I verified this identity exactly on 200 random words. The other ingredients are $|I_{\mathbf u}|\le\min(q_L^{-2},\varphi^{-2(L-1)})$ and $(q_L+p_L)^{-2s}\ge2^{-2s}|I_{\mathbf u}|^s\ge2^{-2s}\varphi^{2(1-s)(L-1)}|I_{\mathbf u}|$. The hand proof at *M* = 100, *L* = 52 is correct line by line:
  - φ > 8/5 from 125 > 121;
  - *e* < 8/3 + 5/96 = 261/96 < 11/4;
  - *e*² < 121/16 < 243/32 = (3/2)⁵;
  - the reduction to 2<sup>155</sup> > 3·11<sup>10</sup>·5<sup>51</sup> = (2 · (128/121)<sup>5</sup> · (128/125)<sup>17</sup> > 3);
  - the Bernoulli factors 156/121 > 5/4 and 176/125 > 6/5.

  I re-verified each step in exact arithmetic. The true log-margin is log Σ ≥ 0.10746 (float).
- **(3)** I recomputed the three certificates **by a different code path**: direct continued-fraction recursion over all blocks, unique-value grouping, and a float-seeded integer root corrected exactly, with *D* = 10<sup>16</sup>. The results are Σ(42, 4, 18/19) ≥ 1.0185231, Σ(14, 4, 10/11) ≥ 1.0147692 and Σ(30, 2, 10/11) ≥ 1.0257434, all **exact** lower bounds with 550 612 / 8 439 / 337 distinct *N*. They match the note.
- **(4)** Even block length gives det = +1, so $T_{\mathbf a}$ is increasing and $p(\mathbf a)q'(\mathbf a)\equiv-1\pmod{q(\mathbf a)}$. The even-length expansion is unique, so (*p*, *q*) determines **a**. Further checks:
  - Submultiplicativity follows from $q(\mathbf w\mathbf u)=q(\mathbf w)q_L(\mathbf u)+q'(\mathbf w)p_L(\mathbf u)$.
  - The stopping set satisfies $R\le q<B_{M,L}R$ and $|I_{\mathbf a}|\ge1/(2q^2)$, hence $|\mathcal W(R)|\le2B^2R^2$.
  - Independence follows from the strong Markov property at a block stopping time.
  - The Frostman bound is $\mu(I)\le(2B^2+2)|I|^s$ via $R=|I|^{-1/2}$.

  All of this is **correct**. *Exact:* $B_{42,4}=3\,191\,161$, $B_{14,4}=41\,777$ and $B_{30,2}=931$, and $B_{100,52}$ has 105 digits. All satisfy $B_{M,L}\le2(M+1)^L$.
- **"Exact Frostman exponent."** The note does **not** claim an exact exponent and does not need one. *s* is a certified *upper-Frostman* exponent ($\mu(I)\le C_F|I|^s$ and $w(\mathbf a)\le q(\mathbf a)^{-2s}$), and that is all Theorem 2.3 uses. Any certified *s* lies below dim<sub>H</sub> *F*<sub>*M*</sub>. Paper XVI should say "certified Frostman exponent", never "the dimension".

### 1.4 Theorem 2.3: polynomial Fourier decay for $P_*\mu$ (lines 268–396)

The proof does **not** use van der Corput or degree-*r* stationary phase. It passes from linear to polynomial phases by (a) linearizing $\xi P(T_{\mathbf a}(y))$ at the scale $|I_{\mathbf b}|\le R_2^{-2}$ and (b) requiring $|P'|\ge\delta$ on surviving first-level cylinders. The degree enters only through $M_P$, $L_P$, $c_*$ and the excision exponent $s\theta/(r-1)$. I re-derived each step.

- **Step 2.** $|T_{\mathbf a}'|\le q^{-2}$ and $|T_{\mathbf a}''|=2q'/(q+q'y)^3\le2q^{-2}$, so $|f_{\mathbf a}''|\le(L_P+2M_P)R_1^{-2}$. The phase error is $\le\pi(L_P+2M_P)|\xi|^{-m_{\rm lin}}$. The left endpoint satisfies $y_{\mathbf b}\ge1/(b_1+1)\ge1/(M+1)$.
- **Step 3 (Gallagher–Fejér).** Averaging over $t_0$ in each bin gives $\sup|g|^2\le\Delta^{-1}\int|g|^2+2\int|g||g'|$. The Fejér step uses $H\ge4/\pi^2$ on $|t|\le T$, with transform $2T\max(1-2T|z|,0)$. The Frostman bound on the window of length $1/T$ gives $(\pi^2/2)C_FT^{1-s}w(\mathbf b)$. For $g'$, the signed weights $(y-x_0)(y'-x_0)$ are handled correctly by $|\cdot|\le\rho_{\mathbf b}^2\le1/(4\Delta^2)$. The constant is $\sqrt{\pi^2/2+\pi^3}=5.995<6$. Cauchy–Schwarz over $|\mathcal W_2|\le2B_0^2\Delta$ cancels Δ, giving (2.6).
- **Step 4 (hyperbola count).**
  - The lower bound $u_{\min}=\delta|\xi|/(4B_0^2R_1^2)$ uses $q+q'y\le2q<2B_0R_1$.
  - The endpoint shift is $\Delta'=L_P|\xi|R_1^{-4}$.
  - Under $\Delta\le u_{\min}/2$ and $\Delta'\le\min(\Delta/2,u_{\min}/4)$ we get $u'\ge u_{\min}/4$, and the window $[u',u'+2\Delta]$ follows.
  - The width bound $\sqrt A(\,u'^{-1/2}-(u'+2\Delta)^{-1/2})\le\sqrt A\,\Delta/u'^{3/2}$ gives exactly $W_0=64(M+1)B_0^3M_P^{1/2}\delta^{-3/2}\Delta R_1^3/|\xi|$.
  - $|F_q'|\le2(M+1)B_0L_P/\delta$ uses $\sqrt{u'}\ge\sqrt{\delta|\xi|}/(4B_0R_1)$ and $q\ge R_1$.
  - $\{\xi P'\ge\delta|\xi|\}$ has at most *r* components, since $P'\mp\delta$ is nonconstant of degree *r* − 1 when *r* ≥ 2 and constant when *r* = 1.
  - $K\le q\Leftarrow S_0+1\le q^{1+\rho}$; then $2+2S_0q/K\le4(S_0+1)^{1/2}q^{(1+\rho)/2}$, $K\le2(S_0+1)^{1/2}q^{(1-\rho)/2}$ and $K+r\le(r+1)K$.
  - Summing over *q* uses $\sum_{q\le X}\tau(q)\le X(1+\log X)$ and $\log(eB_0R_1)\le\log(3B_0|\xi|)$.

  Each displayed factor in the bound on $N(\Delta)$ is correct.
- **Step 5 (exponent bookkeeping).** Done symbolically by hand:
  - $\bigl(4\alpha+2\beta+\tfrac32\theta-1-2\alpha s\bigr)+(1-2\alpha)(1-s)=-m_A$;
  - $\bigl(\tfrac{3+\rho}{2}\alpha-2\alpha s+\tfrac\theta2\bigr)+(1-2\alpha)(1-s)+\tfrac{m_B}2=-\tfrac{m_B}2$.

  The log absorption $\log x\le x^\varepsilon/\varepsilon$ with $\varepsilon=m_B/2$ and $(3B_0)^{m_B/2}\le3B_0$ is valid. So is $\sqrt{2C_F}\sqrt{2\bar M_P(K_A+K_B)}\le2C_F\bar M_P(K_A+K_B)$, which yields the factor 12 in $A_3$. Finally, $|\xi|^{-\eta}\le2(1+|\xi|)^{-\eta}$ for $|\xi|\ge16$, and the trivial bound handles $|\xi|<\bar\xi_0$.
- **Thresholds.** The rule $A|\xi|^{-\gamma}\le1\Leftarrow|\xi|\ge\max(1,\lceil A\rceil)^{\lceil1/\gamma\rceil}$ was verified exactly on 3 000 random rational pairs. I re-matched each $X_i$ to its inequality: $X_1\leftrightarrow\Delta\le u_{\min}/2$ ($\gamma_1$), $X_2\leftrightarrow\Delta'\le\Delta/2$ ($\gamma_2=4\alpha+2\beta-1$), $X_3\leftrightarrow\Delta'\le u_{\min}/4$ ($\gamma_3=2\alpha-\theta$), $X_4\leftrightarrow S_0+1\le R_1^{1+\rho}$ ($\gamma_4$) and $X_5\leftrightarrow\Delta\le U$ ($\gamma_5$). Every $\gamma_i>0$ follows from (2.5).

**Conclusion:** Theorem 2.3 is **correct** with the stated rational $\bar\xi_0(P)$ and $\bar C(P)$. It also holds for $X-S$ with *S* irrational, because the constants depend only on $|c_j|$ for *j* ≥ 1.

### 1.5 Critical-point excision: no circularity, and positivity is untouched

The covering $\{|P'|<\delta\}\subseteq\bigcup_i(\operatorname{Re}\rho_i-\rho,\operatorname{Re}\rho_i+\rho)$ follows from $|P'(x)|=rc_*\prod|x-\rho_i|$ and $|x-\operatorname{Re}\rho_i|\le|x-\rho_i|$. It is valid for repeated and complex roots. At most 2(*r* − 1) endpoints each lie in at most two closed cylinders, giving at most 4(*r* − 1) boundary cylinders. The bound $(rc_*)^{-s/(r-1)}\le\max(1,1/(rc_*))$ uses $0<s/(r-1)<1$.

**There is no circularity, and no positivity issue across the countably many *P*.** The excision happens *inside* each Fourier estimate, for each fixed (ξ, *P*). Its only parameters are δ = |ξ|<sup>−θ</sup> and *c*<sub>∗</sub>. It never removes anything from the support of μ, and the roots are never computed. μ is fixed once from (*M*, *L*, *s*), independently of every *P*. The selected point *x* is then controlled by the single potential Ψ, which encodes all *P* at once. No simultaneous excision over all *P* is ever needed, so the question "does excision preserve positivity for all *P* simultaneously" does not arise. Positivity of the selected cylinder masses depends only on $p_{\mathbf u}>0$; see G1.

### 1.6 Parameter feasibility for *M* = 100, 42, 14

- **Exact.** I checked all five inequalities of (2.5), the three derived inequalities ($\gamma_1,\gamma_4,\gamma_5>0$) and their θ = 0 versions for *r* = 1, for the three printed triples. The margins are (1/50, 37/2000, 1/500), (1/125, 959/76000, 33/38000) and (1/50, 177/11000, 17/5500), matching the note. The resulting η values are:

  | Measure | η for *r* = 1 | η for *r* = 2 | η for *r* = 10 |
  |---|---|---|---|
  | *M* = 100 | 1/1600 | 1/2000 | 19/180000 |
  | *M* = 42 | 17/60800 | 33/152000 | 1/19000 |
  | *M* = 14 | 9/8800 | 17/22000 | 1/4950 |

- **Thresholds are exact, not artifacts.** Eliminating β and θ by hand gives $2(1-s)/(1-\rho)<\alpha<s-\tfrac12$. A linear program for the largest common margin of (2.5) gives −9.47·10<sup>−7</sup>, 0 and +9.47·10<sup>−7</sup> at *s* = 17/18 − 10<sup>−6</sup>, 17/18 and 17/18 + 10<sup>−6</sup> (ρ = 3/4). It gives the analogous values at 9/10 (ρ = 1/2).
- The midpoint formula satisfies every inequality exactly for *s* = threshold + 10<sup>−*k*</sup>, *k* = 2, …, 11, in both regimes. The claim 4α + 2β > 6/5 holds because α > (*s* − 1/2)/2 > 1/5.
- **Caps are not sharp** (Minor m1). These are float measurements, not certificates:
  - Σ(41, 4, 18/19) = 1.0142 and Σ(40, 4, 18/19) = 1.0097. The smallest *L* = 4 cap at *s* = 18/19 is *M* = 38 (Σ = 1.00006). At *s* = 17/18 + 10<sup>−4</sup> it is *M* = 34.
  - Regime B reaches *M* = 12 at *L* = 4 (*s* = 9/10 + 10<sup>−4</sup>) and *M* = 11 at *L* = 6.
  - The hand-analytic route is feasible for every *M* ≥ 43 at *s* = 19/20 with *L* ≈ 400.
  - Σ(13, 4, 10/11) = 0.976 < 1, so *M* = 14 is minimal only for *L* = 4 at *s* = 10/11.

### 1.7 Effective moment and Davenport–Erdős–LeVeque/Weyl variance bound (lines 415–423)

- $h(b^n-b^m)\ge b^{n-1}\ge2^{n-1}$ for $m<n$, with *n* pairs per *n*. Together with $\sum n x^{n-1}=(1-x)^{-2}$ this gives $\int|S_N|^2d\mu\le K(P)/N$, **uniformly** in *b* and *h*.
- The bounds $1-e^{-x}\ge x/(1+x)$ (from $e^x\ge1+x$) and log 2 > 2/3 (from *e*² < 8, proved by hand) give the rational $\bar K_e>K(P_e)$.
- $J_e=\lfloor2^{e+3}\bar K_e\rfloor+1$ and $\sum_{j\ge J}j^{-2}\le2/J$ give $\int\Psi\,d\mu<1/4$.
- Square-subsequence interpolation is bounded by 4/*j*.

All **correct**. The method yields **no effective discrepancy rate** for *P*(*x*): $\Psi(x)\le1$ bounds the *number* of bad *j* but not their location. Paper XVI must not attach a rate (Minor m10).

### 1.8 Rational error budgets: no hidden non-effective constant or uncertified rounding (lines 438–445)

| Budget | Mechanism | Verdict |
|---|---|---|
| Tail in *e* (δ/4) | $\sum_{e>E}2\bar K_e/J_e<2^{-E-2}$, divided by the exact $w(\mathbf a)$ | rational ✓ |
| Tail in *j* (δ/4) | $2\sum_{e\le E}\bar K_e/(Jw(\mathbf a))$ | rational ✓ |
| Discretization (δ/6) | Lipschitz bound $\lvert(\lvert S\rvert^2)'\rvert\le4\pi hM_Pb^{j^2}\le16hM_Pb^{j^2}$; sub-cylinder length $\le\varphi^{-2(dL-1)}<(5/8)^{2(dL-1)}$; total over 𝓕 | rational ✓ |
| *S*-truncation (δ/6) | $\lvert S-S_{N_S}\rvert<b^{-N_S}$ (ℓ<sub>*n*</sub> ≥ 2); Lipschitz bound in *S* with *M*<sub>*P*</sub> = 1 | rational ✓ |
| Trigonometry (δ/6) | Machin π̃ to ε/4; Taylor degree chosen by the rational test $7^{2N+1}/(2N+1)!<\varepsilon/2$, which forces *N* ≥ 9 and so also covers the cosine remainder; $\lvert S̃\rvert^2$ within 6ε; $\varepsilon=\delta/(36N_{\mathcal F})$ | rational ✓ |

The one-sided truncation (in [0, δ/2)) plus the two-sided remainder (< δ/2) gives |Ê − 𝔼| < δ. Every decision is an exact rational comparison. The quantities $\bar K_e$, $\bar\xi_0(P)$ and $\bar C(P)$ are explicit rationals. I wrote an independent implementation, and it reproduces the repository's (η, ξ̄₀, C̄, K̄) **exactly** on the three *M* = 30 sample polynomials. On six polynomials up to degree 7 for each certified measure, the sizes are log<sub>10</sub> ξ̄₀ ≈ 101 (*M* = 14), ≈ 222 (*M* = 42) and ≈ 3 133 (*M* = 100). In each case $2\bar K_e/J_e<2^{-e-2}$ holds exactly for *e* = 1, 5, 40.

("Packet digits" in the brief refers to F1. For F2, the precision needed per step is δ<sub>*m*</sub> = 2<sup>−*m*−4</sup>, with *J* ≈ 2<sup>*m*</sup>Σ*K̄*/*w*(**a**) and refinement depth ≍ *J*² log *b*. The cost is doubly exponential in *m*, as §7 Q4 of the note concedes.)

### 1.9 Nested-cylinder selection: averaging, no dead ends, and the zero-weight defect (lines 438, 447)

- **Averaging.** $\sum_{\mathbf u}p_{\mathbf u}\mathbb E[\Psi\mid I_{\mathbf a\mathbf u}]=\mathbb E[\Psi\mid I_{\mathbf a}]<B_m$, so some child has conditional expectation below $B_m$. Since $B_{m+1}-B_m=4\delta_m$, the test $\hat E<B_{m+1}-\delta_m$ passes for that child and certifies $\mathbb E<B_{m+1}$.
- **The expectation does not need to shrink, and does not.** The invariant $\mathbb E[\Psi\mid I_m]<B_m<1$ is allowed to creep up to 1, and that is all Step 4 uses.
- **No dead ends.** Every child word lies in $\{1,\dots,M\}^L$, so the process never leaves *F*<sub>*M*</sub>.
- **Limit.** The limit passage through the continuous truncations $\Psi_T$ (first *m* → ∞, then *T* → ∞, by monotonicity) is valid.

**But see G1.** As written, the weight search in Step 3 can produce children with $p_{\mathbf u}=0$, and then "compute $\hat E(\mathbf a\mathbf u)$ for every child" divides by zero.

### 1.10 Turing computability of the continued fraction and of the base-*b* digits

- The machine outputs blocks **u**. Hence the cylinders satisfy $|I_m|\le\varphi^{-2(mL-1)}$ and *x* is a computable real with an explicit modulus.
- *x* is irrational: it is the limit of an infinite continued fraction, never a rational endpoint.
- For each $P\in\mathbb Q[X]$, *P*(*x*) is computable and normal, hence never a *b*-adic rational. So the digit-extraction machine halts on every digit. This is a fixed machine whose halting is guaranteed by the theorem, which is standard. The same holds for {*x* − *S*} in part (3).
- $q\|qx\|>1/(M+2)$ follows from $q_n|q_nx-p_n|=1/(\alpha_{n+1}+q_{n-1}/q_n)$ and Lagrange's best approximation. *Exact stress:* the minimum over tested *q* is 0.26795 for *M* = 2 (bound 0.25), 0.06275 for *M* = 14 (bound 0.0625) and 0.02274 for *M* = 42 (bound 0.02273).
- In (3), *Z* = *x* − ⌊*x* − *S*⌋ has exact shifted-prefix denominator $\prod_{n\le N}\ell_n$, because the primes are distinct and coprime to *b*. ✓

---

## 2. Item 2: the *d* = *r* local limitation, the exact IFF threshold, and *c* = 1 folding

**Theorem 1.1 (*d* = *r* local single-packet limitation).** Parts (1)–(2) are correct. That includes the split into the cases *e* − *m* < *h* (integer perturbation) and *e* − *m* ≥ *h* (shift by a multiple of *p*<sup>*h*</sup>).

In (3), the translated grid of spacing $p^{-(e-h)}$ meets every *b*-adic cylinder of length at least $p^{-(e-h)}$. The 0<sup>*L*</sup> bound $\max_m[(L-m+1)/L-b^{-m}]$ is correct: I rechecked 47/72 (*b* = 2, *L* = 9, *m* = 3) and 7/12 (*L* = 6, *m* = 2). I also re-derived the comparison bound (*m* + 1)/*L* by enlarging and shrinking the interval by 1/*L* and charging the *m* − 1 uncontrolled shifts.

The statement is now honestly scoped. It is a **local non-determination** result. It constructs no globally consistent counter-model and does not bear on *D*<sup>+</sup> < 1. Its Objective-4 weight is slight. Paper XVI should present it as a remark, or drop it from Paper XVI altogether (Minor m11).

**Theorem 1.3(1) (exact IFF threshold r<sub>min</sub>/(Q′p<sup>e</sup>)).** I re-derived the threshold from scratch:
- The set $\{kB^M/Q-N\}$ equals $(1/Q')\mathbb Z$.
- So the least admissible tail is (least positive residue of $-Q'\tilde A$ mod $p^e$)/($Q'p^e$).
- For *h* ≥ 1, the lifts sweep the coset $-Q'A_0+g_0p^h\mathbb Z$. For *h* = 0, they give $p^{\min(v,e)}=g_0$.

The characterization is **correct**. *Exact brute force that never uses Q′:* a direct search over all *N* mod *B*<sup>*M*</sup> and all admissible lifts covered 1 530 configurations (*b* ∈ {2, 3, 5, 6, 10}, *p* ∈ {3, 5, 7}, *B*<sup>*M*</sup> ≤ 800, *e* ≤ 2, 0 ≤ *h* ≤ *e*, ten values of *Q*), 941 of them with gcd(*Q*, *B*<sup>*M*</sup>) > 1. It found **0 mismatches**. The result is elementary, a coset computation, and should not be advertised as a principal advance.

**Theorem 3.1(1) (*c* = 1 folding).** I re-derived both canonical expansions:
- $[0;a_1,\dots,a_n,d-1,1,a_n-1,a_{n-1},\dots,a_1]$ when ε = (−1)<sup>*n*</sup>;
- $[0;a_1,\dots,a_n-1,1,d-1,a_n,\dots,a_1]$ when ε = −(−1)<sup>*n*</sup>, via the non-canonical tail $(a_n-1,1)$.

The terminal digit is $a_1-1\ge2$ exactly when *n* = 1 and ε = −1. *Exact:* 31 900 folds were checked: all canonical *u* < 1/2 with *q* ≤ 60, all 2 ≤ *d* ≤ 30, and both signs.

The identity is **correct, and it is the classical Folding Lemma** (Mendès France 1973; van der Poorten–Shallit 1992), in its regularized form $[\dots,x,-a_n,\dots,-a_1]\to[\dots,x-1,1,a_n-1,a_{n-1},\dots,a_1]$. See G3. The *c* ≥ 2 bound of 3.1(2) is also correct: Lagrange's bound applied at denominator $cl_i$ gives the strict −1.

---

## 3. Specialist literature comparison: Montgomery's question and prior art

### 3.1 What Montgomery asked, as recorded by two independent secondary sources

- **Queffélec**, *Old and new results on normality*, IMS Lecture Notes 48 (2006), pp. 232–233 (arXiv:math/0608249):
  > "Montgomery [29] in his book posed the following problem: Does there exist normal numbers with bounded partial quotients ? In 1980, Kaufman [18] … obtained the following deep result. Theorem 4.3 (Kaufman). For N ≥ 3 F(N) carries a probability measure μ such that |μ̂(t)| ≤ c|t|<sup>−η</sup> … When Kaufman's paper appeared, R.C. Baker observed in [29] that combining the above result with a corollary of the Davenport–Erdös–Leveque's theorem … yields the existence of normal numbers in BAD. … Theorem 4.4. If dim<sub>H</sub>(F(A)) > 1/2, F(A) supports a Kaufman's measure and contains infinitely many normal numbers. In particular there exist infinitely many normal numbers with partial quotients ∈ {1, 2}. Note that no explicit normal numbers in BAD have been constructed yet."

  Here [29] is Montgomery, *Ten Lectures …*, CBMS **84** (1994), MR1297543.
- **Jordan–Sahlsten**, arXiv:1312.3619v3, p. 3 (Math. Ann. 364, 2016):
  > "For N ≥ 3 this was already settled by Baker, who pointed out this could be deduced from Kaufman's result (see for example the lecture notes by Montgomery [26]), but for B<sub>2</sub> the Kaufman measure constructed by Queffélec–Ramaré finally settled this problem for all N ≥ 2."

I could not access the primary text of Montgomery (1994), so I do not quote it here. Both secondary sources agree on two points. **Montgomery's question is an existence question**, and it was **already answered**: by Kaufman's measure through Baker's observation, which Montgomery's lectures themselves record, for *N* ≥ 3, and by Queffélec–Ramaré (2003) for *N* = 2. The open residue in the literature is the *explicit-example* problem, which Queffélec stated in 2006.

### 3.2 What existing results already give, including at cap *M* = 2 (all non-effective)

| Source | Conclusion | Bounded cap | Polynomial images | Computable |
|---|---|---|---|---|
| Kaufman 1980 + Baker (in Montgomery 1994) | Fourier decay on *F*<sub>*N*</sub>, *N* ≥ 3 ⇒ μ-a.e. absolutely normal | *N* ≥ 3 | not stated in the sources I read (G4c) | no |
| Queffélec–Ramaré 2003 | Fourier decay when dim *F*(*A*) > 1/2 ⇒ μ-a.e. normal; includes {1, 2} | **2** | not verified (G4c) | no (decay rates parametrized by dim; constants not shown computable) |
| Jordan–Sahlsten 2016, Cor. 1.6 | Gibbs measures of dim > 1/2 on *B*(*A*): (*s*<sub>*k*</sub>*x*) u.d. for **every** strictly increasing integer sequence | **2** | no (linear phases; Lemma 6.4 is a *C*² stationary-phase lemma applied to ξ(*T*<sub>**a**</sub> − *T*<sub>**b**</sub>)) | no |
| Hochman–Shmerkin 2015, Thm 1.12 (as quoted by J–S) | every Gibbs measure on *B*(*A*), *A* finite, is *n*-normal for every *n* | any finite *A*, \|*A*\| ≥ 2 | §4 and Phase 24 GF-39 assert *C*¹-image invariance; **not re-verified here** (G4b) | no |
| Sahlsten–Stevens; Algom–Rodriguez Hertz–Wang; Baker–Banaji | polynomial Fourier decay for nonlinear self-conformal measures and nonlinear pushforwards | potentially 2 (hypotheses to check) | plausibly (G4c) | constants not made explicit |

**Consequence at *M* = 2.** The QR measure with DEL already gives absolutely normal numbers with partial quotients in {1, 2}. If the Hochman–Shmerkin *C*¹-image statement holds as the repository's earlier notes assert, then (restricting to monotone pieces of *P*) μ-a.e. *x* ∈ *F*<sub>2</sub> has *P*(*x*) absolutely normal for every nonconstant *P* ∈ ℚ[*X*]. The **existence** part of GF-46's conclusion would then be known at the optimal cap *M* = 2. GF-46's conclusion is genuinely new only in being **computable**.

### 3.3 Computable-normality literature

- **Sierpiński and Becher–Figueira** (TCS 270, 2002, 947–958): a computable absolutely normal number.
- **Turing**, completed by Becher–Figueira–Picchi: an algorithm in double-exponential time.
- **Becher–Heiber–Slaman** (2013): polynomial time.
- **Alvarez–Becher** (arXiv:1510.02004): computability and discrepancy of Levin's construction.
- **Scheerer** (arXiv:1701.07979): absolutely normal and continued-fraction normal. The ambient set is Ω = {*a*<sub>*i*</sub> ≤ *A*·2<sup>*i*</sup> − 2}, of positive Lebesgue measure (his Prop. 4.1), so the partial quotients are unbounded.
- **Becher–Yuhjtman** (arXiv:1704.03622): an improved version of Scheerer's construction.

None of these produces a bounded-partial-quotient example. Every one works in Lebesgue or Gauss measure. GF-46's selection step is the same Sierpiński–Turing–Becher–Figueira paradigm, namely a computable point in a set of positive measure carved out by a computable *L*² potential. It is transplanted to a computable **singular** measure on *F*<sub>*M*</sub>. Once a computable measure with computable decay constants is in hand, this step is routine. The substantive inputs are (i) exact rational block weights and (ii) explicit rational majorants for the decay of every polynomial pushforward.

I did not locate "Alvarez–Becher–Mereb" (listed in the brief) and do not assess it. I did not re-verify Lutz–Mayordomo. Neither my searches nor the repository's located a prior **computable** badly approximable normal number. That is not proof of priority.

### 3.4 What is genuinely novel in GF-46 (provisional) and what must not be overstated

**Defensible novelty (provisional, pending G4).**
1. A Turing-computable real with all partial quotients ≤ *M* (*M* = 14 with Weil–Estermann; 42 with no external input and a finite certificate; 100 with neither), all of whose images under nonconstant rational polynomials are absolutely normal.
2. A Kaufman-type Fourier-decay bound for $P_*\mu$ with **fully explicit rational** exponent and constants, valid at certified Frostman exponent *s* > 17/18 (elementary) or *s* > 9/10 (Weil–Estermann).

This addresses a **computable version of Queffélec's 2006 explicit-example remark**. It does **not** address Montgomery's existence question, which is classical.

**Must NOT be stated in Paper XVI** (each item is required for the gate):
- that GF-46 "resolves", "answers" or "strengthens" Montgomery's problem, or that it gives "the first normal number with bounded partial quotients";
- "explicit" without qualification, since the construction is computable in principle only. For *M* = 100 the weights alone require enumerating 100<sup>52</sup> blocks, ξ̄₀ ≈ 10<sup>3133</sup>, and the running time is doubly exponential;
- "completely resolves the computable badly approximable frontier". Lowering the cap to *M* = 2 is open, and the registry's own `scope` says so;
- that the nonlinear Fourier-decay mechanism is new. Only the explicit constants are;
- that *M* = 42 or *M* = 14 is sharp or optimal for the method (Minor m1);
- any effective discrepancy rate for *P*(*x*) (Minor m10);
- that the *c* = 1 folding identity is new (G3);
- polynomial-time or practical computability.

---

## 4. Computational verification

**Repository verifier.** `python -B scripts/phase25_nonlinear_approx.py` (Windows, Python 3.13.13, no WSL) gave **exit 0** in 8.3 s, ending with `All Phase 25 Track F exact finite certificates passed.` The printed counts match §6 of the note: 810 lifts / 10 530 sites / 45 360 pairs, 68 grids, collapse [1, 2, 4, 11, 31], 2 322 iff configurations, drops at 783 … 1268, 367 split sums (maximum 0.4952), Σ ratios 1.018523 / 1.014769 / 1.025743, majorants for *r* = 1, 2, 3, 1 780 + 4 272 folds, and 6 + 117 pole-depth checks. Exact and float checks are honestly separated.

**Independent adversarial stress suite.** I wrote it from scratch; it does not import the verifier, except for one final cross-check of the majorant function. It is not committed and lives in the session scratchpad as `audit4_stress.py`, plus `minM.py` and `dsearch.py`. It exited 0 in 12.3 s.

| Test | Type | Result |
|---|---|---|
| Kloosterman (2.1) on all *q* ≤ 300 and all *u*, *v* | float | max ratio 0.2611 |
| Estermann bound on all *q* ≤ 300 | float | max ratio 0.9974 (*q* = 211) |
| Fourth-moment count 3(*p* − 1)(*p* − 2), *p* ≤ 37 | exact | all pass |
| Prime-power stationary phase, 16 prime powers | float | max 0.9998 (tight, never violated) |
| Trapezoid split sums (70 980 cases) | float | max 0.2533 < 1 |
| Majorant pointwise ≥ count (300 rectangles) | exact | pass |
| ζ(7/4) < 2 and ζ(3/2) < 2.8 | exact | 1.990494 and 2.616335 |
| Σ certificates by an independent code path | exact | ≥ 1.0185231 / 1.0147692 / 1.0257434 |
| *M* = 100 hand steps | exact | all pass; log-margin 0.10746 |
| Retained-mass identity | exact | 200 / 200 |
| (2.5) margins and LP thresholds | exact / LP | thresholds exactly 17/18 and 9/10 |
| Majorant pipeline, 18 (measure, *P*) pairs | exact | *J*<sub>*e*</sub> inequalities pass; identical to the repository on *M* = 30 |
| Theorem 1.3(1) direct search (1 530 configurations) | exact | 0 mismatches |
| Folding Lemma (31 900 folds) | exact | pass |
| *q*‖*qx*‖ > 1/(*M* + 2) | exact | pass for *M* = 2, 3, 14, 42 |
| Monte Carlo \|∫*e*(ξ*P*) *d*μ\|, *M* = 30 measure | float | decays from 0.11 (*x*² − *x*/3, ξ = 10²) to ≤ 0.006 at ξ = 10<sup>5</sup>; a sanity measurement, not evidence |
| **Weight search of Theorem 2.4 Step 3** | exact | **halts by *D* ≤ 14 200 with 461 of 900 weights zero** (G1) |

Monte Carlo and the other float entries are measurements only. The certified bounds are vastly weaker (η ≈ 10<sup>−3</sup> to 10<sup>−4</sup>).

---

## 5. Classified findings

### Critical
None. No inequality, constant or logical step of GF-46 fails.

### Major

**G1. The weight search in Theorem 2.4, Step 3 yields zero weights, and the selection then divides by zero.** *Location:* note line 438. *Defect:* "compute the exact rational block weights $p_{\mathbf u}$ … by searching *D* = 1, 2, … until $\sum_{\mathbf u}a_{N(\mathbf u)}>D$." This stopping rule does not enforce Lemma 2.2(1)'s requirement $a_N\ge1$ for every *N*, and $\sum a_N>D$ first holds long before $D\ge\max N^{2s}$.

*Reproduction (M = 30, L = 2, s = 10/11):* the search halts by *D* ≤ 14 200 (a scan bound; the true first *D* is no larger). At that point **461 of the 900** blocks have $a_N=0$. Positivity of all weights requires *D* ≥ 250 087. For *M* = 42, a heuristic estimate puts the stopping *D* near (block count)/(Σ − 1) ≈ 3.1·10<sup>6</sup>/0.0185 ≈ 2·10<sup>8</sup>, while positivity needs $D\ge B_{42,4}^{36/19}\approx2\cdot10^{12}$.

The algorithm then computes $\hat E(\mathbf a\mathbf u)$, which involves $w(\mathbf a\mathbf u)^{-1}$, "for every child". The claim "$p_{\mathbf u}\in\mathbb Q_{>0}$" is not delivered. The theorem is unaffected: the repository certificate uses *D* = 10<sup>18</sup>, where all weights are positive. But the algorithm **as specified** is ill-defined.

*Fix (either works):*
- (a) search only *D* with $D^Q\ge B_{M,L}^P$, an exact integer test;
- (b) restrict children to $p_{\mathbf u}>0$, and state that μ lives on the corresponding subshift.

**G2. "Explicit" and "completely resolves" overstate the result. Montgomery framing must be fixed before Paper XVI.** *Locations:*
- Registry `GF-46` `statement`: "explicit computable real numbers".
- [`docs/benchmarks/arithmetic-families.toml`](../../../docs/benchmarks/arithmetic-families.toml) line 380 (in `HEAD`): "GF-46 **completely resolves** the computable badly approximable frontier … constructing **explicit** computable reals". This contradicts the registry `scope` ("lowering the computable badly approximable cap to M = 2 remain[s] open").
- Note §4: it never cites the Queffélec (2006) explicit-example remark, Baker's observation, or the fact that Montgomery's existence question is classical.

*Fix:*
- Replace "explicit computable" by "computable (Turing-computable; in-principle algorithm)".
- Replace "completely resolves the computable badly approximable frontier" by "constructs computable badly approximable polynomial-absolutely-normal reals at caps *M* ∈ {14, 42, 100}; the computable cap *M* = 2 remains open".
- Add to §4 the §3.1 quotations and the novelty statement of §3.4.

**G3. The classical Folding Lemma is presented as an advance.** *Locations:* registry `statement` (3), "Exact zero-loss c = 1 continued-fraction folding identity", inside a `principal = true` result; §0 table (Theorem 3.1); §8, "Theorems 3.1–3.2 eliminate folding losses at *c* = 1". Theorem 3.1(1) is exactly the regularized Folding Lemma (Mendès France 1973; van der Poorten–Shallit 1992). §4 attributes "exact reciprocal folding" correctly, but the theorem header, table, registry and §8 do not.

*Fix:* label Theorem 3.1(1) "classical Folding Lemma (restated with max-partial-quotient bookkeeping)". Drop it from the principal registry statement, or mark it as classical there. Keep only 3.1(2) as possibly new, subject to a literature check against Mendès France 1973.

**G4. Prior-art verification that blocks Paper XVI.**
- (a) Quote Montgomery (1994) from the primary text, with page, before any statement about "Montgomery's question". I could not access it.
- (b) Give the theorem number and hypotheses of the Hochman–Shmerkin *C*¹-image statement that §4 and GF-39 rely on. These determine exactly what is known at *M* = 2.
- (c) Check whether Kaufman (1980, §4–5) or Queffélec–Ramaré (2003) already state decay for $\varphi_*\mu$ with φ ∈ *C*² and φ′ ≠ 0. Jordan–Sahlsten note that Kaufman's stationary-phase lemma holds for any *C*² ψ with |ψ′| ≥ *r* and |ψ″| ≤ *R*. Also check whether Baker–Banaji, Algom–Rodriguez Hertz–Wang or Sahlsten–Stevens cover the Gauss-map IFS with digits {1, 2} under polynomial maps.
- (d) Perform the MathSciNet/zbMATH search that `historical-provenance-lambert.md` Entry 9.3 makes mandatory (Becher, Slaman, Bugeaud, Scheerer, Madritsch, Levin, Kristensen, Figueira, 2015–2026), and record the result.

### Minor
1. **m1.** Lemma 2.2(3) is titled "Sharp finite integer certificates", but the certificates are not sharp. At *L* = 4, *M* = 40 already gives Σ = 1.0097 > 1 at *s* = 18/19, and the floor is *M* = 38 (34 near 17/18). Regime B reaches *M* = 12 (*L* = 4) or 11 (*L* = 6). The hand route works for *M* ≥ 43. Remove "sharp". Optionally lower the caps, with exact certificates.
2. **m2.** §8 says "optimal badly approximable Diophantine rate". The order $q\|qx\|\asymp1$ is optimal, but the constant 1/(*M* + 2) is not. Reword.
3. **m3.** Registry `inputs` and `statement` say "Weil Kloosterman bound" for *M* = 14. Weil (1948) covers prime moduli; the all-moduli bound used is Estermann (1961). Name both.
4. **m4.** Registry `scope` says "Written proofs checked by exact integer/Fraction certificates". The certificates check finite ingredients, not the analytic proofs. Reword.
5. **m5.** "hand-checkable block weight" (registry): only the *existence* of weights is hand-checkable. State that the algorithm is in-principle only (100<sup>52</sup> blocks, ξ̄₀ ≈ 10<sup>3133</sup>), as §7 Q4 of the note already does.
6. **m6.** §4 dates Becher–Yuhjtman "(2024)". The preprint is arXiv:1704.03622 (2017). Verify the journal and year.
7. **m7.** In Lemma 2.1(2), the axis terms are at most 10τ(*q*), since $\widehat B(0)\le q$. 20τ is harmless slack.
8. **m8.** In Theorem 2.4(3), *x* depends on the chosen radix *b* through *S*. All radices can be handled at once by enumerating $(X-S_b,b,h)$ for every *b*. Optional.
9. **m9.** Theorem 2.3's η also depends on the chosen (α, β, θ), not only on (*r*, *s*, ρ). Say "for the stated choice".
10. **m10.** No effective discrepancy rate for *P*(*x*) follows from Ψ(*x*) ≤ 1 (§1.7). State this explicitly, and keep the Objective 1 claim to plain normality.
11. **m11.** Paper XVI scope: Theorems 1.1–1.3 and 3.2 (the F1 and F3 material) are of a different character and much lower relevance to the F2 result. Their Objective-4 weight is slight. Recommend excluding them from Paper XVI, or confining them to an appendix.

---

## 6. Gate decision for Proposed Paper XVI

**GF-46 does not pass the gate as it stands. It passes, conditionally, after the following exact repairs:**

1. **G1.** In Theorem 2.4, Step 3, either search only *D* with $D^Q\ge B_{M,L}^P$, or restrict the selection to children with $p_{\mathbf u}>0$. Add a verifier assertion that all weights are positive at the *D* actually used, and a regression check reproducing the 461/900 zero-weight case.
2. **G2.** Remove "explicit" and "completely resolves" from the registry statement and from `arithmetic-families.toml` line 380. Add the Montgomery/Queffélec/Baker/Kaufman/Queffélec–Ramaré/Hochman–Shmerkin framing and the provisional novelty statement of §3.4 to the note's §4 and to the paper.
3. **G3.** Label Theorem 3.1(1) as the classical Folding Lemma throughout the theorem header, the §0 table, §8 and the registry.
4. **G4.** Complete items (a)–(d): the primary-source Montgomery quotation, the HS theorem number, the Kaufman/QR *C*²-phase check, and the MathSciNet/zbMATH search. Then adjust the novelty statement to the findings.

The Minor items should be fixed in the same pass but do not block the gate. **No benchmark status may change** as a result of this audit. BC-01…BC-50 are unaffected, since GF-46 concerns constructed numbers, not classical constants.

---

## 7. Residual scope

This audit establishes only the following:
- the analytic F2 chain of GF-46 at the audited hashes contains no false step;
- its finite certificates are reproducible by an independent code path;
- the four Major items above must be repaired before publication.

It does not establish priority. It did not consult Montgomery's primary text or the full texts of Kaufman (1980), Queffélec–Ramaré (2003), Hochman–Shmerkin (2015), Baker–Banaji, Algom–Rodriguez Hertz–Wang or Sahlsten–Stevens. It makes no assessment of Theorem 3.2 beyond spot checks: I confirmed ν<sub>3,1,3</sub> = 3, ν<sub>3,2,3</sub> = 2 and ν<sub>4,2,3</sub> = 4 by hand. Every float figure in this report is a measurement, not a proof certificate. Nothing was committed, and no repository file other than this report was modified.

**Cross-model review is not independent human peer review.** This verdict is an automated cross-model audit. Human referees must confirm it before Paper XVI is presented as refereed work.
