# Independent Cross-Provider Referee Review: Phase 26 Track A (`A1`–`A7`)

- **Reviewed targets:**
  - `notes/phase26/toeplitz-determinants-and-uniformity.md`
  - `scripts/phase26_toeplitz_uniformity.py`
- **Review mode:** Independent cross-provider adversarial mathematical audit (attempting to invalidate every theorem, constant, proof step, and computational certificate).
- **Disclaimer:** **Cross-model review is not independent human peer review.**
- **Verdict:** **REVISE** (0 Critical, 2 Major, 9 Minor).

---

## Executive Summary

The core mathematical architecture of Phase 26 Track A (`A1`–`A7`) is **sound and well-executed**. Every flagship result—the sharp Gram inequality and equality characterization (`A1.1`), the orbit-vector Verblunsky factorization and monotone normalized root (`A1.2`), the self-contained outer-function proof of constant-density Szegő–Kolmogorov–Krein and atom-proof determinant-to-uniformity transfer (`A2`), the elementary bounded-convergence proof of $a(\mu) = \mu(\mathcal{N}_b)$ (`A2.6`), the optimal-rate characterization $a_*$, biased-Bernoulli separation, and de Bruijn no-universal-schedule theorem (`A3`), the compound-symmetric and Champernowne–zero-run sharpness controls (`A4`), the exact Koksma constant $2$ (`A5.1`), the genuinely linear-in-$(r-1)$ Toeplitz operator-norm bound $\pi|h|(r-1)D_N$ (`A5.2`), the random-point law (`A5.5`), the affine regularization limit, all-radix $2 \times 2$ characterization of $D^+ < 1$ and $K_b$ with explicit $\ln 2$ thresholds, fixed-dimension hierarchy, and finite Fejér interval-mass certificate (`A6.1`–`A6.4`), and the Cauchy–Binet / cyclotomic Vandermonde divisibility / separation-cost barrier / rank-only and denominator-only countermodels (`A7.1`–`A7.4`)—survived adversarial verification.

The companion script `scripts/phase26_toeplitz_uniformity.py` ran cleanly on Windows (`python -B scripts/phase26_toeplitz_uniformity.py`, exit code `0`, 5.5 s), passing all **76,678 `[exact]`** assertions and **198 `[finite]`** assertions. An AST audit confirmed **zero floating-point values or `math`/`cmath` calls inside any `[exact]` assertion** (the only `float()` calls prior to `finite_section()` occur inside diagnostic `print()` lines 669–670 and 772).

However, the audit identified **2 Major defects** that must be repaired before acceptance:

1. **MJ-1 (False converse in Corollary 5.4, line 571):** The unqualified converse claiming that $(\det G_{N,r})^{1/r} \to 1$ implies $\sum_{k<r}(1-k/r)|S_N(kh)|^2 \to 0$ is **false** whenever $\|E\|_{\rm op} \ge 1$, refuted below by an explicit counterexample family (and a normal-number realization) where $(\det G_{N,r})^{1/r} \to 1$ while the Fejér-weighted Fourier energy diverges to $+\infty$.
2. **MJ-2 (Invalid deduction in Proposition 3.4(3), line 440, plus contradictory front-table entry A3.4, line 26):** Non-computability / non-c.e. / non-co-c.e. recognition of $a_* = 1$ (`AC-11`) does **not** imply that no algorithm uniformly produces an optimal schedule from a program for $x$ (since a uniformly computable $\liminf$ characterization is still $\Pi^0_3$). The conclusion is true, but requires diagonalization via Kleene's Recursion Theorem applied to Proposition 3.5. In addition, Results-at-a-glance row A3.4 contradicts Proposition 3.4(2) and §10 both in its mathematical statement (`{x computable : a_*(x) = 1}` vs `{x ∈ ℝ : a_*(x) = 1}`) and in its external citation (`Becher–Heiber–Slaman (2014)` vs `Ki–Linton (1994)`).

Once **MJ-1**, **MJ-2**, and the **9 Minor** items below (including a proof slip in Theorem 1.3's antiunitary flip, an upward-rounded lower bound `0.101782` in A5, broken section cross-references, and a stale `GF-45` / misplaced `CC-50` citation) are repaired, Track A will be ready for acceptance.

---

## Script & Exactness Verification

Command run on Windows:
```text
python -B scripts/phase26_toeplitz_uniformity.py
```
- **Exit code:** `0` (5.5 s)
- **Counts verified:**
  - `A1 Gram determinant inequalities`: `5,230` `[exact]`
  - `A4 exact controls`: `1,747` `[exact]`
  - `A5 Koksma constant and Toeplitz norm bounds`: `31,254` `[exact]`
  - `A6 weak positivity certificates`: `16,232` `[exact]`
  - `A7 Cauchy-Binet, arithmetic and countermodels`: `22,215` `[exact]`
  - **Total `[exact]`:** `76,678` (verified zero floats in any `[exact]` computation or assertion via AST inspection)
  - **`[finite]` (isolated in `finite_section`):** `198`
  - **Total:** `76,876`
- **Algorithmic checks on script internals:**
  - Exact `QI` field arithmetic, `det()` Gaussian elimination, Sylvester `is_pd_hermitian()`, `gs_residuals()`, `cyclotomic()`, `poly_resultant()` (verified resultant sign/leading-coefficient recursion $\operatorname{Res}(a,b) = (-1)^{mn}\operatorname{lc}(b)^{m-k}\operatorname{Res}(b,r)$), `cyc_norm()`, and `extreme_discrepancy()` (exact on all duplicate-free sorted atom lists passed to it) were all checked line by line and are exact.
  - Exact rational check of the $K=12$ Bernoulli enclosure:
    - $D_{\text{grid}} = \frac{520393063}{2176782336} \approx 0.2390652728 \ge 0.239065$ (valid lower bound).
    - $D_{\text{up}} = \frac{67212715}{272097792} \approx 0.2470167601 \le 0.247017$ (valid upper bound).
  - Exact rational check of the A5 sharpness lower bound `re_lower`:
    - `re_lower` $= 0.1017817061\ldots < 0.101782$ (see **MN-2**); ratio `re_lower / (52/1000)` $= 1.9573405\ldots > 1.957$ (valid).
  - High-precision spot check of `[finite]` bit generators (`int_bits_ln2`, `int_bits_stoneham23`, `int_bits_euler2`): agree with $\ln 2$, $\alpha(2,3)$, and $E_2$ to machine precision.

---

## Section-by-Section Mathematical Audit

### Section 0 & Track A1 (`A1.1`–`A1.3`, §1.1–§1.6)
- **Lemma 0.1:** Verified. $D_N = \sup R - \inf R$, circular-arc equivalence (noting complements of `[u, v)` on $\mathbb{T}$ are half-open `[v, u)` of the same orientation), and $D_N^* \le D_N \le 2D_N^*$ are exact.
- **Lemma 1.1:** Verified in arbitrary (including infinite-dimensional $L^2(\rho)$) inner product spaces, including singular / linearly dependent families.
- **Theorem 1.2 (`A1.1`):** Verified for all $r \ge 1$ and all singular cases. Specifically tested the boundary cases:
  - $r = 1$: both sides equal $1$ (with $0^0 = 1$), condition $S_N(0) = 1 = S_N(h)^0$ holds.
  - $\det G = 0$, $|S_N(h)| < 1$ ($r \ge 2$): LHS $= 0 < (1 - |S_N(h)|^2)^{r-1} =$ RHS, so equality never holds; conversely $S_N(kh) = S_N(h)^k$ for $k < r$ forces $v_j - S v_{j-1} \perp W_j$ and hence $\det G = (1 - |S|^2)^{r-1} > 0$, ruling out any singular counterexample.
  - $|S_N(h)| = 1$ ($r \ge 2$): strict convexity of $S^1$ forces all $z_n$ equal, so both sides equal $0$ and $S_N(kh) = S^k$ holds.
- **Theorem 1.3 (`A1.2`):** The Verblunsky factorization $\det G_{N,r} = \prod_{k=1}^{r-1}(1 - |\alpha_k|^2)^{r-k}$ (when $\det G_{N,r-1} > 0$), $|\alpha_j| \le 1$, $\alpha_1 = S_N(h)$, and Simon's indexing correspondence $|\alpha_k| = |\alpha_{k-1}^{\text{Simon}}|$ are all valid. However, line 123 contains a one-phrase proof slip in the antiunitary-flip map (**MN-1**).
- **Corollary 1.4:** Minor hypothesis/notation precision needed for singular $G_{N,m}$ and the $r \to \infty$ limit at fixed $N$ (**MN-3**).
- **Corollary 1.5:** Both $d_0 \ge d_1 \ge \cdots$, monotonicity $(\det G_{N,r})^{1/r} \le (\det G_{N,m})^{1/m}$, and Hadamard–Fischer with remainder block $\det G_{N,r} \le (\det G_{N,m})^q \det G_{N,s} \le (\det G_{N,m})^{\lfloor r/m \rfloor}$ are completely rigorous, including singular cases.
- **Propositions 1.6, 1.7, 1.8:** All verified. Proposition 1.7(3) is properly labelled as an unverified external proof sketch. Proposition 1.8(4)–(5)'s calculation of $\gamma(m) = |\hat\mu_p(1)|^2 + O(2^{-m})$ for biased Bernoulli $\mu_p$, real-analyticity of $f$, and integrability $\log f \in L^1$ (finitely many finite-order zeros on compact $\mathbb{T}$) was checked step by step and is airtight (modulo specifying $p \in (0, 1) \setminus \{1/2\}$, **MN-4**).

### Track A2 (`A2`, `A2.6`, §2.1–§2.6)
- **Lemmas 2.2 & 2.3:** Completely rigorous. Lusin's property (N) (forward images of Borel $\lambda$-null sets under finite-to-one piecewise-affine $T_b$ and $M_h$ are Borel and $\lambda$-null) is properly used to prove $(T_b)_*\mu_s \perp \lambda$ and $(M_h)_*\mu_s \perp \lambda$, and Riemann–Lebesgue on $\widehat{\mu_{ac}}(k) = \widehat{\mu_{ac}}(b^j k)$ cleanly forces $\mu_{ac} = a(\mu)\lambda$.
- **Proposition 2.4 (Self-contained constant-density Szegő–Kolmogorov–Krein):** Verified line by line. Inner regularity of $\rho_s$ + outer regularity of $\lambda$, smooth cutoff $\varphi$, conjugate function $\widehat{\tilde u}(k) = -i\,\mathrm{sgn}(k)\hat u(k)$ (checked: $\tilde u$ is real-valued since $\widehat{\tilde u}(-k) = \overline{\widehat{\tilde u}(k)}$, and $\hat G(k) = (1 + \mathrm{sgn}(k))\hat u(k)$ vanishes for $k < 0$ and equals $\hat u(0)$ at $k = 0$), outer function $F = e^G$ with $|F| = e^{-M\varphi}$ and $F(0) \ge e^{-\varepsilon}$, uniform polynomial approximation $q_n = P_n/\hat F(0)$, reciprocal monic polynomial $p(z) = z^m \overline{q_n(1/\bar z)}$, and Cesàro limit for $D_m^{1/m}$ (including the $a = 0$ case) are **100% rigorous**.
- **Theorem 2.1 & Lemma 2.5:** Both the monotone-root proof and the Hadamard–Fischer variant are airtight. In Lemma 2.5(2), unrolling $J$ of length $\ell \in [2/K, 1)$ confirms $1 \le \lfloor K(u+\ell)\rfloor - \lceil Ku\rceil \le K - 1$, so the inscribed grid open arc always has distinct endpoints and length $\ge \ell - 2/K$; the open-interior argument safely bypasses boundary atoms at $b$-adic endpoints.
- **Lemma 2.6:** Verified (including connectedness of $C_b(x)$ from $\|\mu_{N+1}-\mu_N\|_{TV} \le 2/(N+1)$).
- **Proposition 2.7 (`A2.6`, $a(\mu) = \mu(\mathcal{N}_b)$):** Checked with particular care. Because $\mathcal{N}_b$ is Borel, strictly $T_b$-invariant ($T_b^{-1}\mathcal{N}_b = \mathcal{N}_b$), and of full $\lambda$-measure (Borel's theorem), $\mu' = \mu|_{\mathcal{N}_b}$ is $T_b$-invariant, $\int f\,d\mu' = \int A_N f\,d\mu' \to \mu(\mathcal{N}_b)\int f\,d\lambda$ by Bounded Convergence and Wall's equidistribution equivalence, while $\mu|_{\mathbb{T}\setminus\mathcal{N}_b} \perp \lambda$. Uniqueness of Lebesgue decomposition gives $\mu_{ac} = \mu(\mathcal{N}_b)\lambda$ without invoking ergodic decomposition or Birkhoff's theorem. **Completely rigorous.**

### Track A3 (`A3`, `A3.4`, §3)
- **Theorem 3.1:** Both directions ($\le$ via Theorem 2.1, $\ge$ via fixed-$m$ compactness + diagonal selection $r(N) = \max\{m \le N : N_m \le N\}$ with $N_1 = 1$), monotonicity for slower schedules, fixed-$m$ $\lambda_{\min}$ characterization, and $h$-independence are airtight.
- **Proposition 3.2:** All four cases of the explicit bound $D(\mu_p) \le \max(2(1-q)^k, 1 - q^k, 2^{1-k}) < 1$ (noting $k \ge 2$ automatically since $2(1-q) > 1$), the value $8/9$ for $p = 1/3$, and the level-12 enclosure $[0.239065, 0.247017]$ are verified.
- **Proposition 3.4 & Table row A3.4:** **Major defect (MJ-2)** — see Findings below.
- **Proposition 3.5 (No universal schedule):** Checked every constant and error term. The polynomial $p(z) = z^{j-P_k}\prod_i(z - e(y^{(i)}))$ yields $d_j(\mu_{N_k}) \le 4^{P_k}(4\pi^2 b^{-4P_k} + 16^{-P_k}) \le (4\pi^2 + 1)4^{-P_k}$, hence $(\det G_{N_k, r(N_k)})^{1/r(N_k)} \le ((4\pi^2+1)4^{-P_k})^{1/2} \to 0$ (for $k$ large enough that $(4\pi^2+1)4^{-P_k} \le 1$). For normality, $P_k = b P_{k-1}$ and $N_{k-1} \ge 2 \cdot 16^{P_{k-1}}$ cleanly make $P_k / N_{k-1} \to 0$ and $kL/N_{k-1} \to 0$, and the construction is computable when $r$ is. **Airtight.**

### Track A4 (`A4`, §4)
- **Proposition 4.1:** Exact over any commutative ring.
- **Theorem 4.2:** Sound (minor precision polish on "approaches $0$ from the right" in item 3, **MN-4**).
- **Proposition 4.3:** Unconditional Champernowne–zero-run witnesses $y_\alpha$ verified carefully: block $m$ has length $O(m) = O(\sqrt{N})$, boundary positions number $O(L\sqrt{N}) = o(N)$, and convergence on all $b$-adic cylinders $I_w$ implies weak-$*$ convergence on $\mathbb{T}$ because every $f \in C(\mathbb{T})$ is uniformly approximated by level-$L$ cylinder step functions. **Airtight.**
- **`GF-45` controls:** Note that Phase 26 Audit III (`notes/phase26/reviews/audit-3-gf45.md`) has already passed cleanly (0 Critical, 0 Major), so the `Conditional` / `(audit pending)` labels on `GF-45` are now stale (**MN-7**).

### Track A5 (`A5.1`–`A5.5`, §5)
- **Theorem 5.1 (`A5.1`):** Integration by parts $S_N(h) = -\int_0^1 R(s) f'(s)\,ds$ (sign verified), recentering by $\kappa = \frac{1}{2}(\sup R + \inf R)$, rotation into a real cosine integral ($\int_0^1 |\cos(2\pi hs - \phi)|\,ds = 2/\pi$), bounds $2|h|D_N$ and $4|h|D_N^*$, and sharpness via $\rho_\delta$ and $M_h$-pullbacks are all **100% rigorous**. Minor rounding slip `0.101782` in the finite sharpness certificate text/printout (**MN-2**).
- **Theorem 5.2 (`A5.2`, linear-in-$r$ operator norm bound):** Checked line by line with extreme scrutiny. Applying integration by parts directly to the real 1-periodic $C^\infty$ quadratic form $f(\theta) = |q(\theta)|^2$ for frequency-centred $q(\theta) = \sum_{j=0}^{r-1} a_j e((j - \frac{r-1}{2})\theta)$ (where $e((j-\frac{r-1}{2})\theta)$ remain orthonormal on $[0,1]$ even when $r$ is even!) yields $\int_0^1 |f'| \le 2\|q\|_2 \|q'\|_2 \le 2\pi(r-1)$, hence $\|G_{N,r}(h) - I\|_{\rm op} \le \pi(r-1) D(\nu_N) \le \pi|h|(r-1) D_N$. Independent numerical stress-testing on 200 adversarial point sets confirmed the bound with margin. **Genuinely linear in $r - 1$ and completely rigorous** (tiny orientation note for $h < 0$, **MN-4**).
- **Theorem 5.3:** Both scalar log inequalities $\lambda - \frac{\lambda^2}{2(1-\eta)} \le \log(1+\lambda) \le \lambda - \frac{\lambda^2}{2(1+\eta)}$ on $[-\eta, \eta]$ verified by differentiation; trace and Frobenius sums are exact.
- **Corollary 5.4:** Forward bound verified, but the **unqualified converse on line 571 is FALSE** (**MJ-1**).
- **Corollary 5.5, §5.4, Lemma 5.6, Theorem 5.7:** Verified (`ST-28` rates, Ramanujan cancellation on prime powers for $r \le p^{K-1}/|h|$, Gershgorin approximation stability $\pi|h|r(r-1)\bar\varepsilon$, random-point expectation $\prod_{j<r}(1-j/N)$, $\mathbb{E}\log\det G_{N,N} = -N\log N$, and regular $N$-gon extremality).

### Track A6 (`A6.1`–`A6.4`, §6)
- **Theorem 6.1:** Affine limit $t + (1-t)a(\mu)$, supremum $t + (1-t)a_*$, and $1/t$-Lipschitz stability (including factor $2$ from Toeplitz row sum of $|\Delta c_{k-j}|$) verified.
- **Theorem 6.2 & Corollary 6.2.1:** Every constant verified independently:
  - $1 - \cos\pi\ell \ge 4\ell^2$ on $[0, 1/2]$ (concavity / single inflection of $f'' = \pi^2\cos\pi\ell - 8$).
  - Optimized cube-root converse $D_N \ge 1 - \frac{3}{2}\bigl(\frac{1-|S_N(1)|}{2}\bigr)^{1/3}$ for $1 - |S_N(1)| \le 1/4$ (including boundary $1 - \sigma = 1/4$ and $|S| = 1$).
  - Direct bound $(1-\delta)\cos\pi\delta - \delta \ge 1 - 2\delta - 5\delta^2$ on $[0, 1/2]$ (since $\pi^2/2 < 5$).
  - Quadratic inverse $\delta_\sigma = (\sqrt{1+5(1-\sigma)}-1)/5 \in [0, (\sqrt{6}-1)/5] \subset [0, 1/2]$.
  - $\ln 2$ constants at $\delta = 10^{-4}$: $1 - 2\delta - 5\delta^2 = 0.99979995$ and $16\delta^3/27 = 16/(27 \cdot 10^{12})$ are exact.
- **Theorem 6.3:** Exact.
- **Theorem 6.4:** Fejér pointwise lower bound $F_r * \mu_N \ge \gamma$, tail bound $\int_{\delta \le |u| \le 1/2} F_r(u)\,du \le \frac{1}{2r}(\frac{1}{\delta} - 2) < \frac{1}{2r\delta}$, shrunken-arc bound $\mu_N(J) \ge \gamma(\lambda(J) - 2\delta) - \frac{1}{2r\delta}$ (vacuously true when $\lambda(J) \le 2\delta$), and optimization at $\delta = (4\gamma r)^{-1/2}$ yielding $D_N \le 1 - \gamma + 2\sqrt{\gamma/r}$ are all **100% exact**.

### Track A7 (`A7.1`–`A7.4`, §7)
- **Theorem 7.1:** Cauchy–Binet exact.
- **Proposition 7.2:** Total nonnegativity in $\mathbb{Q}(\zeta_Q)^+$, Liouville bound $N^{-r\varphi(Q)}$, prime-level valuation $v_{\mathfrak{p}}(X) \ge r(r-1)$ and norm divisibility $p^{r(r-1)} \mid N_{\mathbb{Q}(\zeta_p)/\mathbb{Q}}(X)$, Galois-averaged lower bound $N^{-r} p^{r(r-1)/(p-1)}$ (attained at $N = r = p$ where $X = p^p$), and uniform-roots identity $\sum_{|I|=r} |V_I|^2 = Q^r$ are all exact (specify $\mathrm{Norm} = N_{\mathbb{Q}(\zeta_Q)/\mathbb{Q}}$ explicitly, **MN-4**).
- **Proposition 7.3:** Separation bound $s = 2\sin(\pi/Q) \ge 4/Q$, $N^{-1} M_r^{1/r} s^{r-1} \le \frac{e}{r} s^{r-1}$, ceiling $r - 1 \le \log(e/(rc))/\log(Q/4)$ (for $Q > 4$), and the $\ln 2$ BBP denominator growth $\log \operatorname{lcm}_{n<N} Q_n \sim N$ are verified.
- **Theorems 7.4 & 7.5 and §7.6:** Rank-only ($L_b \in K_b$) and denominator-only ($e(1/Q_n)$ and exact rational analogue $\det G_{K,2} < 2/K^2$) countermodels and the Montgomery–Vaughan large-sieve analysis (including the neat $N\delta_N \ge \kappa \implies x \in \mathcal{N}_b$ remark) are all verified. Line 788 misattributes finite-$\mu$ witnesses to `CC-50` (**MN-6**).

---

## Classified Findings

### Critical Findings

None (`0`).

### Major Findings

#### MJ-1 — False converse statement in Corollary 5.4 (counterexample)
- **Location:** `notes/phase26/toeplitz-determinants-and-uniformity.md:571`
- **Quoted text:** *"Conversely, the root tends to $1$ only if $\sum_{k<r}(1-k/r)\lvert S_N(kh)\rvert^2\to 0$, by Theorem 5.3. If $\lVert E\rVert<1$ fails, use Corollary 1.5(2) with a smaller $m$."*
- **Issue:** Without $\limsup \|E\|_{\rm op} < 1$, the first sentence is **false**—the Fejér-weighted Fourier energy at dimension $r$ can tend to $+\infty$ while $(\det G_{N,r})^{1/r} \to 1$.
- **Explicit counterexample:** Let $r = m^4$, $N = 2m^4$ ($m \ge 2$), and take $K = m^3$ points at $0$ together with $N - K = 2m^4 - m^3 > r$ equally spaced $(N-K)$-th roots of unity. For every $1 \le k < r < N - K$, the equally spaced roots sum to $0$, so $S_N(k) = K/N = \frac{1}{2m} =: \alpha$ and $G_{N,r}(1) = (1-\alpha)I_r + \alpha J_r$. By Proposition 4.1,
  $$(\det G_{N,r}(1))^{1/r} = (1-\alpha)^{1-1/r}(1 + (r-1)\alpha)^{1/r} \ge 1 - \alpha = 1 - \frac{1}{2m} \to 1,$$
  whereas
  $$\sum_{k=1}^{r-1}\left(1 - \frac{k}{r}\right)|S_N(k)|^2 = \frac{r-1}{2}\alpha^2 = \frac{m^4 - 1}{8m^2} \to +\infty.$$
  Here $\|E\|_{\rm op} = (r-1)\alpha \sim m^3/2 \to \infty$, so Theorem 5.3 does not apply. The same phenomenon occurs along a single base-$b$ normal number $x$ formed from Champernowne blocks alternating with vanishing-density zero runs ($\alpha_j \to 0$, $r(N_j) \asymp \alpha_j^{-3}$). Applying Corollary 1.5(2) with a smaller $m < r$ only controls $\sum_{k<m}(1 - k/m)|S_N(kh)|^2$ (for dimensions $m$ where $\|G_{N,m}-I\|_{\rm op} < 1$), not the sum up to the original $r$.
- **Required fix:** Restrict the converse at line 571 to the regime $\limsup \|E\|_{\rm op} < 1$, and state separately that unconditionally $(\det G_{N,r})^{1/r} \to 1$ implies $\sum_{k<m}(1 - k/m)|S_N(kh)|^2 \to 0$ for every sub-dimension $m \le r$ satisfying $\limsup \|G_{N,m} - I\|_{\rm op} < 1$ (in particular, every fixed $m$).

#### MJ-2 — Invalid proof deduction in Proposition 3.4(3) and contradictory summary table row A3.4
- **Location:** `notes/phase26/toeplitz-determinants-and-uniformity.md:26`, `notes/phase26/toeplitz-determinants-and-uniformity.md:436–441`, and `notes/phase26/toeplitz-determinants-and-uniformity.md:882`
- **Issue 1 (Non sequitur in Proposition 3.4(3), line 440):** The text argues: *"On digit-oracle program codes, recognizing $a_* = 1$ is neither computable, nor c.e., nor co-c.e. (`AC-11`, kernel-verified switching construction, with the endpoint properties as inputs). So no algorithm produces an optimal schedule uniformly from a program for $x$."*
  This implication is **invalid**. Even if an algorithm $A$ uniformly produced an optimal computable schedule $r_e(N) \to \infty$ from every total digit-oracle program $e$, the resulting criterion $a_*(x_e) = 1 \iff \liminf_{N\to\infty}(\det G_{N,r_e(N)}(1))^{1/r_e(N)} = 1$ is still a $\Pi^0_3$ condition—neither computable, c.e., nor co-c.e.—so no contradiction with `AC-11` arises. (Compare: $1 - D_N(x_e; b)$ is uniformly computable from $e$ and satisfies $\liminf_N(1 - D_N) = 1 \iff a_*(x_e) = 1$, yet recognizing $a_* = 1$ remains neither computable, c.e., nor co-c.e.)
- **Issue 2 (Contradictory statement and citation in Results-at-a-glance row A3.4, line 26):** Row A3.4 claims *"$\{x \text{ computable} : a_*(x) = 1\}$ is the set of computable normal numbers, which is $\Pi^0_3$-complete"* and lists **`Becher–Heiber–Slaman (2014); AC-11`** as external inputs. By contrast, Proposition 3.4(2) (line 439) and §10 (line 882) state that $\{x \in \mathbb{R} : a_*(x) = 1\} = \mathcal{N}_b + \mathbb{Z}$ is $\Pi^0_3$-complete in the **Borel** hierarchy by **Ki–Linton (1994)**, and never cite Becher–Heiber–Slaman (2014). (Also note `AC-11` is registered in `docs/registry/AC.toml` for $b = 2$; its switching construction transfers immediately to arbitrary $b \ge 2$.)
- **Required fix:**
  1. Prove *"no algorithm uniformly produces an optimal schedule $r_e$ from a total digit-oracle program $e$"* rigorously via **Kleene's Recursion Theorem** combined with **Proposition 3.5** (e.g., as a corollary right after Proposition 3.5): build a uniformly computable digit-oracle generator $p(e, \cdot)$ that executes stage $k$ by emitting copies of the de Bruijn cycle $\beta_k$ indefinitely while dovetailing computations of $A(e)(M)$ over $M \ge 16^{P_k}(N_{k-1}+2P_k)$ until some $M_k$ halts with $A(e)(M_k) \ge 2P_k$ (if $M_k$ exceeds the current emitted length $L$, emit copies of $\beta_k$ until reaching $M_k$ and end stage $k$; if $M_k \le L$, the prefix of length $M_k$ already ended inside stage $k$, so the determinant bound at $M_k$ already holds and stage $k$ ends immediately at $L$). Then $p(e,\cdot)$ is unconditionally total for every $e$; by Kleene's Recursion Theorem there is a total fixed point $e^*$ computing $x_{e^*} = p(e^*,\cdot)$, forcing $A(e^*)$ to be a total schedule tending to $\infty$, so every stage terminates, $x_{e^*}$ is normal ($a_* = 1$), yet $\liminf_k (\det G_{M_k, r_{e^*}(M_k)}(1))^{1/r_{e^*}(M_k)} = 0$, contradiction.
  2. Reconcile Results-at-a-glance row A3.4 (line 26) with Proposition 3.4(2) and §10 (matching `{x : a_*(x) = 1}` and `Ki–Linton (1994)`, and noting the $b = 2 \to b \ge 2$ transfer for `AC-11`).

---

### Minor Findings

#### MN-1 — Index slip in the antiunitary-flip proof step of Theorem 1.3
- **Location:** `notes/phase26/toeplitz-determinants-and-uniformity.md:123`
- **Issue:** For $C(u) = D^{j-1}\overline{u}$, $C(v_k) = v_{j-1-k}$ maps $W'_j = \operatorname{span}(v_1,\dots,v_{j-1})$ onto $\operatorname{span}(v_0,\dots,v_{j-2})$, **not** "onto itself" (since $C(v_{j-1}) = v_0 \notin W'_j$). That image $\operatorname{span}(v_0,\dots,v_{j-2})$ is exactly what yields $\|g_j\|^2 = \operatorname{dist}(v_0, W'_j)^2 = \operatorname{dist}(v_{j-1}, \operatorname{span}(v_0,\dots,v_{j-2}))^2 = d_{j-1}$.
- **Fix:** Replace *"maps $W'_j$ onto itself"* with *"maps $W'_j$ onto $\operatorname{span}(v_0,\dots,v_{j-2})$"* (or alternatively use $D^j\overline{u}$, which maps $W'_j$ onto itself and $v_0$ to $v_j$, giving $\|g_j\| = \|f_j\|$).

#### MN-2 — Upward-rounded lower bound `0.101782` in A5 sharpness certificate (note and script)
- **Location:** `notes/phase26/toeplitz-determinants-and-uniformity.md:535` and `scripts/phase26_toeplitz_uniformity.py:669` (and `772`)
- **Issue:** In `a5_checks()`, the exact rational lower bound `re_lower` from $\cos y \ge 1 - y^2/2$ and $\pi < 22/7$ evaluates to `0.1017817061... < 0.101782`. Printing `{float(re_lower):.6f}` rounds *up* to `0.101782`, and line 535 quotes $\operatorname{Re} S_N(1) \ge 0.101782$ as a consequence of those inequalities. (While true $\operatorname{Re} S_N(1) \approx 0.10178216$ exceeds `0.101782`, `re_lower` only certifies $\ge 0.101781$. The claimed ratio $> 1.957$ is valid: `re_lower / 0.052 = 1.95734... > 1.957`.)
- **Fix:** Change `0.101782` at line 535 to `0.101781`, and add explicit outward-rounded exact `check(...)` assertions in `a5_checks()` (`re_lower >= F(101781, 10**6)`) and `a6_checks()` (`Dgrid >= F(239065, 10**6)` and `Dup <= F(247017, 10**6)`).

#### MN-3 — Missing nondegeneracy hypothesis and measure-vs-finite-$N$ phrasing in Corollary 1.4
- **Location:** `notes/phase26/toeplitz-determinants-and-uniformity.md:128–130`
- **Issue:** Assuming $\det G_{N,m} > 0$ is needed for $\alpha_1,\dots,\alpha_m$ to exist and for $\det G_{N,m+1}/\det G_{N,m}$ to avoid $0/0$. Also, $\limsup_{r\to\infty}(\det G_{N,r})^{1/r}$ at fixed finite $N$ is trivially $0$ (Proposition 1.6); the $\limsup_{r\to\infty}$ statement belongs to $D_r(\rho)^{1/r}$ for a measure $\rho$.
- **Fix:** Add $\det G_{N,m} > 0$ and state the $\limsup_{r\to\infty}$ inequality for $D_r(\rho)^{1/r}$ (or uniformly over $N$ with $r \le N$).

#### MN-4 — Minor hypothesis and precision omissions in Prop 1.8(4), Thm 4.2(3), Thm 5.2, §5.4, Prop 7.2, Prop 7.3
- **Locations & fixes:**
  - *Prop 1.8(4), line 180:* state $p \in (0,1) \setminus \{1/2\}$ explicitly (not just $p \ne 1/2$).
  - *Thm 4.2(3), line 478:* replace the informal *"If the orbit approaches $0$ from the right"* (since the $(1-\alpha)\lambda$ part visits $(1-\varepsilon, 1)$) with the precise condition $\lim_{\varepsilon\to 0^+}\limsup_N \mu_N((1-\varepsilon, 1)) = 0$.
  - *Thm 5.2, line 550:* note that for $h < 0$, $M_h^{-1}([u,v))$ consists of $|h|$ arcs $(a,b]$ rather than $[a,b)$, which satisfy the same discrepancy bound $D_N$ by $\varepsilon \downarrow 0$ (or simply note $G_{N,r}(-h) = \overline{G_{N,r}(h)}$).
  - *§5.4, line 588:* note $Q \nmid h$ (e.g. $h = 1$) for $G_{P,r}(h) = (1+\beta)I - \beta J$.
  - *Prop 7.2, lines 742–746:* explicitly define $\mathrm{Norm}(X) = N_{\mathbb{Q}(\zeta_Q)/\mathbb{Q}}(X)$ (degree $\varphi(Q)$) to avoid ambiguity with $N_{\mathbb{Q}(\zeta_Q)^+/\mathbb{Q}}(X)$ from item 1.
  - *Prop 7.3, lines 758–759 & Table line 36:* state $s < 1$ (resp. $Q > 4$) when dividing by $\log(1/s)$ (resp. $\log(Q/4)$); in Table line 36, align *"budget of order $r\log N$"* with §7.3 line 772's sharper net budget $r\log(e/(rc))$ after $N^r$ cancels $N^{-r}$.

#### MN-5 — Broken internal section cross-references and skipped subsection numbers
- **Locations:**
  - Line 7: `§1.9` $\to$ actual heading is `§1.6`.
  - Line 21 (Table A1.2): `§1.3–1.5` $\to$ actual is `§1.3`.
  - Line 22 (Table A1.3): `§1.6–1.8` $\to$ actual is `§1.5`.
  - Line 26 (Table A3.4): `§3.4` $\to$ no `§3.4` heading exists (Proposition 3.4 is inside `§3.3`).
  - Line 352: `§4.2` $\to$ no `§4.2` heading exists (Proposition 4.3 is inside `§4`).
  - Also §3 jumps directly to `### 3.3` and §4 jumps directly to `### 4.4`.
- **Fix:** Normalize subsection numbering and fix all five cross-references.

#### MN-6 — Misattributed registry citation `CC-50` for finite-irrationality-exponent $D=0$/$D=1$ witnesses
- **Location:** `notes/phase26/toeplitz-determinants-and-uniformity.md:788`
- **Issue:** Line 788 says "`AC-11` and `CC-50` record witnesses with finite irrationality exponent at both extremes $D = 0$ and $D = 1$." In `docs/registry/CC.toml`, `CC-50` is the Legendre–Bezout linear-window and window–denominator barrier for $\ln 2$, not paired finite-$\mu$ witnesses at $D=0,1$. The finite-$\mu$ / $\mu=2$ witnesses at $D=1$ and $D=0$ are recorded in `AC-11`, `GF-28` (Kempner–Shallit badly-approximable $K_2$ barrier), and `GF-33`/`GF-46` ($\mu=2$ / badly-approximable normal numbers).
- **Fix:** Replace `CC-50` at line 788 with the appropriate IDs (`GF-28`, `GF-33`, `GF-46`).

#### MN-7 — Stale `GF-45` audit-pending / Conditional status
- **Location:** `notes/phase26/toeplitz-determinants-and-uniformity.md:27, 490, 497, 840, 880`
- **Issue:** The note marks `GF-45` as `Conditional` / `(audit pending)`, whereas Phase 26 Audit III (`notes/phase26/reviews/audit-3-gf45.md`) has already passed cleanly (0 Critical, 0 Major).
- **Fix:** Update the `GF-45` witness status to reflect the completed Audit III (retaining the distinction between `GF-45` external-to-Track-A input and Proposition 4.3's self-contained unconditional witnesses).

#### MN-8 — Mathlib inner-product convention note in Lean blueprint (§1.6)
- **Location:** `notes/phase26/toeplitz-determinants-and-uniformity.md:214`
- **Issue:** In Mathlib, `⟪x, y⟫_ℂ` is conjugate-linear in the *first* argument (`x`), opposite to §0's convention. Although `det_gram_eq_prod_gramSchmidt` remains true as stated (since $\det G^T = \det G$), `orbitGram z r j k` equals `⟪v j, v k⟫_ℂ`, not `⟪v k, v j⟫_ℂ`.
- **Fix:** Add a brief comment or swap to `⟪v j, v k⟫_ℂ` in statement 3 so Track H can apply it directly to `orbitGram` without taking a transpose.

#### MN-9 — Small notational and boundary polishes
- **Line 432:** In $r(N) = \max\{m \le N : \varepsilon_j(N) \le 1/j\ \forall j \le m\}$, note $\varepsilon_1 \equiv 0$ (since $\lambda_{\min}(G_{N,1}) = 1 \ge a_*$) so the set is nonempty at small $N$.
- **Line 602:** Write $\{2^n\ln 2\} \equiv \{s_n\} + T_n \pmod 1$ (or $\|\{2^n\ln 2\} - \{s_n\}\|_{\mathbb{T}} \le T_n$) since $\{s_n\} + T_n$ can exceed $1$.
- **Line 674:** Specify slowly growing run lengths (e.g. $L_k = k$, not exponentially growing) so that $C_3(x) = \{\frac{1}{2}(\delta_0 + \delta_{1/2})\}$ is a singleton.
- **Line 970:** Replace $\log Q_N \gg N$ with $\log Q_N \asymp N$ (or $\ge c N$) to avoid ambiguity with line 456's use of $\gg$ for asymptotic dominance.

---

## Final Assessment

- **Benchmark & evidence discipline:** Fully respected. No benchmark status in `BC-01`…`BC-50` is altered; `[exact]` vs `[finite]` boundaries are clean; external inputs are clearly tracked (except the table mismatch in **MJ-2** and `CC-50` in **MN-6**); and the note explicitly states that cross-model review is not independent human peer review.
- **Verdict:** **REVISE** — repair **MJ-1** (qualify line 571's converse to $\limsup\|E\|_{\rm op} < 1$), **MJ-2** (replace Proposition 3.4(3)'s non sequitur with the Kleene Recursion Theorem + Proposition 3.5 diagonalization, and align Table row A3.4 with Proposition 3.4(2) and §10), and **MN-1** through **MN-9**. No structural redesign of `A1`–`A7` is needed.

*Cross-model review is not independent human peer review.*

---

## Post-Repair Verification

- **Post-repair verdict:** **ACCEPT** (`0` Critical, `0` Major, `0` Minor remaining).
- **Disclaimer:** **Cross-model review is not independent human peer review.**

### 1. Script & Exactness Re-Verification

Command run on Windows:
```text
python -B scripts/phase26_toeplitz_uniformity.py
```
- **Exit code:** `0` (`5.7 s`).
- **Assertion counts verified:** **77,250 total** — **77,052 `[exact]`** (`A1`: 5,230; `A4`: 1,747; `A5`: 31,642; `A6`: 16,234; `A7`: 22,199) and **198 `[finite]`** (isolated in `finite_section`).
- **Zero-float audit:** An AST and division-operand scan over lines 1–982 confirmed **zero** floating-point or complex literals, **zero** `float`/`complex`/`math`/`cmath` references, and **zero** `int / int` floating-point divisions anywhere outside the `[finite]` section (lines 983–1089). Diagnostic decimals printed in `A5` and `A6` now use exact integer outward rounding (`dec_floor`/`dec_ceil`).
- **New exact certificates verified:**
  - `converse_counterexample_checks()` (`A5`, lines 736–781): verifies the `MJ-1` counterexample family ($r = m^4$, $N = 2m^4$, $K = m^3$, $\alpha = 1/(2m)$) for $2 \le m \le 6$, including exact $\mathbb{Z}[\zeta_{N-K}]$ verification of $N S_N(k) = K$ ($1 \le k < r$) and exact $r \times r$ Gaussian elimination of $\det G_{N,r}(1)$ for $m \le 3$, plus exact Fejér energy $(m^4-1)/(8m^2) \ge (m^2-1)/8$, $\|E\|_{\rm op} = (r-1)\alpha \ge 1$, and sub-dimension $m$ norm $< 1/2$ and energy $\le 1/(8m)$.
  - `MN-2` outward-rounded assertions: `re_lower >= F(101781, 10**6)` and `re_lower < F(101782, 10**6)` in `a5_checks()`, and `Dgrid >= F(239065, 10**6)` and `Dup <= F(247017, 10**6)` in `a6_checks()`.

### 2. Resolution Audit of Every Finding (`MJ-1`, `MJ-2`, `MN-1`–`MN-9`)

| ID | Status | Verification in repaired files |
| --- | --- | --- |
| **MJ-1** | **Resolved** | `toeplitz-determinants-and-uniformity.md` lines 616–638 restrict the Corollary 5.4 converse to $\limsup_N \|G_{N,r(N)}(h)-I\|_{\rm op} < 1$, state and prove the unconditional sub-dimension converse (including AM–GM compactness for fixed $m$), give the explicit compound-symmetric counterexample with exact script certificates (`A5`), and provide a full single-normal-number orbit realization. Reflected consistently in Table row A5.2 (line 29), Theorem 5.3 (line 607), §8 (lines 891, 895), §14 (line 1029), and §15 (line 1049). |
| **MJ-2** | **Resolved** | Proposition 3.4(3) (lines 455–457) removes the invalid deduction from `AC-11`, explains why a uniformly computable optimal schedule yields a $\Pi^0_3$ condition without contradicting `AC-11`, and explicitly marks the $b=2 \to b\ge 2$ transfer of `AC-11` as a paper deduction. New Proposition 3.6 (lines 477–497) proves non-existence of a uniform optimal-schedule algorithm via Kleene's Recursion Theorem. Table row A3.4 (line 26) and §10 (lines 949–951) now match Proposition 3.4(2) and Proposition 3.6 (`{x ∈ ℝ : a_*(x) = 1}`, `Ki–Linton (1994)`, `AC-11`, Kleene's recursion theorem). |
| **MN-1** | **Resolved** | Theorem 1.3 proof (line 123) now correctly states that $C(v_k) = v_{j-1-k}$ maps $W'_j = \operatorname{span}(v_1,\dots,v_{j-1})$ onto $\operatorname{span}(v_0,\dots,v_{j-2})$ and $v_0$ to $v_{j-1}$. |
| **MN-2** | **Resolved** | Note line 580 reports the certified outward-rounded bound $\mathrm{Re}\,S_N(1) \ge 0.101781$ (noting $0.1017817\ldots < 0.101782$); lines 429–430 record the exact rational `Dgrid` and `Dup` enclosure $[0.239065, 0.247017]$; script enforces both via exact `Fraction` assertions and prints outward-rounded decimals via `dec_floor`/`dec_ceil`. |
| **MN-3** | **Resolved** | Corollary 1.4 (lines 128–132) explicitly assumes $\det G_{N,m}(h) > 0$, distinguishes the fixed-$N$ uniform bound from the trivial $r > N$ vanishing, and proves $\limsup_{r\to\infty} D_r(\rho)^{1/r} \le d_m(\rho)$ for finite positive measures $\rho$ with $D_m(\rho) > 0$. |
| **MN-4** | **Resolved** | All 6 precision items verified: $p \in (0,1)\setminus\{\frac12\}$ (Prop. 1.8(4), line 182); $\lim_{\varepsilon\to 0^+}\limsup_N \mu_N((1-\varepsilon,1)) = 0$ with rigorous proof in Thm. 4.2(3) (lines 521–523) and verification for $y_\alpha$ in Prop. 4.3 (line 533); $h < 0$ orientation handling in Thm. 5.2 (line 595); $Q \nmid h$ in §5.4 (line 655); explicit $\mathrm{Norm}(X) = N_{\mathbb{Q}(\zeta_Q)/\mathbb{Q}}(X)$ in Prop. 7.2 (line 809); $s < 1$ / $Q > 4$ in Prop. 7.3 (lines 824–826) and net budget $r\log(e/(rc))$ aligned across Table row A7.3 (line 36), §7.3, and §8 (line 894). |
| **MN-5** | **Resolved** | Automated scan confirms contiguous section numbering (`0`, `1.1–1.6`, `2.1–2.6`, `3.1–3.4`, `4.1–4.3`, `5.1–5.5`, `6.1–6.4`, `7.1–7.6`, `8–15`) and **0 broken `§` cross-references** across the entire note. |
| **MN-6** | **Resolved** | Line 855 replaces `CC-50` with `AC-11`, `GF-28`, `GF-33`, and `GF-46`; §10 (line 923) accurately cites `CC-50` for the Legendre–Bezout window–denominator barrier for $\ln 2$. |
| **MN-7** | **Resolved** | All `GF-45` references (lines 27, 535, 542, 907, 947) updated to reflect registered `Paper proof` status and completed Phase 26 Audit III (0 Critical, 0 Major; explicitly noted as cross-model, not human peer review), while retaining its external-input distinction from Proposition 4.3. |
| **MN-8** | **Resolved** | §1.6 Lean blueprint (lines 215–222) documents Mathlib's conjugate-linearity in the first slot of `⟪x, y⟫_ℂ` and updates statement 3 to `Matrix.of fun j k => ⟪v j, v k⟫_ℂ` so it applies directly to `orbitGram` without transposition. |
| **MN-9** | **Resolved** | All 4 polishes verified: $\varepsilon_1 \equiv 0$ nonemptiness note (line 445), $2^n\ln 2 \equiv s_n + T_n \pmod 1$ / torus distance (line 669), slowly growing run lengths $L_k = k$ (line 741), and $\log Q_N \ge cN$ replacing $\gg$ (line 1050). |

### 3. Verification of Newly Added Proofs

- **Proposition 3.6 (Kleene Recursion Theorem diagonalization, lines 477–497):** Checked step by step.
  - *Totality:* Stage $k$ emits one digit of $\beta_k^\infty$ at each step $t$ while simulating $t$ steps of $A(e, M)$ for $T_k \le M \le T_k + t$, continuing to $N_k = \max(L, M_k)$ once some $M$ halts with $A(e, M) \ge 2P_k$. Even if a stage never terminates, a digit is emitted at every step, so $p(e, n) \in \{0,\dots,b-1\}$ is total computable.
  - *Fixed point & stage termination:* s-m-n + Kleene's recursion theorem yield a digit-oracle program $e^*$ with $\varphi_{e^*} = p(e^*,\cdot)$. If $A(e^*,\cdot)$ is total and tends to $\infty$, then for every $k$ some $M \ge T_k$ halts with $A(e^*, M) \ge 2P_k$, so every stage ends and $M_1 < M_2 < \cdots \to \infty$.
  - *Normality:* $N_k \ge M_k \ge T_k \ge 16^{P_k}$ preserves the Proposition 3.5 word-count error bound (the incomplete final cycle of stage $j$ adds at most $P_j$, already covered by $\sum_{j<k} P_j = O(P_{k-1}) = o(N_{k-1})$), and de Bruijn cycles ensure infinitely many non-$(b-1)$ digits so $x_{e^*}$ is not a $b$-adic rational with ambiguous expansion.
  - *Determinant collapse:* Since $N_{k-1} < T_k \le M_k \le N_k$, every position $n \in [N_{k-1}, M_k - 1]$ with $n < N_k - s_k$ has at least $s_k$ digits of $\beta_k^\infty$ to its right, leaving at most $N_{k-1} + s_k$ bad positions. Hence $d_j(\mu_{M_k}) \le 4^{P_k}(4\pi^2 b^{-2s_k} + (N_{k-1}+s_k)/M_k) \le (4\pi^2+1)4^{-P_k} < 1$ for $P_k \ge 3$ and $j \ge P_k$, giving $(\det G_{M_k, r}(1))^{1/r} \le ((4\pi^2+1)4^{-P_k})^{1/2} \to 0$ (both for $2P_k \le r \le M_k$ and trivially when $r > M_k$). **Sound.**
- **Corollary 5.4 — Orbit realization (single normal number, lines 630–636):** Checked step by step.
  - *Parameter consistency:* $r_j \ge 8$, $\alpha_j = r_j^{-1/3} \le 1/2$, $k_j = s_j = \lceil 3\log_b r_j \rceil$ satisfy $r_j b^{-k_j} \le r_j^{-2}$ and $r_j^2 b^{-s_j} \le r_j^{-1}$; inductive growth allows $b^{k_j} + s_j \le N_{j-1}/j$ for large $j$ and $A_j$ a multiple of $b^{k_j}$ with $A_j \ge j(r_j N_{j-1} + r_j^2 s_j)$; $Z_j = \lfloor \alpha_j(N_{j-1}+A_j)/(1-\alpha_j)\rfloor$ satisfies $0 \le \alpha_j - Z_j/N_j < 1/N_j$.
  - *Gram-matrix perturbation:* Replacing stage-$j$ points by shadowed de Bruijn rotations or $0$ moves at most $N_j$ points by $\le b^{-s_j}$ and at most $2s_j$ boundary points (at most $s_j$ at the end of each of the two stage-$j$ blocks) by $\le \frac{1}{2}$ on $\mathbb{T}$, giving $\bar\varepsilon \le b^{-s_j} + s_j/N_j$ and Lemma 5.6 norm change $\le \pi r_j^2(b^{-s_j} + s_j/N_j)$. The $b^{k_j}$ de Bruijn rotations lie one per $b$-adic interval of length $b^{-k_j}$, hence have discrepancy $\le 2 b^{-k_j}$ and $\|G^{\rm dB} - I\|_{\rm op} \le 2\pi(r_j - 1)b^{-k_j}$; $\|G^{\rm old} - I\|_{\rm op} \le r_j$; thus $\eta_j \to 0$.
  - *Root, energy, normality, and schedule:* Weyl's inequality gives $(\det G_{N_j, r_j}(1))^{1/r_j} \ge \lambda_{\min} \ge 1 - \alpha'_j - \eta_j \to 1$; reverse triangle inequality in Frobenius norm gives $\mathcal{E}_{N_j, r_j} \ge \frac{1}{2}(\alpha'_j\sqrt{r_j - 1} - \eta_j)^2 \to +\infty$ since $\alpha_j^2 r_j = r_j^{1/3}$; zero runs satisfy $Z_j \le 2\alpha_j N$ (since $1 - \alpha_j \ge 1/2$) and $\sum_{i<j} Z_i \le \alpha_{j-1}N_{j-1} + N_{j-2} = o(N_{j-1})$, while partial cycles and block boundaries are $O(b^{k_j} + jL) = o(N)$, establishing normality of $x$; splicing $r(N_j) = r_j$ with an optimal schedule $\rho(N)$ for $N \notin \{N_j\}$ yields $r(N) \to \infty$, $(\det G_{N, r(N)}(1))^{1/r(N)} \to 1$ along all $N$, and $\mathcal{E}_{N_j, r(N_j)} \to +\infty$. **Sound.**

### 4. Regressions & Evidence-Label Discipline

- No new mathematical errors, broken cross-references, or evidence-label regressions were introduced.
- Benchmark roster `BC-01`…`BC-50` is untouched (`D^+(ln 2; 2) < 1` remains `Open`); `[exact]` and `[finite]` boundaries are clean; external inputs and cross-model review caveats are accurately maintained.
- **Final Post-Repair Verdict:** **ACCEPT**.

*Cross-model review is not independent human peer review.*
