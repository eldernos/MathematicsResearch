# Independent Cross-Provider Referee Review — Phase 26, Track D (`D1`–`D4`)

**Targets audited:**
- [notes/phase26/euler-square-and-modular-determinants.md](../euler-square-and-modular-determinants.md)
- [scripts/phase26_euler_modular.py](../../../scripts/phase26_euler_modular.py)

**Disclaimer.** This document is an automated cross-provider AI referee review. **Cross-model review is not independent human peer review.**

---

## Executive Verdict: **REVISE**

The mathematical architecture of Track D is strong and genuine. Every headline theorem (`D1.1`–`D1.6`, `D2.3`, `D3.1`–`D3.4`, `D4.0`'s equality $K_2 = M_2$, `D4.1`, `D4.2`, `D4.3`) is mathematically sound at its core, the sharpness model in `D1.4` and the inertness construction in `D3.2` both survive adversarial testing, and the `D4.1` isolation/entropy/singular-series proof is clean and nontrivial.

However, the audit uncovered **4 Major defects** (literal false statements in the prose and/or an inverted rounding direction in a claimed "certified lower bound" in both the note and verifier script), alongside **9 Minor** gaps/clarifications. All 4 Major defects have short, surgical fixes and do not overturn the main conclusions, but they must be repaired before acceptance:

| ID | Severity | Location | Summary |
| --- | --- | --- | --- |
| M1 | **Major** | `D4.0` (note L295) | Unrestricted quantitative claim $D^+ \le 1 - \tau/2$ is **false** for $\tau > 1/2$ (counterexample: $x = 1/3$ has $\tau = 1$ and $D_\infty = 2/3 > 1/2$). Correct bound: $D^+ \le 1 - \min(1/4, \tau/2)$. (`D4.1` is unaffected since $\tau_{w,k} \ll 1/2$.) |
| M2 | **Major** | `D4.1` (note L311; script L653) | Claimed "Certified lower bound" $\tau_{3,93} > 2.23 \cdot 10^{-6}$ is **false** (true value $2.2269 \cdot 10^{-6} < 2.23 \cdot 10^{-6}$). Caused by printing lower bounds with round-to-nearest `{float(tau):.2e}` instead of exact outward `Fraction` assertions (same bug in script printout `tau(2k0)>4.44e-05` for $w = 4$, where true value is $4.4389 \cdot 10^{-5}$). |
| M3 | **Major** | `D2.2` (note L188; script L418–419) | Two literal errors: (a) claims the $9 \times 9$ mixed Gram matrix $G_m$ is invariant under $s \mapsto -s$ and checked as such by the verifier — **false** (its first row/column $[2501, 1, 1, 12, 12, -9, 34, 15, 15]$ negates under $s \mapsto -s$, and the script only checks sign-flip invariance of the $12 \times 12$ matrix $G$); (b) claims $\bigl(\begin{smallmatrix} S & \sum sg \\ \sum sg & \sum g^2 \end{smallmatrix}\bigr)$ is the *only* PSD matrix with $\sum s_i g_i$ and sign-free diagonal up to congruence — **false** (e.g., $\bigl(\begin{smallmatrix} \sum g & \sum sg \\ \sum sg & \sum g \end{smallmatrix}\bigr)$ from $(s_i\sqrt{g_i}, \sqrt{g_i})$). |
| M4 | **Major** | `D2.1` (note L163, L175) | Overclaims "all autocorrelations of $a$ of every order agree" and "higher moment tensors are built the same way" (and writes the 2-point diagonal as $C(\{i,j\},\varnothing)$). Allowing repeated shifts breaks the claim at order 3: $\mathbb{E}[a(m)^2 a(m+1)] = \mathbb{E}[u(m) a(m+1)]$ equals $-1/4$ in Model A vs. $0$ in Model B. Must restrict to distinct-shift (multilinear) autocorrelations (or odd leftmost multiplicity). |

**Critical findings:** None (0).  
**Major findings:** 4 (`M1`–`M4`).  
**Minor findings:** 9 (`m1`–`m9`).

---

## 1. Script Execution and Verification Audit

Command run directly on Windows (no WSL):

```sh
python -B scripts/phase26_euler_modular.py
```

- **Exit code:** `0`.
- **Assertion count:** `40,162` assertions executed via `check(...)`, matching the note (L354).
- **Zero floats in theorem assertions:** Verified by full code audit of lines 1–728. Every `check(...)` predicate uses exact `int` and `fractions.Fraction` arithmetic. In particular:
  - `pi_bounds()` (L69–73) uses Machin's alternating series truncated at opposite parities so `lo < pi < hi` holds rigorously.
  - `log2_bounds()` (L76–82) uses $2\operatorname{atanh}(1/3)$ with a valid geometric tail majorant $\frac{2}{25\cdot 3^{25}}\cdot\frac{9}{8}$.
  - `int(R / step)` in `inertness()` (L533) invokes `Fraction.__int__` (exact integer division, no float conversion).
  - `is_psd(M)` (L353–369) performs exact rational Schur-complement elimination on symmetric matrices, correctly rejecting negative pivots and nonzero off-diagonals on zero-pivot rows.
  - The sole floating-point routine `beta_sieve_exploration()` (L311–348) contains zero `check(...)` calls and is explicitly tagged `[exploration, floats, proves nothing]`.
- **Defects found in the script's certificate printouts:**
  - **M2 (script L653–654):** `d4_constants()` checks only `check(tau > 0)` and then prints `f"tau(k0)>{float(tau):.2e}"` and `f"tau(2k0)>{float(tau2):.2e}"`. Round-to-nearest formatting turns a lower bound into a **false** inequality whenever the 3rd significant digit rounds up:
    - $w = 3, k_0 = 93$: exact $\tau_{3,93} = 2.2269\ldots \times 10^{-6} < 2.23 \times 10^{-6}$, yet the script prints `tau(k0)>2.23e-06` (copied into note L311).
    - $w = 4, 2k_0 = 278$: exact $\tau_{4,278} = 4.4389\ldots \times 10^{-5} < 4.44 \times 10^{-5}$, yet the script prints `tau(2k0)>4.44e-05`.
  - **M3 (script L418–419):** `d2_checks()` prints `"12x12 signed Toeplitz Gram and 9x9 mixed Gram PSD and sign-flip invariant"`, but lines 381–383 only check sign-flip invariance of the $12\times 12$ matrix `G`, and direct evaluation confirms `Gm != Gm(-s)` because `Gm[0] = [2501, 1, 1, 12, 12, -9, 34, 15, 15]` negates in entries `1..8` under $s \mapsto -s$.
  - **m1 (Minor, script L229 & note L127):** `range(3 * Hs, Hmax, 7)` stops at $H = 2014$, not $H = 2016$ (the note says "a grid up to $H = 2016$").

---

## 2. Audit of D1 (Euler's Square: Sharpness of $1/(3\pi)$ & Optimality)

### Constant check & factorization (note L37–47)
- **Verified.** Using Wirsing's theorem for integers composed of primes $\equiv 1 \pmod{12}$ ($\tau = 1/4$) and Mertens' theorem $\prod_{p \le Y}(1-1/p)^{-1} \sim e^{\gamma_E}\log Y$, the count up to $Y$ is indeed $(e^{3\gamma_E/4}/(3\Gamma(1/4))) Y V(Y)$. Summing over square parts $v^2$ ($p \mid v \Rightarrow p \in \mathcal{P}$) with $X = 12N + 1$ multiplies by $12\prod_{\ell\in\mathcal{P}}(1-\ell^{-2})^{-1}$, yielding $\mathcal{W} = 4 e^{3\gamma_E/4}\prod_{\ell\in\mathcal{P}}(1-\ell^{-2})^{-1}/\Gamma(1/4)$ cleanly.
- The local cancellation $(1 - \frac{1}{\ell-1})(1 + \frac{1}{\ell(\ell-2)}) = 1 - \frac{1}{\ell}$ and $\Gamma$-reflection $\Gamma(7/4)\Gamma(1/4)4^{3/4}/4 = \frac{3}{4}(\pi\sqrt{2})(2\sqrt{2})/4 = 3\pi/4$ are exact.
- The factorization $\frac{3\pi}{4} = \bigl(\frac{3\pi\sqrt{2}}{16}\cdot 2^{3/4}\bigr) \times 2^{3/4}$ ($1.401002 \times 1.681793 = 2.356194$) is exact.

### Theorem D1.1 (Sign-conditioned gap law near zero)
- **Verified.** Replacing GF-43's triangular weights $(H-h)$ with uniform weights $1$ on $1 \le h \le H = \lfloor t/\rho \rfloor$:
  - Unselected endpoint mass is bounded via $\mathbf{1}[g \le H] \le (1 - w(m_i)) + w(m_i)\mathbf{1}[g \le H]$, costing $(\eta + o(1))S$.
  - Immediate predecessors with square part $> V$ are charged once each, costing $O(S/V) + o(S)$.
  - For each fixed squarefree $d$ coprime to $M_0$, $\frac{1}{H}\sum_{1 \le h \le H,\, d \mid h} b_v(h) \to b_*/d$ and is dominated by $1/d$, while $\sum_d \mu^2(d) r(d)/d < \infty$; dominated convergence gives the stated mean $b_*\prod_{\ell > T}(1 + \frac{1}{\ell(\ell-2)})$.
  - Pólya's argument for one-sided $\limsup$ bounds of monotone functions $F_{\sigma,N}(\tau)$ against continuous $K\tau$ holds verbatim on any compact $[0, T]$, and Fatou's lemma / uniform integration immediately recovers $\liminf W_\sigma/N \ge \frac{1}{2}\int_0^{1/K}(1-K\tau)\,d\tau = \frac{1}{4K} = \frac{1}{3\pi}$.
- **m2 (Minor, note L57):** The final limit order should mention $J_0 \to \infty$ and $\beta \uparrow 1/4$ alongside $\eta \to 0$ and $V, T \to \infty$, matching GF-43.

### Corollary D1.2 (First-order sign cancellation of small gaps)
- **Verified.** From $S_\sigma(1 - K\rho u) - o(S) \le \#\{s(m_i)=\sigma : g(m_i) > u\} \le S_\sigma$ uniformly for $u \in [0, t/\rho]$ (valid even if $K\rho u > 1$ since the lower bound turns negative while the count is $\ge 0$), integrating over $u \in [0, t/\rho]$ gives:
  - Signed sum: $\le \frac{S}{2} K\rho \cdot \frac{(t/\rho)^2}{2} + o(N) = (\frac{K}{4} t^2 + o(1)) N = (\frac{3\pi}{16} t^2 + o(1)) N$.
  - Unsigned sum: $\ge S(t/\rho) - \frac{S}{2} K\rho (t/\rho)^2 - o(N) = (t - \frac{3\pi}{8} t^2 - o(1)) N$.
  - Exact identity $\sum s\min(g, H) = H(S_+ - S_-) - \sum s(H-g)_+$ holds identically.

### Theorem D1.3 (Class $\mathfrak{B}(K)$ optimality & transfer formula)
- **Verified.**
  - **Part (a):** Since $\varphi(h) \le \Phi$ for all $h$, every term $\Phi - \varphi(h) \ge 0$, so dropping all predecessors except the nearest one ($h = g$) validates (ii). Since $\Phi - \varphi(h) \ge (\Phi - h)_+$ pointwise and $\varsigma \ge 0$, $\varphi = \min(\cdot, \Phi)$ maximizes the output for every fixed $\Phi$. Summation by parts with $\varsigma$ of mean $1$ gives $\frac{1}{2}\rho\Phi - \frac{1}{4}K\rho^2\Phi^2 = t/2 - Kt^2/4$, uniquely maximized at $t = 1/K$ with value $1/(4K)$.
  - **Part (b):** Algebra for $K(A, \theta) = \frac{A\Gamma(1/4)}{4e^{\gamma_E\delta}}\theta^{-\delta}$ and $\frac{1}{4K(A,\theta)} = \frac{A_{\rm Sel}}{A}\frac{(2\theta)^{3/4}}{3\pi}$ is exact. Crucially, removing primes $\ell \mid h$ from the sifting set decreases the local sifting density $g_h(\ell) \le g(\ell)$, so the one-sided sieve dimension condition ($\Omega_2(\delta, K_0)$ in *Opera de Cribro* Ch. 11) holds with a constant $K_0$ **uniformly in $h$**, and $V_h(z) = V_T(z)\prod_{T < \ell < z,\,\ell \mid h}(1 - \frac{1}{\ell-1})^{-1} \le V_T(z) R_T(h)$ reproduces the exact same local factor $R_T(h)$ as Selberg's sieve.
- **m3 (Minor, note L101):** In the proof of (b), "Take $z = D^{1/s}$ with $s$ small" can force $z > X$ if $s < \theta$; since $F(s) = A s^{-\delta}$ holds up to $s = \beta_\delta + 1 > 1 \ge \theta$ (for both Selberg and $\beta$-sieve), one may simply take $s = 1$ (i.e. $z = D \le X$), or any $s \in [\theta, \beta_\delta + 1]$.

### Theorem D1.4 (Sharpness model attaining $1/(4K)$)
- **Verified under adversarial stress-testing.** The alternating renewal model ($g_+ \sim \operatorname{Unif}\{1,\dots,H_*\}$, $g_- = L$, with $H_* = \lfloor 1/(K\rho)\rfloor$ and $L = \lfloor (2 - \frac{1}{2K})/\rho\rfloor$ on dyadic blocks) genuinely satisfies every property (a)–(e) for $K > 9/4$:
  - **(e):** $\mathbb{E}g_+ / (\mathbb{E}g_+ + L) = \frac{1/(2K\rho) + O(1)}{2/\rho + O(1)} \to \frac{1}{4K}$, independent of the block parameter $\rho$.
  - **(c) for $+$ endpoints:**
    - $H \le H_* + 1$: exact triangular sum $H(H-1)/(2H_*) \le H^2/(2H_*)$; uniform count $H/H_* = K\rho H$.
    - $H_* < H \le L$: only $D_1 = g$ contributes; $\mathbb{E}(H - g) = H - (H_*+1)/2 \le H^2/(2H_*)$ since $(H-H_*)^2 + H_* \ge 0$; uniform count $1 < H/H_* = K\rho H$.
    - $H > L$: $D_{2i}, D_{2i+1} \ge iL$ gives triangular sum $\le H + 2\sum_{i\ge 1}(H - iL)_+ \le H + H^2/L$ (exact algebraic check: $H^2/L - (2mH - m(m+1)L) = (H-mL)^2/L + mL > 0$). Dividing by $H^2$, $1/H + 1/L < 2/L \le K\rho/2$ once $L \ge 4/(K\rho)$, i.e. $2 - \frac{1}{2K} \ge \frac{4}{K} \iff K \ge 9/4$ (strict inequality $K > 9/4$ absorbs rounding). Uniform count $\le 1 + 2\lfloor H/L \rfloor \le K\rho H$ once $3/L \le K\rho \iff K \ge 7/4$.
  - **(c) for $-$ endpoints:** For $H \le L$, zero predecessors. For $H > L$, $D_{2i-1}^-, D_{2i}^- \ge iL$, so the triangular sum is $\le 2\sum_{i\ge 1}(H - iL)_+ \le H^2/L \le K\rho H^2/2$ (needs only $K \ge 5/4$) and the uniform count is $\le 2\lfloor H/L\rfloor \le K\rho H$ (needs only $K \ge 5/4$).
  - **Early-block density effect (checked):** If $\rho(x)$ is slowly varying (e.g. $(\log x)^{-3/4}$ or slower) with $x\rho(x)^3 \to \infty$, then pairs with $m \le 2H$ contribute $O(H^2) = O(t^2/\rho(N)^2) = o(N\rho(N))$, and for $2H < m \le N$ the density on $[m-H, m]$ is $\le \rho(m/2) \sim \rho(m)$, so summing over earlier blocks gives $\int_{2H}^N \rho(x)\rho(x/2)\,dx \sim N\rho(N)^2$ by Karamata's theorem, preserving (c) globally as well as (a) and (d).
  - **(b) Equidistribution mod $q$:** Because $g_+ \sim \operatorname{Unif}\{1,\dots,H_*\}$ is independent of the past, conditioned on $m_{2i-2}$ the residues $m_{2i-1} \bmod q$ and $m_{2i} = (m_{2i-1} + L) \bmod q$ each hit every class $a \bmod q$ with conditional probability $\frac{1}{q} + O(1/H_*)$. Martingale LLN / Azuma–Hoeffding therefore yields a.s. equidistribution mod $q$ for both signs even with block-varying parameters.
  - **Caveat worth noting:** The model has a point spike $P_L^- = S_-$ at $h = L$, so it satisfies the *averaged* bounds (c) (and pointwise bounds up to $H_* = \lfloor 1/(K\rho)\rfloor$), not a uniform pointwise bound $P_h^- \le K\rho S_-$ at $h = L$. This does **not** weaken D1.4, because GF-43 Theorem 1 only uses averaged/immediate-predecessor bounds (as its $v > V$ charging step prevents a uniform pointwise bound at scale $\rho$).
- **m4 (Minor, note L105, L117–125):** Three small proof-writing omissions in D1.4:
  1. The proof states `1 + 2\lfloor H/L\rfloor \le K\rho H` without restricting it to $H \ge L$ (for $H \le H_*$, the bound fails because $K\rho H \le 1$; one uses $\mathbb{E}[\mathbf{1}(g \le H)] = H/H_* = K\rho H$ for $H \le H_*$ and $1 \le H/H_*$ for $H_* < H < L$).
  2. For $-$ endpoints, the proof stops at "no predecessor closer than $L$" and omits the 1-line check for $H > L$ ($D_{2i-1}^-, D_{2i}^- \ge iL$).
  3. Specify that $\rho(N)$ is slowly varying (with $N\rho(N)^3 \to \infty$) so early-block sums satisfy Karamata's theorem, state explicitly that a deterministic realization $(U^*, s^*)$ exists a.s., and invoke the direct one-step conditional mixing $\frac{1}{q} + O(1/H_*)$ + martingale LLN rather than "the ergodic theorem" (since block-varying $(H_*, L)$ makes the chain time-inhomogeneous).

### D1.5 & D1.6 (Conditional bounds & warning model)
- **D1.5 Verified.** Level $\theta$ gives $(2\theta)^{3/4}/(3\pi)$, certified in $(0.1784, 0.1785)$ at $\theta = 1$. Under (H1)–(H2) ($A_{3/4} \le 2.21$), $A_{\rm Sel}/(3\pi\cdot 2.21) = 0.114410 > 0.1144$.
- **m5 (Minor, note L135 & script L313–348):** An independent grid-aligned Simpson solver for the $\beta$-sieve DDE at $\kappa = 3/4$ gives $\beta_{3/4} \approx 1.3981$, $A_{3/4} \approx 2.2020$ ($A_{3/4}/A_{\rm Sel} \approx 0.9240$, implied bound $\approx 0.1148$, combined with $\theta = 1$: $\approx 0.1931$), versus the script's $O(h)$-discretized values $1.399 / 2.2054 / 0.1146$. Both are well below hypothesis (H2) ($A_{3/4} \le 2.21$) and properly tagged `[exploration, floats, not a certificate]`.
- **D1.6 Verified.** Exact stationary law and $\Phi = 1/2$ are elementary and checked.

---

## 3. Audit of D2 (Modular Positivity and Determinant Methods)

### Theorem D2.1 (Signed-leftmost data are blind to gap weights)
- **Core result verified, but overclaimed for repeated shifts (`M4`).**
  - Under the stationary Palm measure of the renewal process with i.i.d. gaps in $\{1, 3\}$, $s_0$ depends solely on $g_0$ while all future support indicators $u(h)$ and signed values $a(h)$ ($h > 0$) depend solely on $(g_1, g_2, \dots)$. Since $\mathbb{E}[s_0] = 0$, **every** squarefree correlation $C(T_a, T_u)$ with $\min(T_a \cup T_u) \in T_a$ vanishes identically in both Model A and Model B. Pure support correlations ($T_a = \varnothing$) and all 2-point Gram/Hankel/Toeplitz matrices $\mathbb{E}[a(m+i)a(m+j)]$ (where $i = j$ gives $\mathbb{E}[u(m+i)] = 1/2$ and $i \ne j$ gives $0$) also agree identically, while $\Phi_A = 1/2 \ne 0 = \Phi_B$.
- **M4 (Major, note L163, L175):**
  1. Line 163 writes: *"Gram, Hankel and Toeplitz matrices of $a$ have entries $C(\{i, j\}, \varnothing)$; higher moment tensors are built the same way."* Strictly, as a *set*, $\{i, i\} = \{i\}$, so $C(\{i, i\}, \varnothing) = \mathbb{E}[a(m+i)] = 0 \ne \mathbb{E}[a(m+i)^2] = C(\varnothing, \{i\}) = 1/2$.
  2. More seriously, line 175 claims *"so in particular all autocorrelations of $a$ of every order agree."* If repeated shifts are permitted — as in standard higher-order moment tensors $T_{i_1,\dots,i_r} = \mathbb{E}[\prod_{t=1}^r a(m+i_t)]$ or degree-$d$ Lasserre/SOS moment matrices of $a$ — this is **false already at order 3**:
     $$\mathbb{E}\bigl[a(m)^2 a(m+1)\bigr] = \mathbb{E}\bigl[u(m) a(m+1)\bigr] = C(\{1\}, \{0\}) = \begin{cases} -1/4 & \text{in Model A,} \\ 0 & \text{in Model B.} \end{cases}$$
     Squaring the leftmost factor strips its sign ($a(m)^2 = u(m)$) and converts a 3rd-order autocorrelation of $a$ into a predecessor-type correlation! The verifier (`d1_warning_and_gram_models`, L276–282) only tested strictly increasing triples ($d, e \ge 1$) and missed $i = j < k$.
  3. **Required fix:** Restrict the claim in L163 and L175 to **distinct-shift (multilinear) autocorrelations** (or monomials whose leftmost shift appears to an odd power), and explicitly note that 2-point Gram/Hankel/Toeplitz diagonals are $C(\varnothing, \{i\})$ (pure support, so 2-point matrices still match).

### Lemma D2.2 (Gap-indexed Gram collapse & bordered Gram bound)
- **Part (a) verified:** $v_i v_i^{\mathsf{T}} = s_i^2 e_{\psi(g_i)} e_{\psi(g_i)}^{\mathsf{T}} = e_{\psi(g_i)} e_{\psi(g_i)}^{\mathsf{T}}$.
- **M3 (Major, note L188 & script L418–419) — two literal misstatements:**
  1. **False uniqueness claim in part (b):** Line 188 asserts *"The only PSD matrix containing $\sum s_i g_i$ as an entry with sign-free diagonal is, up to congruence, $\begin{pmatrix} S & \sum s g \\ \sum s g & \sum g^2 \end{pmatrix}$."* This is **false**. For instance, the $2 \times 2$ Gram matrix of $(s_i \sqrt{g_i}, \sqrt{g_i})$ is
     $$\begin{pmatrix} \sum g & \sum s g \\ \sum s g & \sum g \end{pmatrix},$$
     which is PSD, has sign-free diagonal, contains $\sum s_i g_i$, and is **not** congruent to $\bigl(\begin{smallmatrix} S & \sum sg \\ \sum sg & \sum g^2 \end{smallmatrix}\bigr)$ whenever the $g_i$ are not all equal (more generally, $(s_i g_i^{\alpha/2}, g_i^{1-\alpha/2})$ works for every $\alpha \in \mathbb{R}$). **Recommended fix (strictly stronger and true):** State that for *any* $2\times 2$ Gram matrix $\sum_i (x_i, y_i)^{\mathsf{T}}(x_i, y_i)$ with $x_i y_i = s_i g_i$, Cauchy–Schwarz gives $\sqrt{(\sum x_i^2)(\sum y_i^2)} \ge \sum |x_i y_i| = \sum g_i$, so every $2\times 2$ Gram bound is vacuous (at least $\sum g_i$).
  2. **False sign-flip invariance claim for $G_m$:** Line 188 claims the verifier *"checks exactly that the $12\times 12$ signed Toeplitz Gram matrix and a $9\times 9$ mixed Gram matrix are PSD and invariant under $s \mapsto -s$,"* and script L418–419 prints the same. In fact, $G_m$ has first row $[2501, 1, 1, 12, 12, -9, 34, 15, 15]$, whose entries $1\ldots 8$ **negate** under $s \mapsto -s$ (so $G_m(-s) = J G_m(s) J \ne G_m(s)$ for $J = \operatorname{diag}(-1, 1, \dots, 1)$; PSD-ness is invariant, not the matrix itself), and `d2_checks()` never asserts sign-flip invariance of `Gm`. **Required fix:** Restrict "invariant under $s \mapsto -s$" to the $12\times 12$ matrix $G$ in both note L188 and script L418–419 (noting that $G_m$ is PSD and conjugate under $s \mapsto -s$, while its first row holds the sign-sensitive backward sums).

### Theorem D2.3 (The moment–positivity ceiling)
- **Verified.** When $\sum_{h < H} u_h \le 1$, the distribution $\mu^*(e_h) = u_h$, $\mu^*(0) = 1 - \sum_{h<H} u_h$ is a genuine probability law on $\{0, 1\}^{H-1}$ whose higher moments $\mathbb{E}_{\mu^*}[\prod_{h\in S}\omega_h]$ ($|S| \ge 2$) all vanish identically and which attains $\mathbb{E}_{\mu^*}[\min(g, H)] = H - \sum_{h<H}(H-h)u_h$. Hence no valid inequality for probability laws (PSD moment matrices, Lasserre/SOS hierarchies, Bonferroni, Hunter, Kounias, de Caen) combined with upper correlation bounds of any order can improve the bound.
- **m6 (Minor, note L192–200):** What if an analyst chooses $H > 1/(K\rho)$, where $\sum_{h<H} u_h > 1$? In that regime the greedy singleton law placing mass $u_h$ on $e_1, \dots, e_{H_0 - 1}$ and the residual mass $1 - \sum_{h < H_0} u_h$ on $e_{H_0}$ (where $H_0$ is the first index with $\sum_{h \le H_0} u_h \ge 1$) is *still* a genuine probability law with all higher moments identically $0$ and still achieves the same $1/(4K)$ ceiling. Adding one sentence noting this makes the exclusion of arbitrary-horizon Lasserre/Bonferroni arguments completely self-contained.

---

## 4. Audit of D3 (Theta Cube & Fourth Power)

### §3.1 Prior art (BBCP 2004)
- **Verified.** Confirmed via independent literature check: Bailey, Borwein, Crandall, and Pomerance, *On the binary expansions of algebraic numbers*, *J. Théor. Nombres Bordeaux* **16** (2004), no. 3, 487–518, DOI `10.5802/jtnb.457`. Correcting the erroneous *Experimental Mathematics* 13(3) citation from the Track D brief is accurate.

### Proposition D3.1 (Exact identities)
- **Verified for ALL $n \ge 0$ (both algebraically and numerically).**
  - Checked $r_3(n) = 12(H(4n) - 2H(n))$ directly against naive 3-square counting for all $0 \le n \le 600$ (including $n = 0$: $12(H(0)-2H(0)) = -12(-1/12) = 1 = r_3(0)$), with zero discrepancies.
  - Verified algebraically for all $n \ge 1$ across all residue classes mod $8$ via the Hurwitz 2-conductor relation:
    - $n \equiv 1, 2 \pmod 4$: $H(n) = 0$ and Gauss gives $r_3(n) = 12 H(4n)$.
    - $n \equiv 3 \pmod 8$: $d_0 \equiv 5 \pmod 8 \Rightarrow (\frac{d_0}{2}) = -1 \Rightarrow H(4n) = (3 - (-1)) H(n) = 4 H(n)$, so $12(H(4n) - 2H(n)) = 24 H(n) = r_3(n)$ (checked for non-squarefree values $n = 27, 75, 99, 147, 243$ as well as $n = 3$).
    - $n \equiv 7 \pmod 8$: $d_0 \equiv 1 \pmod 8 \Rightarrow (\frac{d_0}{2}) = +1 \Rightarrow H(4n) = 2 H(n)$, so $12(H(4n) - 2H(n)) = 0$.
    - $n = 4^a m$ ($a \ge 1, 4 \nmid m$): $H(4^{a+1} m) - H(4^a m) = 2(H(4^a m) - H(4^{a-1} m))$ implies $H(4n) - 2H(n)$ is invariant under $n \mapsto 4n$, matching $r_3(4n) = r_3(n)$.
  - Items (2), (3) ($8q^3\psi(q^8)^3$), and (4) ($r_4(2^a u) = 24\sigma(u)$ for $a \ge 1$, $r_4(4n) = r_4(2n)$) are all exact.
- **m7 (Minor, note L235):** Line 235 states "$24 H(n)$ for $n \equiv 3 \bmod 8$ with $n > 3$." With Hurwitz class numbers $H$ (which already include automorphism weights, $H(3) = 1/3$, $H(12) = 4/3$), $r_3(3) = 8 = 24 H(3)$ holds for $n = 3$ as well; the restriction $n > 3$ is only needed for unweighted $h(-n)$.

### Theorem D3.2 (Inertness of Legendre, 2-adic, scaling, and size data)
- **Verified.** Both the $r_3$ and $r_4$ constructions satisfy (a)–(d) and fill the entire stated interval via Kakeya's greedy algorithm:
  - Consecutive gaps in $\mathfrak{F}_3 = \{m \ge 1 : m \bmod 8 \in \{1,2,3,5,6\}\}$ are $\le 3$, and in $\mathfrak{F}_4 = \{m \ge 1 : m \not\equiv 0 \bmod 4\}$ are $\le 2$.
  - For $r_3$, $w_m = \sum_{i\ge 0} 2^{-k 4^i m} \le 2\cdot 2^{-km} \le 2^{3k+1} w_{m'} < J w_{m'}$ ($J = 2^{3k+2}$).
  - For $r_4$, $\mathrm{rep}_4(n)$ gives orbit $\{m\}$ for odd $m$ and $\{2^i m : i \ge 0\}$ for $m \equiv 2 \pmod 4$, preserving $a_{4n} = a_{2n}$ and still satisfying $w_m \le 2\cdot 2^{-km} < J w_{m'}$.
  - In (d): $r_3(n) \to \infty$ in density on its support (since $r_3(d) \mid r_3(n)$ for squarefree part $d$, and by Heilbronn/Siegel only $O_M(1)$ squarefree $d$ have $r_3(d) \le M$, so $\#\{n \le X : 0 < r_3(n) \le M\} \ll_M \sqrt{X} = o(X)$), and similarly $r_4(n) \to \infty$ in density; subadditivity gives $w(a_n) \ge w(r_3(n)) - w(2^t j) = w(r_3(n)) - w(j) \ge w(r_3(n)) - (3k+3) \ge w(r_3(n)) - (t+3k+3)$.
- **m8 (Minor, note L244–257):** Three small phrasing cleanups:
  1. State explicitly that $a_0 = r_j(0) = 1$ (the perturbation acts on $n \ge 1$).
  2. In (d), clarify "$a_n/r_3(n) \to 1$ in density *on the support*" (since $r_3(n) = 0$ on a set of density $1/6$).
  3. For $r_4$ (L257), note that the interval upper endpoint uses $w_m = \sum_{\mathrm{rep}_4(n) = m} 2^{-kn}$ (giving upper endpoint $x_{4,k} + 2^t J / (2^k - 1)$), matching the script (L517), rather than $\sum_{i \ge 0} 2^{-k 4^i m}$ from L254.

### Proposition D3.3 ($v_2(r_4(n))/\log\log n \to 2$ in density)
- **Verified.** $v_2(r_4(n)) = 3 + \sum_{p^e \parallel n,\, p \text{ odd}} b_p(e)$ holds for both odd and even $n$ ($v_2(8) = v_2(24) = 3$). Layer-cake plus Dirichlet/Mertens in progressions gives the main term $\sum_{j \le J} 2^{1-j}\log\log X + O_J(1)$. For $j > J$, splitting $p \le 2^{2j}$ (trivial arithmetic progression sum $\ll j 2^{-j}$) and $2^{2j} < p \le X$ (Brun–Titchmarsh with $\log(t/2^j) \ge \frac{1}{2}\log t$ plus partial summation $\ll 2^{-j}\log\log X$) rigorously gives $O((\log\log X + J) 2^{-J})$ for the first moment and $O((J\log\log X + J^2) 2^{-J})$ for the second moment. Prime powers ($e \ge 2$) contribute $O(1)$. Turán–Kubilius and Chebyshev conclude the proof.

### Corollary D3.4 (Sharp carry order for the fourth power)
- **Verified.** Direct rearrangement of GF-43's exact column identity combined with $w \le s_2 \ll \log M$ and GF-43 Theorem 2 yields $K_M \asymp M\log M$ for $x_{4,k}$ and $M \ll o(K_M)$, $K_M \ll M\log M$ for $x_{3,k}$.

---

## 5. Audit of D4 ($K_2 = M_2$, Prime Subseries $D^+ < 1$, Dichotomy)

### Lemma D4.0 ($K_2 = M_2$ in base 2)
- **$K_2 = M_2$ is 100% verified and cleanly proved.**
  - $M_2 \subset K_2$: Markov's inequality on $[\epsilon, 1-\epsilon)$ gives $D_N \ge 1 - 2\epsilon - o(1)$.
  - $K_2 \subset M_2$: If $D_N > 1 - \eta$ ($\eta < 1/4$), either (i) at least $(1-\eta)N$ points lie in an interval $[a, b)$ of length $< \eta$, whence at least $(1 - 2\eta)N - 1$ consecutive pairs $(y_n, y_{n+1})$ both lie in $[a, b)$; crucially, in base $2$, $|\{2y\} - y| = \|y\|$ **identically on $[0, 1)$** ($2y - y = y$ on $[0, 1/2)$ and $y - (2y - 1) = 1 - y$ on $[1/2, 1)$), forcing $\|y_n\| < \eta$; or (ii) $[a, b) \supset [\eta, 1-\eta)$ contains $< \eta N$ points. Both cases yield $\frac{1}{N}\sum_{n<N} \|y_n\| \le 2\eta + \frac{1}{2N}$.
  - *(Note on $b \ge 3$)*: As expected, $K_b \ne M_b$ for $b \ge 3$ because $T_b$ has nonzero fixed points $k/(b-1)$ ($1 \le k \le b-2$), e.g. $1/2 \in K_3 \setminus M_3$ ($D_N(1/2; 3) = 1$ while $\|3^n/2\| = 1/2$). Base $2$ is special precisely because $0$ is the unique fixed point of $T_2$ on $\mathbb{T}$.
- **M1 (Major, note L295) — quantitative bound $D^+ \le 1 - \tau/2$ is FALSE as stated:**
  - Line 295 states: *"If adjacent unequal binary digits have lower density $\tau$, then $D^+ \le 1 - \tau/2$. A transition at position $n$ means exactly $y_n \in [1/4, 3/4)$, and that interval meets neither of the two concentrated configurations."*
  - **Counterexample:** Take $x = 1/3 = 0.010101\ldots_2$. Every orbit point $y_n \in \{1/3, 2/3\}$ lies in $[1/4, 3/4)$, so the transition density is $\tau = 1$. Yet $D_\infty(1/3; 2) = 2/3$ (witnessed by $[1/3, 2/3 + \epsilon)$, which captures mass $1$ in length $1/3 + \epsilon$; also listed in [docs/research-objectives.md](../../../docs/research-objectives.md) L68). Here $D^+ = 2/3 > 1/2 = 1 - \tau/2$.
  - **Root cause:** The disjointness of $[1/4, 3/4)$ from $\{y : \|y\| < \eta\}$ and the inclusion $[1/4, 3/4) \subset [\eta, 1-\eta)$ both require $\eta \le 1/4$. Thus $D_N > 1 - \eta$ forces $\tau_N \le 2\eta + 1/N$ **only when $\eta < 1/4$**.
  - **Required fix:** Change $D^+ \le 1 - \tau/2$ to $D^+ \le 1 - \min(1/4, \tau/2) = \max(3/4, 1 - \tau/2)$ (or assume $\tau \le 1/2$).
  - **Downstream impact:** Zero impact on Theorem D4.1 or D4.2, because every $\tau_{w,k}$ (and $\tau_{w,k}^{\rm Euler}$) in D4.1 is $\ll 1/2$ (below $10^{-3}$), so $\min(1/4, \tau_{w,k}/2) = \tau_{w,k}/2$.

### Theorem D4.1 (Large-stretch prime subseries are outside $K_2$)
- **Theorem statement and proof verified (modulo `M2` below).**
  - **Isolation:** $k H_p = \frac{w-1}{2}\log_2(4p) + 4 \ge L_p + 4 > L_p + 2$, ensuring $I_p \equiv 0 \pmod{2^{L_p + 2}}$ and strictly disjoint windows. Tail bound $|\tau_p| \le \frac{2}{16} 2^{-(w-1)/2} (1 - 2^{-k})^{-1} + o(1) < 0.18 < 1$ for large $p$.
  - **Transitions per isolated prime:** For both signs of $a_f(p)$ and both $\varepsilon \in \{0, -1\}$, the $(L_p+2)$-bit window is the unsigned binary string (or bitwise complement) of $M \in \{A, A-1\}$ ($A = |a_f(p)|$) whose MSB is $0$. Since the left edge is $0$, at most the right edge can meet a run of ones, giving $T(M) \ge 2 R(M) - 1 \ge w(M) - 1 \ge w(A) - 2$. Confirmed exhaustively in Python for all $1 \le A \le 2048$, both signs, and both $\varepsilon$.
  - **Counting isolated primes:** Selberg's 2-dimensional upper bound for prime pairs (Halberstam–Richert, *Sieve Methods*, Thm. 3.11) gives $\le (16 + o(1)) C_2 \prod_{p\mid h,\, p>2}\frac{p-1}{p-2} \frac{2X}{\log^2 X} = (8 + o(1)) \mathfrak{S}(h) \frac{2X}{\log^2 X}$ with $\mathfrak{S}(h) = 2 C_2 \prod_{p\mid h,\, p>2} \frac{p-1}{p-2}$ ($h$ even). Counting both left and right neighbors within $H = \max_{p\in(X,2X]} H_p = \lambda\log X + O(1)$ gives $(32 + o(1)) \frac{X}{\log^2 X} \sum_{h\le H}\mathfrak{S}(h)$.
  - **Exact singular-series inequality $\sum_{h \le H} \mathfrak{S}(h) \le H$:** Verified algebraically for **every** integer $H \ge 1$: writing $h = 2m$ ($1 \le m \le M = \lfloor H/2\rfloor$) and expanding $\prod_{p\mid m,\, p>2}(1 + \frac{1}{p-2})$ over odd squarefree $d \mid m$ yields
    $$\sum_{h \le H} \mathfrak{S}(h) = 2 C_2 \sum_{d \text{ odd}} \mu^2(d)\Bigl(\prod_{p \mid d}\frac{1}{p-2}\Bigr)\Bigl\lfloor\frac{M}{d}\Bigr\rfloor \le 2 C_2 M \prod_{p > 2}\Bigl(1 + \frac{1}{p(p-2)}\Bigr) = 2M \le H.$$
  - **Entropy & polynomial root count:** Every split prime in $\mathbb{Q}(\sqrt{-3})$ has a generator $\pi = x + y\sqrt{-3}$ with $x, y \in \mathbb{Z}$, $|y| \le \sqrt{2X/3} < \sqrt{2X}$ (and in $\mathbb{Q}(i)$, $p = x^2 + y^2$, $|y| \le \sqrt{2X}$). All unit polynomials $\operatorname{Tr}(\zeta \pi^{w-1}) - v$ in $x$ are nonconstant of degree $\le w - 1$: in particular, for $w = 3, \zeta = \pm i$, $\operatorname{Tr}(\pm i(x+yi)^2) = \mp 4xy$ has $y \ne 0$ because $p = x^2$ cannot be prime. The Chernoff bound $\sum_{j \le \alpha n}\binom{n}{j} 2^j \le 2^{n(H(\alpha) + \alpha)}$ for $\alpha \le 2/3$ with $t = \alpha/(2(1-\alpha))$ is exact, and $(w-1)(H(c'_w) + c'_w) < 1$ holds for $c'_2 = 1/5$ ($0.9219$), $c'_3 = 2/25$ ($0.9644$), $c'_4 = 1/22$ ($0.9367$).
  - **Thresholds:** All six exact integer thresholds verified independently:
    - Fourier index: $32(w-1)/\log 2 \approx 46.166, 92.332, 138.499 \implies k \ge 47, 93, 139$.
    - Euler index: $32 c (w-1)/\log 2 \approx 276.997, 369.330, 415.496 \implies k \ge 277, 370, 416$ (and $\{p \equiv 1 \bmod c\}$ matches the split primes exactly in all three cases $(r,c,w) = (4,6,2), (6,4,3), (8,3,4)$).
- **M2 (Major, note L311 & script L653–654):** As detailed in §1, the claimed "certified lower bound" $\tau_{3,93} > 2.23 \cdot 10^{-6}$ is **false** ($\tau_{3,93} \approx 2.2269 \cdot 10^{-6}$), and the script printout `tau(2k0)>4.44e-05` for $w = 4$ is also **false** ($\tau_{4,278} \approx 4.4389 \cdot 10^{-5}$). **Required fix:** Change note L311 to $\tau_{3,93} > 2.22 \cdot 10^{-6}$, add explicit exact `Fraction` assertions in `d4_constants()` for every quoted numerical lower bound, and truncate downward (never round-to-nearest) when formatting lower bounds.
- **m9 (Minor, note L311, L315, L319):**
  1. L315: Briefly note why the $-2$ in $w(|a_f(p)|) - 2$ covers both the right window edge ($-1$, the MSB being guaranteed $0$ after complementing negative coefficients) and $w(A-1) \ge w(A) - 1$ ($-1$).
  2. L319: Note explicitly that $y \ne 0$ for prime $p = x^2 + y^2$, excluding degeneracy of $\operatorname{Tr}(\pm i(x+yi)^2) = \mp 4xy$.
  3. L311: "with $\lambda$ replaced by $c\lambda$ and $\tau$ multiplied by $c$" is slightly ambiguous — clarify "replacing $k$ by $k/c$ in $\tau_{w,k}$" (so $\lambda \mapsto c\lambda$ inside $(\frac{1}{2} - 32\lambda)$ *and* the outer factor multiplies by $c$).

### Theorem D4.2 (Dichotomy for full Euler powers)
- **Verified.** $E(2^{-k})^r = P_{r,k} + C_{r,k}$, $P_{r,k} \notin K_2$ by D4.1, and $K_2 = M_2$ (D4.0) is an additive subgroup of $\mathbb{R}$. Completely airtight.

### Proposition D4.3 (Composite complement & telescoping counterexample)
- **Verified.**
  - The CM support law ($a_f(n) \ne 0$ iff every inert prime has even exponent) holds for all $n = cj+1 \ge 1$ because unique factorization in $\mathcal{O}_K$ ($\mathbb{Z}[\omega]$ or $\mathbb{Z}[i]$) prevents $(\pi/\bar{\pi})^{e+1} = 1$, so $a_f(p^e) \ne 0$ for every split prime power $p^e$. Wirsing's theorem then gives support count $\asymp M/\sqrt{\log M}$ (density zero).
  - The telescoping sequence $d_n = (4^{b(n)} - 1)/3$, $c_n = 2d_n - d_{n+1}$ is completely valid for all $n \ge 1$: for $n \ne 2^m - 1$, $c_n = (4^m - 1)/3 > 0$ has exact NAF weight $m = b(n)$; for $n = 2^m - 1$, $c_n = -(2\cdot 4^m + 1)/3 < 0$ has NAF weight $m + 1$. Since $d_{N+1} = O(N^2)$, $\sum_{n=1}^N c_n 2^{-n} = d_1 - d_{N+1}/2^N \to 1 \in M_2$ absolutely while mean NAF weight is $\log_2 N + O(1) \to \infty$.
- *(Minor terminology note, paired with m9)*: In L333, "mean minimum signed weight of its coefficients is $\asymp \sqrt{\log M}$" divides total weight ($\asymp M\sqrt{\log M}$, GF-27 Corollary D4.15) by *all* $M$ indices (including zeros), whereas the finite measurement on L342 (and script L695) computes "composite mean NAF weight" by dividing by `len(comp)` (supported composite indices, whose asymptotic mean is $\asymp \log M$). Clarifying the denominator in L333 ("mean per index $1 \le j \le M$ is $\asymp \sqrt{\log M}$, and per supported composite index is $\asymp \log M$") avoids any reader confusion.

---

## 6. Evidence Labels & Benchmark Integrity Check

- Evidence labels in the summary table (L11–29) and §5 (L383–390) strictly adhere to [docs/research-objectives.md](../../../docs/research-objectives.md):
  - `Paper proof`, `Conditional`, `External input`, `Finite certificate`, `Open`, `[finite]`, and `[exploration]` are cleanly separated.
  - Benchmark statuses (`BC-29`, theta powers, higher Euler powers) are left unchanged, as required.
  - The note explicitly states that cross-model review is not independent human peer review (L9, L390).
- Once the 4 Major defects (`M1`–`M4`) are fixed (and the `M2` certified bounds are backed by exact `Fraction` assertions in `d4_constants()`), Track D will be ready for **ACCEPT**.

---

## Post-Repair Verification

**Post-Repair Verdict: ACCEPT**

**Disclaimer.** This post-repair verification is an automated cross-provider AI review. **Cross-model review is not independent human peer review.**

### 1. Script Re-Execution and Exact-Arithmetic Audit

Executed directly on Windows (no WSL):

```sh
python -B scripts/phase26_euler_modular.py
```

- **Exit code:** `0`.
- **Assertion count:** `44,890` exact assertions passed (`All exact checks passed: 44890 assertions.`), matching the repaired note (L419).
- **Zero floats in `check(...)` predicates:** Verified by full code review and AST audit of all `104` `check(...)` call sites, all float literals/`float()` calls, and all `/` operations in `scripts/phase26_euler_modular.py`. Every `check(...)` predicate evaluates strictly over `int`, `bool`, and `fractions.Fraction` (including negative integer powers `F(g) ** (2 * e)`, `F(10) ** e`, and exact `Fraction.__int__` in `floor_sci3` and `inertness`). All float literals reside exclusively inside `beta_sieve_exploration()` (zero `check(...)` calls, tagged `[exploration, floats, proves nothing]`) or print-only formatting for `[finite]`/target summaries.

### 2. Finding-by-Finding Resolution Audit

| ID | Status | Verified Resolution |
| --- | --- | --- |
| **M1** | **Resolved** | Note L26, L339–347, L446 state and prove $D^+ \le 1 - \min(1/4, \tau/2)$, explain why $\eta \le 1/4$ is essential with the $x = 1/3$ counterexample ($\tau = 1, D^+ = 2/3$), and verify that the cap is inactive in D4.1 ($\tau_{w,k} \le c'_w/1024 \le 1/5120 < 1/2$, L357, L369). Script `d4_quantitative_k2()` (L808–850) exactly checks all $121$ primitive binary cycles $a/d$ ($d$ odd $\le 99$), verifying $D \le 1 - \min(1/4, \tau/2)$ for every cycle and $D = 2/3 > 1 - \tau/2$ uniquely at $d = 3$. |
| **M2** | **Resolved** | Note L371, L445 quote downward 3-significant-digit truncations ($\tau_{2,47} > 1.36\cdot 10^{-5}$, $\tau_{2,94} > 1.95\cdot 10^{-4}$, $\tau_{3,93} > 2.22\cdot 10^{-6}$, $\tau_{3,186} > 7.81\cdot 10^{-5}$, $\tau_{4,139} > 6.38\cdot 10^{-7}$, $\tau_{4,278} > 4.43\cdot 10^{-5}$) and record the prior round-to-nearest bug. Script `d4_constants()` (L741–795) computes a strict rational lower bound `tau` (using `log_lo` inside `lam` and `log_hi` in the outer factor), asserts `tau > bound`, `tau < bound + ulp`, and `floor_sci3(tau) == (m, e)` for all 6 entries in `CERTIFIED_TAU`, and formats them via integer-only `sci3(m, e)`. |
| **M3** | **Resolved** | (a) Note L20, L208–220 replace the false uniqueness claim with the strictly stronger Cauchy–Schwarz theorem for all real (and $\mathbb{R}^d$-vector) factorizations $x_i y_i = s_i g_i$, attaining $\sum g_i$ at $(s_i\sqrt{g_i}, \sqrt{g_i})$; script L471–481 checks the family $e \in \{-1, 0, 2, 3\}$ and the equality matrix `[[g1, sg], [sg, g1]]`. (b) Note L222, L432 and script L446–453, L513–516 cleanly separate sign-flip invariance of the $12\times 12$ Toeplitz Gram $G$ from the exact congruence $G_m(-s) = J G_m(s) J$ ($J = \operatorname{diag}(-1, 1, \dots, 1)$) of the $9\times 9$ mixed Gram $G_m$, explicitly asserting `Gm_neg != Gm` and negation of all 8 mixed entries. |
| **M4** | **Resolved** | Note L19, L172, L184–198, L248–249 restrict D2.1 to signed-leftmost and distinct-shift (multilinear) autocorrelations in reduced form, identify the 2-point Gram/Hankel/Toeplitz diagonal as $C(\varnothing, \{i\})$, and add an explicit subsection showing that repeated-shift moments fail at order 3 via $\mathbb{E}[a(m)^2 a(m+1)] = C(\{1\},\{0\}) = -1/4$ (Model A) vs. $0$ (Model B). Script L285–302, L313 verify these exact Palm values. |
| **m1** | **Resolved** | Script L234–235, L244–246 append `Hmax = 2016` and assert `grid[-2] == 2014 and grid[-1] == Hmax == 2016`; note L136, L426 match verbatim. |
| **m2** | **Resolved** | Note L57 explicitly includes $J_0 \to \infty$ and $\beta \uparrow 1/4$ (in $\xi = N^\beta$) alongside $\eta \to 0$ and $V, T \to \infty$. |
| **m3** | **Resolved** | Note L92, L101 require $s_0 \ge 1$ and choose $s = 1$ ($z = D \le X$), noting any $s \in [\theta, s_0]$ keeps $z = D^{1/s} \le X$. |
| **m4** | **Resolved** | Note L105, L117, L126–132 specify slowly varying $\rho(N)$ with $N\rho(N)^3 \to \infty$, state a.s. existence of a deterministic realization $(U^*, s^*)$, restrict $1 + 2\lfloor H/L\rfloor$ to $H \ge L$, add the $H \ge L$ check for $-$ endpoints, justify the global bound via $O(H^3) = o(N)$ and Karamata's theorem, note the pointwise spike at $h = L$, and prove (b) via conditional mixing $1/q + O(1/H_*)$ and the martingale strong law. |
| **m5** | **Resolved** | Script L340–406 upgrades `beta_sieve_exploration()` to a delay-aligned trapezoid + bisection + Richardson solver ($\beta_{3/4} \approx 1.3981$, $A_{3/4} \approx 2.2020$, ratio $\approx 0.9240$, implied bound $\approx 0.1148$, combined with $\theta = 1$: $\approx 0.1931$; reproduces $\beta_1 = 2$ and $A_1 = 2e^{\gamma_E}$ within $10^{-11}$). Note L3, L17, L144–145, L452 match and retain `[Exploration, floats, not a certificate.]`. |
| **m6** | **Resolved** | Note L21, L234–242 add the arbitrary-horizon formula $\sum_{v=0}^{H-1}(1 - \sum_{h\le v} u_h)_+$ and the greedy singleton law (still giving $1/(4K)$ for $u_h = K\rho$); script L494–512 verifies two $\sum u_h > 1$ test vectors (including fractional residual mass) and PSD moment matrices. |
| **m7** | **Resolved** | Note L279, L284, L437 remove the $n > 3$ restriction for Hurwitz $H$, note $r_3(3) = 8 = 24H(3)$, and explain $n > 3$ applies only to unweighted $h(-n)$; script L578–587 checks all three special cases and asserts `cube[3] == 8 == 24 * hurwitz(3)`. |
| **m8** | **Resolved** | Note L288, L293, L295, L301 explicitly set $a_0 = r_j(0) = 1$, clarify "$a_n/r_3(n) \to 1$ in density on the support of $r_3$ (density $5/6$)", and state $w_m = \sum_{\mathrm{rep}(n)=m} 2^{-kn}$ explicitly for $r_4$ ($2^{-km}$ for odd $m$, $\sum_{i\ge 0} 2^{-k2^im}$ for $m \equiv 2 \pmod 4$). |
| **m9** | **Resolved** | Note L363–369 clarify the Euler-index scaling via $k \mapsto k/c$ and display $\tau_{w,k/c}$; L376–380 break down the $-2$ in $w(A) - 2$ (right window edge and $\varepsilon$); L384 notes $y \ne 0$ for prime $p = x^2 + y^2$ in the $\zeta = \pm i$ case; L398, L407 and script L884 distinguish mean NAF weight per index $1 \le j \le M$ ($\asymp \sqrt{\log M}$) from mean per supported composite index ($\asymp \log M$). |

### 3. Regression Check (Mathematics, Evidence Labels, Benchmarks)

- **No new mathematical errors found.** Every newly added derivation and finite check was audited: the exact discrepancy calculation over half-open intervals in `d4_quantitative_k2()`, the boundary behavior of $\eta \le 1/4$ in Lemma D4.0, the quadratic identity proving $\tau_{w,k} \le c'_w/1024 < 1/2$, the Palm formula for `rep_A[h]`, the Cauchy–Schwarz proof for vector $2\times 2$ Gram matrices, the greedy singleton optimum for $\sum u_h > 1$, and the $O(H^3) = o(N)$ / Karamata / martingale strong-law steps in D1.4 are all mathematically sound.
- **No evidence-label or benchmark regressions.** The summary table (L11–29) and §5 (L411–461) cleanly separate `Paper proof`, `Conditional`, `External input`, `Finite certificate`, `Open`, `[finite]`, and `[exploration]`, leave all benchmark statuses (`BC-29`, theta powers, higher Euler powers) untouched, and explicitly state that cross-model review is not independent human peer review (L9, L461).

All 4 Major (`M1`–`M4`) and 9 Minor (`m1`–`m9`, plus the D4.3 denominator clarification) findings are completely resolved. **Track D is ACCEPTED.**
