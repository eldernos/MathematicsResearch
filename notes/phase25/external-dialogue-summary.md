# Technical Summary: Digit-Mass Transfer and Nonnormality of Generalized Erdős–Borwein Constants $E(2^k)$ and $E_+(2^k)$

> **Disclaimer and Provenance Notice.** This summary was prepared solely for owner-initiated mathematical examination (for example, by Mira Cult or David Bailey). **No external submission, outreach, collaboration, endorsement, or independent human peer review has occurred.** The underlying research and Lean 4 formalization were produced in an AI-assisted project (`https://github.com/eldernos/MathematicsResearch`, commit `04969b91f0c897ce55d21cb62c6b2c5aa3affe97`); cross-model audits are not independent human peer review. Every result below is tagged with its exact evidence scope (`Kernel-verified`, `Paper proof + Finite certificate`, `Paper proof + External input`, or `Open`).

---

## 1. The Complete Kernel-Verified Lean 4 Theorem

For an integer $q \ge 2$, let
$$E(q) = \sum_{m=1}^{\infty} \frac{1}{q^m - 1} = \sum_{n=1}^{\infty} \frac{\tau(n)}{q^n}, \qquad E_+(q) = \sum_{m=1}^{\infty} \frac{1}{q^m + 1} = \sum_{n=1}^{\infty} \frac{a_+(n)}{q^n},$$
where $\tau(n)$ is the divisor-counting function and $a_+(n) = \sum_{d \mid n} (-1)^{d-1} = (1 - v_2(n))\,\tau_{\mathrm{odd}}(n)$. While Erdős (1948) and P. Borwein (1991, 1992) established irrationality (and non-Liouville behavior) for these series, and recent 2026 work by Campbell, Captain Sude, and Mira Cult established binary disjunctivity and positive lower word density for $E(2)$, the digit distribution of the generalized constants $E(2^k)$ for $k \ge 3$ admits an elementary, completely unconditional nonnormality proof.

**Theorem 1 (Kernel-verified in Lean 4, zero external inputs).** *Let $f_1(N; x, 2) = N^{-1}\#\{1 \le j \le N : d_j(x; 2) = 1\}$ be the empirical $1$-bit frequency and $D_N(x; 2)$ the extreme interval discrepancy of the doubling orbit $\{2^n x\}_{0 \le n < N}$, with $D^-(x; 2) = \liminf_{N \to \infty} D_N(x; 2)$. For every integer $k \ge 1$,*
$$\limsup_{N \to \infty} f_1\!\bigl(N; E(2^k), 2\bigr) \le \frac{29}{20k}.$$
*Consequently, for every integer $k \ge 3$:*
1. $\limsup_{N \to \infty} f_1(N; E(2^k), 2) \le \dfrac{29}{20k} \le \dfrac{29}{60} < \dfrac{1}{2}$;
2. $D^-(E(2^k); 2) \ge \dfrac{1}{2} - \dfrac{29}{20k} \ge \dfrac{1}{120} > 0$ *(specifically, for every $\varepsilon > 0$, $D_N(E(2^k); 2) \ge \frac{1}{2} - \frac{29}{20k} - \varepsilon$ for all sufficiently large $N$, and $D_N(E(2^k); 2) \ge \frac{1}{120}$ eventually)*;
3. *$E(2^k)$ is **not simply normal in base $2$**, and is **not simply normal in any base $2^j$ ($j \ge 1$)**—in particular, it is not simply normal in its own construction radix $2^k$ (for instance, $E(8)$ in base $8$, and $E(16)$ in base $4$).*

**Formal verification record.** All parts of Theorem 1 are kernel-checked in `NormalityChecker/DigitMassTransfer.lean` at commit `04969b91f0c897ce55d21cb62c6b2c5aa3affe97` (62 exported theorems, zero `sorry`, standard axioms `propext`, `Classical.choice`, `Quot.sound` only, zero Tauberian or analytic external inputs):
- `erdosBorweinPow_eq_divisor_series` (L1770),
- `erdosBorwein_two_pow_digitFreq_limsup_le` (L2143),
- `erdosBorwein_two_pow_radixDiscrepancy_eventually_ge` (L2161),
- `erdosBorwein_two_pow_lowerDiscrepancy_pos` (L2194),
- `erdosBorwein_two_pow_not_simplyNormal` (L2334),
- `erdosBorwein_two_pow_not_simplyNormal_pow` (L2277).

---

## 2. The Elementary 4-Step Proof Mechanism (`h = g * \mu`, Zero External Inputs)

Unlike sparsity arguments (such as Bailey–Borwein–Crandall–Pomerance's 2004 isolation proof for $\theta_3(1/2)^2$, or Captain Sude's Sept 2026 proof for nonlinear power-Lambert series $\sum (b^{m^r}-1)^{-1}$, $r \ge 2$), the series $E(2^k) = \sum_{n \ge 1} \tau(n) 2^{-kn}$ has **full coefficient density**: every coefficient $\tau(n) \ge 1$ is nonzero. Rather than isolating bits, the proof tracks binary digit mass monotonically through carries:

1. **Kummer carry dissipation and submultiplicativity.** For nonnegative integers $a, c$ and any radix $b \ge 2$, Kummer's column-carry identity $s_b(a + c) + (b - 1)\kappa_b(a, c) = s_b(a) + s_b(c)$ shows that carries can only *destroy* digit sum (`digitSum_add_add_carries`). Hence $s_2$ is subadditive, shift-invariant ($s_2(2^t a) = s_2(a)$), and submultiplicative ($s_2(ac) \le s_2(a) s_2(c)$).

2. **Exact prefix decomposition with logarithmic carry tail.** Setting $M = \lfloor N/k \rfloor$, write $2^N E(2^k) = A_N + \tau_N$ with $A_N = \sum_{n=1}^M \tau(n) 2^{N - kn} \in \mathbb{Z}$ and $\tau_N = \sum_{n > M} \tau(n) 2^{N - kn}$. Then $\lfloor 2^N E(2^k) \rfloor = A_N + \lfloor \tau_N \rfloor$ (`floor_pow_mul_eq_head_add_floor_tail`). Since $\tau(n) \le n$, one has $0 \le \tau_N \le M + 2 \le N + 2$, so $s_2(\lfloor \tau_N \rfloor) \le \lfloor \log_2(N+2) \rfloor + 1 = O(\log N)$. *(Note: the tail $\lfloor \tau_N \rfloor$ is not bounded by $1$; e.g., for $E(8)$ at $N = 35$, $\lfloor \tau_{35} \rfloor = 3$ and the prefix bit count exceeds the coefficient mass by $2$.)* By Step 1,
   $$N\, f_1\!\bigl(N; E(2^k), 2\bigr) \le s_2\!\bigl(\lfloor 2^N E(2^k) \rfloor\bigr) \le \sum_{n=1}^{\lfloor N/k \rfloor} s_2(\tau(n)) + \lfloor \log_2(N+2) \rfloor + 1.$$

3. **Squarefull Möbius-convolution mean value (`h = g * \mu`).** Since $\tau(n) = \prod_{p^e \parallel n} (e+1)$ and $s_2$ is submultiplicative, $s_2(\tau(n))$ is dominated pointwise by the multiplicative function
   $$g(n) = \prod_{p^e \parallel n} s_2(e + 1) \ge s_2(\tau(n)).$$
   Its Möbius convolution $h = g * \mu$ is multiplicative with prime-power values
   $$h(p^e) = s_2(e + 1) - s_2(e) = 1 - v_2(e + 1).$$
   In particular, $h(p) = 1 - v_2(2) = 0$ at every prime $p$, so $h$ is supported strictly on **squarefull** integers and satisfies $|h(p^e)| \le \log_2(e+1)$. Therefore $\sum_{n \ge 1} |h(n)|/n < \infty$ trivially (`summable_abs_tauDigitKernel_div`). Expanding $\sum_{n \le X} g(n) = \sum_{d \le X} h(d)\lfloor X/d \rfloor$ and applying dominated convergence (`tendsto_average_of_summable_conv_mobius`) yields, with **zero Tauberian input**,
   $$\lim_{X \to \infty} \frac{1}{X} \sum_{n=1}^{X} g(n) = \sum_{n=1}^{\infty} \frac{h(n)}{n} = \prod_p \Bigl(1 - \frac{1}{p}\Bigr) \sum_{e \ge 0} \frac{s_2(e+1)}{p^e} = \prod_p \sum_{j \ge 0} \frac{p}{p^{2^j} + 1} =: C.$$

4. **Elementary Euler-product bound and base-$2^j$ popcount descent.** Using $h(p^e) = 1$ for even $e$, $h(p^e) \le 0$ for odd $e$, $h(p^3) = -1$, and $h(p^7) = -2$, each local factor satisfies $0 \le L(p) \le (1 - p^{-2})^{-1} - p^{-3} - 2p^{-7} \le 1 + p^{-2}$. Exact rational multiplication for $p < 37$ ($\prod_{p < 37} B(p) \le 1.3958$) and the tail bound $\prod_{p \ge 37}(1 + p^{-2}) \le (1 - \sum_{n \ge 37} n^{-2})^{-1} \le 36/35$ give $C \le 29/20$ (`tsum_tauDigitKernel_div_le`). Hence $\limsup_N f_1 \le 29/(20k) < 1/2$ for $k \ge 3$, which yields $D_N \ge 1/2 - f_1(N)$ and excludes simple normality in every base $2^j$ via the exact block-popcount identity $\sum_{v < 2^j} s_2(v)\,\#\{n < M : d_{n+1}(x; 2^j) = v\} = j M f_1(j M; x, 2)$.

---

## 3. Paper-Only Extensions (Strictly Separated from the Lean Kernel)

The companion manuscript (`papers/14-dense-digit-mass-lambert/paper.tex`) and exact Python verifiers (`scripts/phase24_digit_mass.py`, `scripts/phase24_classical.py`, using integer/rational arithmetic and scale-$2^{-192}$ outward rounding) establish four extensions beyond the Lean kernel:

1. **Sharp exact mean $C_{\mathrm{true}}$ (`Paper proof + Finite certificate`).** Because $s_2(2^t m) = s_2(m)$, we have $s_2(\tau(n)) = s_2\bigl(\prod_p \mathrm{odd}(e_p(n)+1)\bigr)$. An elementary independent-exponent Kubilius model (proved directly from the squarefull convolution lemma without external inputs) shows that the true mean $C_{\mathrm{true}} = \lim_{X \to \infty} X^{-1}\sum_{n \le X} s_2(\tau(n))$ exists and equals $\mathbb{E}\, s_2\bigl(\prod_p \mathrm{odd}(\varepsilon_p + 1)\bigr)$ for independent $\varepsilon_p \sim \mathrm{Geom}(1 - 1/p)$. Outward-rounded dynamic programming over $p \le 20{,}000$ certifies
   $$1.339103 \le C_{\mathrm{true}} \le 1.339116 < 1.4035953 \le C \le 1.4035958 < \tfrac{29}{20}.$$
   This sharpens $\limsup f_1(E(8); 2) \le 0.44638$, yields $D^-(E(8); 2) \ge 0.05362$ and $D^-(E(8); 8) \ge 0.02298$, and via zero-run windows proves $1 - D^-(E(2^k); 2) \le (C_{\mathrm{true}}\lceil \log_2 k \rceil + 1)/k \to 0$. The same method classifies $E_{\mathrm{odd}}(2^k)$ ($k \ge 3$), $E^*(2^k) = \sum \mu^2(m)/(2^{km}-1)$ ($k \ge 3$, $\limsup f_1 \le 1/k$), higher-divisor series $\sum \tau_r(n) 2^{-kn}$ ($r = 4, 8$ for $k \ge 4$; $r = 16$ for $k \ge 5$), and base-$b$ $\tau_b$ families $\sum \tau_{b-1}(m)/(b^{km}-1)$ (e.g., $\sum \tau_9(m)/(10^m - 1)$ in base $10$ with $k_0 = 1$).

2. **Non-dyadic Senge–Straus barrier (`Paper proof + External input`).** The binary mechanism relies essentially on $s_2(\tau(p)) = s_2(2) = 1$. If a radix $b \ge 2$ is **not** a power of $2$, then $\log 2 / \log b \notin \mathbb{Q}$; by Senge–Straus (1973) (effective form: Stewart 1980), $s_b(2^r) \to \infty$ as $r \to \infty$, and hence on squarefree integers $\tau(n) = 2^{\omega(n)}$ forces $X^{-1}\sum_{n \le X} w_b(\tau(n)) \to \infty$ and $X^{-1}\sum_{n \le X} s_b(\tau(n)) \to \infty$. Thus digit-mass transfer is **provably vacuous** for $E(b^k)$ in base $b$ for every $k \ge 1$ (e.g., $E(9)$ in base $3$, $E(25)$ in base $5$, $E(100)$ in base $10$). More generally, $\limsup_X X^{-1}\sum_{n \le X} s_b(\tau_r(n)) < \infty$ if and only if $r$ and $b$ are multiplicatively dependent. *(As a warning against finite-prefix extrapolation: over the first $20{,}000$ decimal digits of $E(100)$, the digit average is $2.5589$ vs. $4.5$—a finite measurement only—yet the true mean digit mass of $\tau(n)$ in base $10$ is $+\infty$.)*

3. **Signed transfer and $E_+(2^k)$ for $k \ge 4$ (`Lean-supported paper proof + Finite certificate`).** Because $E_+(2^k)$ has signed coefficients $a_+(n)$, carries can both create and destroy $1$-bits. Replacing $s_2$ by the minimal signed-digit (Non-Adjacent Form) weight $w_\pm(c)$ and $f_1$ by the two's-complement bit-transition count $T(A)$ (where $|T(A \pm 2^m) - T(A)| \le 2$ is kernel-verified in Lean), we obtain $\limsup_N F_N([1/4, 3/4); E_+(2^k), 2) \le 2W_+/k$ with certified $W_+ = \lim X^{-1}\sum w_\pm(a_+(n)) \in [0.908174, 0.908184]$. For every $k \ge 4$, $2W_+/k < 1/2$, proving $E_+(2^k)$ is not $2$-normal in base $2$ and not normal in any base $2^j$ (e.g., $D^-(E_+(16); 2) \ge 0.0459$). Because $W_+ \ge 3/4$, transition counts cannot reach $k = 3$.

4. **The 4-state free-boundary transducer and $E_+(8)$ (`Paper proof + Finite certificate + External input` [Reitwiesner 1960]).** To break the $k = 3$ barrier for $E_+(8)$, we compare the minimal signed-digit support $\sigma_1(x; N)$ on positions $1, \dots, N$ against the free-boundary minimal signed-digit weight $\sigma_{\mathrm{free}}(u)$ of length-$L$ binary words $u$ (allowing arbitrary incoming/outgoing carries $\delta_0, \delta_L \in \{-1, 0, 1\}$). A closed finite min-plus dynamic program collapses to a **minimal 4-state deterministic transducer** with stationary law $(1/6, 1/3, 1/3, 1/6)$ and exact uniform mean per bit
   $$A_L = \frac{1}{3} - \frac{7 - (-1/2)^{L-1}}{18L} \qquad (L \ge 1).$$
   Every real $x$ satisfies $\limsup_N \sigma_1(x; N)/N \ge A_L(1 - 2^L D^-(x; 2))$, while NAF minimality gives $\limsup_N \sigma_1(E_+(2^k); N)/N \le W_+/k$. At $k = 3$ and $L = 16$, $W_+/3 \le 0.304282 < A_{16} = 324039/1048576 \approx 0.309028$, proving that **$E_+(8)$ is not normal in base $2$ or any base $2^j$**, with $D^-(E_+(8); 2) \ge 2.34 \times 10^{-7}$.

---

## 4. Exact Open Boundaries and the $E(4)$ Carry-Density Threshold

Everything above leaves the classical exponents $k = 1, 2$ and non-dyadic bases strictly **Open**:

1. **Classical constants ($k = 1, 2$).** Normality, simple normality, and exact digit frequencies remain open for **$E(2)$, $E(4)$, $E^*(4)$, $E_{\mathrm{odd}}(2)$, $E_{\mathrm{odd}}(4)$, $E_+(2)$, and $E_+(4)$** (and simple normality of $E_+(8)$ is also open). None of the 50 classical benchmark constants changes status.

2. **Exact carry-density threshold for $E(4)$ (and $E(2)$, $E^*(4)$).** Keeping the carry term $\kappa_k(N) \ge 0$ in Kummer's identity makes the transfer exact (`Theorem 9.1`, `Paper proof`):
   $$f_1\!\bigl(N; E(2^k), 2\bigr) = \frac{C_{\mathrm{true}}}{k} - \frac{\kappa_k(N)}{N} + o(1).$$
   Consequently:
   - **$E(4)$ is simply normal in base $2$ if and only if**
     $$\frac{\kappa_2(N)}{N} \longrightarrow \frac{C_{\mathrm{true}} - 1}{2} \in [0.169551,\, 0.169558],$$
     and $\limsup f_1(E(4); 2) < 1/2$ if and only if $\liminf \kappa_2(N)/N > (C_{\mathrm{true}} - 1)/2$. Because $C_{\mathrm{true}} > 1$, **no** coefficient-mass functional bounded below by $1$ on nonzero integers (and no zero-carry bound) can decide $E(4)$; direct base-$4$ transfer also fails ($\liminf X^{-1}\sum s_4(\tau(n)) > 1.59 > 3/2$, via Wirsing 1967). For $E(2)$, the analogous simple-normality threshold is $\kappa_1(N)/N \to C_{\mathrm{true}} - 1/2 \in [0.839103, 0.839116]$.
   - For the unitary series $E^*(4) = \sum_{n \ge 1} 2^{-(2n - \omega(n))}$, every term is a single bit, giving $f_1(N; E^*(4), 2) = 1/2 - \kappa^*(N)/N + O(\log N / N)$. Thus $\limsup f_1 \le 1/2$ unconditionally, and $E^*(4)$ is simply normal in base $2$ if and only if $\kappa^*(N) = o(N)$. Proving that the collision set $\mathcal{C} = \{n : \exists n' > n,\ \omega(n') - \omega(n) = 2(n' - n)\}$ has positive upper density would prove simple nonnormality of $E^*(4)$ (`Conditional`).

3. **Exact limiting statistics and $D^+ < 1$ for $k \ge 3$.** For fixed $k \ge 3$, exact limiting digit frequencies, exact extreme discrepancy $D_\infty(E(2^k); 2)$, binary disjunctivity, and whether $D^+(E(2^k); 2) < 1$ (equivalently, membership outside $K_2$ via positive lower transition density) remain open: digit mass bounds $D^-$ from below, but gives no lower bound on surviving $1$-bits or transitions.

4. **Non-power-of-2 bases.** Whether $E(9)$ is simply normal in base $3$, $E(25)$ in base $5$, or $E(100)$ in base $10$—and whether $E(2^k)$ ($k \ge 3$) is normal in any base $b$ multiplicatively independent of $2$—remains completely open.

---

## 5. Specific Points of Contact for Dialogue

- **For Mira Cult:** Our $E(2^k)$ ($k \ge 3$) theorem is complementary to your November 2026 short-window positive-word-density theorem for $E(2)$ (audited in `notes/phase13/erdos-borwein.md` and `CC-21`): yours gives a lower bound on word frequencies (hence $D^+(E(2); 2) < 1$) at $k = 1$, whereas ours gives an upper bound on $f_1$ (hence $D^-(E(2^k); 2) > 0$) at $k \ge 3$. Two natural shared questions arise: (i) does a short-window planting argument extend to $E(2^k)$ ($k \ge 3$) to prove $D^+(E(2^k); 2) < 1$ and disjunctivity alongside our $D^- > 0$, giving $0 < D^- \le D^+ < 1$? (ii) At the $k = 2$ boundary, can local arrival correlations establish $\liminf \kappa_2(N)/N > 0.169558$ for $E(4)$, or positive upper density of $\mathcal{C}$ for $E^*(4)$?
- **For David Bailey:** In connection with Bailey–Crandall (2002) on $E(2)$ and Bailey–Borwein–Crandall–Pomerance (2004, §9) on $\theta_3(1/2)^2$ vs. $\theta_3(1/2)^3, \theta_3(1/2)^4$: the generalized Erdős–Borwein family $E(2^k)$ ($k \ge 3$) provides an explicit, kernel-verified family of dense, transcendental-candidate Lambert constants whose binary nonnormality is proved without bit isolation; conversely, our Senge–Straus barrier explains why $E(100)$ in base $10$ exhibits dramatic finite-prefix bias (digit average $2.5589$ over $20{,}000$ digits) despite infinite asymptotic coefficient digit mass, underscoring the caution against extrapolating from finite prefixes in experimental normality studies.
