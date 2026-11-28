# Generalized Erdős–Borwein and Signed Lambert Classification

Phase 25, Track B. Companion verification and certificate script: [`scripts/phase25_lambert_eplus.py`](../../scripts/phase25_lambert_eplus.py) (standard library only; `python -B scripts/phase25_lambert_eplus.py` exits with code `0` in ~3.5–6 s, passing **188,766 assertions**: **186,311 `[exact]`**, **2,428 `[encl]`**, and **27 `[finite]`**).

**Scope, evidence, and benchmark disclaimer.**
- Every numerical bound used inside a theorem is a **Finite certificate** computed exclusively with exact integers, `fractions.Fraction`, integer `isqrt` brackets, or scale-$2^{-96}$ integer intervals with directed outward rounding; zero floating-point checks appear inside any certificate.
- Every prefix statistic in §4.3 and the finite-block table in §4.2 is a **Finite measurement** only. Finite measurements never establish or support asymptotic statements and are never used inside any proof.
- The Lean 4 declarations in §3.5 are an uncompiled formalization blueprint for Stage 3, not kernel-verified code.
- Any subsequent cross-model review of this note is **not** independent human peer review (`AGENTS.md`, `docs/research-objectives.md`).
- **Benchmark stability:** Nothing in this note changes the status of any constant in the permanent 50-constant roster `BC-01`…`BC-50` (`docs/benchmarks/classical-constants.toml`). In particular, full normality and simple normality of $E(2)$ (`BC-37`), $E_+(2)$ (`BC-39`), $E(4)$, $E^*(4)$, $E_{\rm odd}(4)$, and $E_+(4)$, as well as base-2 simple normality of $E_+(8)$, remain **Open**.

---

## Results at a glance

| ID | Main Result | Evidence Label | External Inputs | Standing Objectives (`docs/research-objectives.md`) |
| --- | --- | --- | --- | --- |
| **B1.1–B1.2** | Exact displaced carry-conservation $C_k(n) + q_n = d_n + b q_{n-1}$, dead-block transition inequality, and two-point exit discrepancy bound $1 - D_N(x; b) \ge \min(\frac{b-1}{b^2}, \frac{\#\{d_n=0, d_{n+1}\ne 0\}}{N})$; zero-external-input bound $1 - D_N \gg_k (\log\log N)^{-1/2}$ whenever $k > C_U$ (§1.1–1.2) | Paper proof; Finite certificate | None | Obj. 3 ($D_N$ gap) |
| **B1.3** | Unconditional positive lower transition density, **$D^+(F; b) < 1$**, and **$F \notin K_b$** whenever $k > C_U$ — giving full double-sided **$0 < D^- \le D^+ < 1$** for $E(2^k)$ ($k \ge 3$), $E_{\rm odd}(2^k)$ ($k \ge 3$), $E^*(2^k)$ ($k \ge 3$), $E_b^*(b^k)$ ($b \ge 3, k \ge 2$), **and $D^+ < 1, \notin K_b$ already at the $k = 2$ boundary** for $E_{\rm odd}(4)$, $E^*(4)$, and $E_b^*(b^2)$ ($\forall b \ge 2$) (§1.3) | Paper proof; Finite certificate | 2-D Fundamental Lemma of the Combinatorial Sieve | Obj. 2 (non-membership in $K_b$), Obj. 3 ($0 < D^- \le D^+ < 1$) |
| **B1.4** | Signed Isolated-Odd-Arrival Theorem: for all sufficiently large $k \ge k_0$, **$0 < D^-(E_+(2^k); 2) \le D^+(E_+(2^k); 2) < 1$** and **$E_+(2^k) \notin K_2$** (with $\liminf \mathrm{tr}_N/N \ge 1/(2k)$), and identically for cubic-character Lambert series $L_\pm(2^k)$ ($k \ge k_0(\chi)$, with $D^- > 0$ from `GF-36` for $k > 4 W_\chi$, including $k \ge 4$ on moduli $7, 9, 13$), resolving the open $D^+ < 1$ questions for $E_+(2^k)$ (`GF-36`, `GF-40`) and cubic $L_\pm(2^k)$ (`GF-31`) for large $k$ (§1.4) | Paper proof; Finite certificate | 2-D / $\kappa = \frac{2}{3}$ Fundamental Lemma; Dirichlet's theorem / Halász (for $L_-$) | Obj. 2 ($\notin K_2$), Obj. 3 ($0 < D^- \le D^+ < 1$) |
| **B1.5** | Higher-kernel exclusion $x \notin K_{2^j}$: **$E(2^k) \notin K_{2^j}$ ($\forall k \ge 5, j \ge 1$)**, $E(16) \notin K_2, K_4, K_8, K_{16}$, $E(8) \notin K_2, K_4$, **$E_{\rm odd}(2^k) \notin K_{2^j}$ ($\forall k \ge 3, j \ge 1$)**, and **$E^*(2^k) \notin K_{2^j}$ ($\forall k \ge 2, j \ge 1$, including $E^*(4)$!)** (§1.5) | Paper proof; Finite certificate | Halász (1968); 2-D Fundamental Lemma (for $K_2$ base) | Obj. 2 (kernel tower exclusions) |
| **B2.1–B2.2** | Weighted residue law + exact $s$-moment integral inequality proving **$1 - D^-(F_{2^k}(a); 2^k) \ll \frac{\log k}{k} \to 0$** (hence **$D^-(\cdot; 2^k) \to 1$**) for $E(2^k), E_{\rm odd}(2^k), E^*(2^k), E_+(2^k)$ and $E_b^*(b^k)$ ($148\times$ sharper at $k=64$ than Phase 24), plus direct $s = 1/2$ base-$32$ simple nonnormality of $E_+(32)$ (§2) | Paper proof; Finite certificate | Halász (1968) | Obj. 2 (simple nonnormality), Obj. 3 (sharp $D^- \to 1$) |
| **B3.1** | **Universal Transducer Obstruction:** for every cost pair $(c_+, c_-) \in \mathbb{R}_{\ge 0}^2$, no upper bound on $\sigma_{c_+, c_-}(x; N)/N$ (not even $O(\sqrt{N}) = o(N)$) can exclude base-2 simple normality (witness: $E_2 \in K_2$, `GF-03`). Base-2 simple normality of $E_+(8)$ remains **Open** (§3.1) | Paper proof; Finite certificate | None | Obj. 4 (limitation theorem) |
| **B3.2** | Disjoint-block simple nonnormality of $E_+(2^k)$ with zero external inputs: simply nonnormal in **base $2^k$ ($\forall k \ge 4$, incl. $E_+(16)_{16}$)**, **base $8$ ($\forall k \ge 5$)**, **base $4$ ($\forall k \ge 8$)**, and **$E_+(8)$ in base $2^L$ ($\forall L \ge 13$)** (§3.2) | Paper proof; Finite certificate | None | Obj. 2 (simple nonnormality) |
| **B3.3–B3.4** | Exact circular total variation $V_{\rm circ}(\sigma_{\rm free}; L) = \frac{2^L + 2(-1)^L}{3}$ + discrete circular Koksma boosts $D^-(E_+(8); 2)$ by $> 61\times$ to **$\ge 1.4362 \times 10^{-5}$**; minimal **7-state asymmetric $(1, 3/2)$ automaton** ($A_\infty = 12/31$) boosts it by $> 101\times$ to **$\ge 2.3642 \times 10^{-5}$** (§3.3–3.4) | Paper proof; Finite certificate | None | Obj. 3 (explicit $D^-$) |
| **B3.5** | Clean DP-free **Lean 4 formalization blueprint** for $E_+(2^k)$ ($k \ge 3$): exact prefix-boundary theorem $H_N - X_N \in \{0, 1\} \implies w_\pm(X_N) \le w_\pm(S_M^+) + 1$, three certified DP-free majorants ($p \le 31, 150, 400$ reusing `DigitMassTransfer.lean`, with Tier-1 $< 23671/25000$ giving $\ge 13/10^9$ at $L = 23$), and 4-state transducer invariants (§3.5) | Paper proof + Finite certificate *(Lean blueprint uncompiled)* | None | Obj. 2, Obj. 3 (formalization readiness) |
| **B4.1–B4.2** | Sharpened $E_+(4)$ sufficient NAF deficit $\in [0.120705, 0.120797]$; **Fixed-Window Cancellation Barrier:** for every fixed block width $B \ge 1$ and every $k \ge 1$, $\bar{c}_{k, B}^{\rm block}(M) = O_{k,B}((\log\log\log\log M)^{1/2}/(\log\log M)^{1/8}) \to 0$, exposing a stark finite-scale illusion at $B = 8, 16$ through $M = 2^{16}$ (§4) | Paper proof; Finite certificate; Finite measurement (clearly separated) | 2-D Fundamental Lemma | Obj. 4 (carry-window limitation theorem) |
| **B5.1–B5.4** | Broader Lambert classifications: $\tau_{2^m}$ (base 2, coset law), prime-base $\tau_p$ ($p = 3, 5, 7$), $E_b^*(b^k)$, **Fermat-product moduli $\varphi(M) = 2^t$** extending `GF-07` beyond $M \mid 24$, general periodic integer weights with $\operatorname{odd}(\lambda(M)) \mid 3$, compatible $\mathbb{Z}$-linear combinations, and Senge–Straus synthesis (§5) | Paper proof; Finite certificate | 2-D Fundamental Lemma; Halász; `GF-13` (Wirsing/Selberg–Delange); Senge–Straus (barrier only) | Obj. 2, Obj. 3, Obj. 4 |

---

## 0. Exact Definitions and Conventions

Fix an integer radix $b \ge 2$. Every real $x \in \mathbb{R}$ has a unique canonical base-$b$ expansion not ending in $(b-1)^\infty$:

```math
x = \lfloor x \rfloor + \sum_{n \ge 1} d_n(x; b)\, b^{-n}, \qquad d_n(x; b) \in \{0, 1, \ldots, b - 1\}.
```

Write $\{t\} = t - \lfloor t \rfloor \in [0, 1)$ for the fractional part and $\|t\| = \min(\{t\}, 1 - \{t\}) \in [0, \frac{1}{2}]$ for the distance to $\mathbb{Z}$. For $N \ge 1$, the **extreme interval discrepancy** of the orbit $(\{b^n x\})_{0 \le n < N}$ is

```math
D_N(x; b) = \sup_{0 \le u < v \le 1} \left| \frac{\#\{0 \le n < N : \{b^n x\} \in [u, v)\}}{N} - (v - u) \right|,
```

with $D^-(x; b) = \liminf_{N \to \infty} D_N(x; b)$ and $D^+(x; b) = \limsup_{N \to \infty} D_N(x; b)$. The **numerical translation kernel** is $K_b = \{x \in \mathbb{R} : D_N(x; b) \to 1\}$ (`GF-05`), which decomposes via `GF-29` (`NormalityChecker.HigherOrderTower.kernel_eq_fixedPoint_add_zeroOrbit`) as $K_b = \mathrm{Fix}_b + M_b$ where $\mathrm{Fix}_b = \{R/(b-1) : 0 \le R < b - 1\}$ and $M_b = \{w \in \mathbb{R} : \frac{1}{N} \sum_{n < N} \|b^n w\| \to 0\}$. For base $2$, write $f_{1, N}(x; 2) = \frac{1}{N} \#\{1 \le n \le N : d_n = 1\}$ and $\mathrm{tr}_N(x) = \#\{1 \le n < N : d_n(x; 2) \ne d_{n+1}(x; 2)\}$.

For $a : \mathbb{N} \to \mathbb{Z}$ with $\sum_{n \ge 1} |a(n)| b^{-kn} < \infty$, write

```math
F_{b^k}(a) = \sum_{n \ge 1} a(n)\, b^{-kn}.
```

Our principal arithmetic Lambert series are

```math
E(q) = \sum_{m \ge 1} \frac{1}{q^m - 1} = \sum_{n \ge 1} \tau(n)\, q^{-n}, \qquad
E_{\rm odd}(q) = \sum_{m\text{ odd}} \frac{1}{q^m - 1} = \sum_{n \ge 1} \tau_{\rm odd}(n)\, q^{-n},
```

```math
E^*(q) = \sum_{m \ge 1} \frac{\mu^2(m)}{q^m - 1} = \sum_{n \ge 1} 2^{\omega(n)}\, q^{-n}, \qquad
E_b^*(q) = \sum_{m \ge 1} \frac{\mu^2(m)(b-1)^{\omega(m)}}{q^m - 1} = \sum_{n \ge 1} b^{\omega(n)}\, q^{-n},
```

```math
E_+(q) = \sum_{m \ge 1} \frac{1}{q^m + 1} = \sum_{n \ge 1} a_+(n)\, q^{-n}, \qquad a_+(n) = \sum_{d \mid n} (-1)^{d-1} = (1 - v_2(n))\, \tau_{\rm odd}(n),
```

and for $r \ge 2$, $F_{b^k}(\tau_r) = \sum_{n \ge 1} \tau_r(n)\, b^{-kn} = \sum_{m \ge 1} \tau_{r-1}(m)/(b^{km} - 1)$, where $\tau_r(p^e) = \binom{e+r-1}{r-1}$. For a modulus $M \ge 1$ and $\gcd(r, M) = 1$, set $A_{r, M}(q) = \sum_{m \equiv r \pmod M} (q^m - 1)^{-1}$ and $E^{(M)}(q) = \sum_{\gcd(m, M) = 1} (q^m - 1)^{-1} = \sum_{n \ge 1} \tau^{(M)}(n) q^{-n}$, where $\tau^{(M)}(n) = \#\{d \mid n : \gcd(d, M) = 1\}$.

For a nonzero integer $c$ and radix $b \ge 2$, write $v_b(c) = \max\{j \ge 0 : b^j \mid c\}$ and $u_b(c) = c / b^{v_b(c)}$ (with $v_b(0) = u_b(0) = 0$); when $b = 2$, $u_2(c) = \operatorname{sign}(c)\operatorname{odd}(|c|)$. For an arithmetic sequence $a(m) = b^{V(m)} U(m)$ ($V(m) = v_b(a(m))$, $U(m) = u_b(a(m))$), we write

```math
C_U(s) := \lim_{X \to \infty} \frac{1}{X} \sum_{m \le X} |U(m)|^s \quad (0 < s \le 1), \qquad C_U := C_U(1),
```

and define the **displaced arrival sum** at base-$b$ column $n \ge 1$ by

```math
C_k(n) := \sum_{\substack{m \ge 1 \\ km - V(m) = n}} U(m) \qquad (n \ge 1).
```

For $c \in \mathbb{Z}$ and $\lambda \ge 1$, define the **$(1, \lambda)$-weighted signed binary cost**

```math
w_{1, \lambda}(c) = \min \left\{ \sum_{i} \bigl(\mathbf{1}_{\varepsilon_i = +1} + \lambda \mathbf{1}_{\varepsilon_i = -1}\bigr) : c = \sum_{i} \varepsilon_i 2^{m_i},\ \varepsilon_i \in \{-1, 1\},\ m_i \in \mathbb{Z}_{\ge 0} \right\},
```

so $w_\pm := w_{1, 1}$ is the classical NAF (non-adjacent form) weight, and for $x \in \mathbb{R}$, $\sigma_{1, \lambda}(x; N)$ is the infimum of $\sum_{j=1}^N (\mathbf{1}_{a'_j = +1} + \lambda \mathbf{1}_{a'_j = -1})$ over all signed binary expansions $a' \sim d(x)$ ($a'_j \in \{-1, 0, 1\}$, $\sum_{j \ge 1} a'_j 2^{-j} = \{x\} + m$ for some $m \in \mathbb{Z}$); $\sigma_1 := \sigma_{1, 1}$ matches `GF-32` / `GF-40`.

---

## 1. Track B1: Unconditional $D^+ < 1$, Non-Membership in $K_b$ and $K_{2^j}$, and Two-Sided Classification $0 < D^- \le D^+ < 1$

In `GF-36` (`notes/phase24/dense-digit-mass-and-lambert.md`), dense digit-mass transfer proved $D^-(E(2^k); 2) > 0$ for $k \ge 3$ and $D^-(E_{\rm odd}(2^k); 2), D^-(E^*(2^k); 2) > 0$ for $k \ge 3$, while leaving $D^+ < 1$ and $K_2$-membership open for fixed $k$ (`GF-36` scope). For $E(2)$, Mira Cult's short-window word-density theorem (`CC-21`) gives $D^+(E(2); 2) < 1$ via Perelli–Pintz–Salerno's short-interval Bombieri–Vinogradov theorem. Here we give a different, independent route for the stretched regime $k > C_U$ (which says nothing about $E(2)$, where $C_U > 1 = k$, but applies across $k \ge 3$ for $E(2^k)$ and already at $k = 2$ for $E_{\rm odd}(4)$, $E^*(4)$, and $E_b^*(b^2)$): **exact displaced carry conservation** reduces $D^+ < 1$ to a pure dead-block run-length bound, which yields a zero-external-input $N/\sqrt{\log\log N}$ transition lower bound and—combined solely with the upper bound of the 2-D Fundamental Lemma of the Combinatorial Sieve—proves $D^+ < 1$ and $\notin K_b$ across every nonnegative family with $k > C_U$, as well as signed $E_+(2^k)$ and cubic $L_\pm(2^k)$ for large $k$.

### 1.1 Certified odd-part means $C_U$ and exact displaced carry conservation

**Proposition B1.1 (Exact odd-part means; Paper proof + Finite certificate).**
Let $U_{\rm odd}(n) = \prod_{p > 2} \operatorname{odd}(v_p(n) + 1)$, $U(n) = \operatorname{odd}(\tau(n)) = \operatorname{odd}(v_2(n) + 1) U_{\rm odd}(n)$, and $U_+(n) = u_2(a_+(n))$ (so $|U_+(n)| = \mathbf{1}_{v_2(n) \ne 1} \operatorname{odd}(|1 - v_2(n)|) U_{\rm odd}(n)$). For every $s \in (0, 1]$, the limiting moments $C_U(s), C_{U, \rm odd}(s), C_{U, +}(s)$ exist unconditionally (via Wintner's squarefull convolution lemma, `GF-36` Lemma 3.1, since $U_{\rm odd}(p) = 1$ for all odd primes $p$ and $U_{\rm odd}(p^e) \le e + 1$), with exact Euler products

```math
C_{U, \rm odd}(s) = \prod_{p > 2} L_p^{\rm odd}(s), \qquad
L_p^{\rm odd}(s) = \left(1 - \frac{1}{p}\right) \sum_{e \ge 0} \frac{\operatorname{odd}(e + 1)^s}{p^e},
```

```math
C_U(s) = L_2^{\rm odd}(s)\, C_{U, \rm odd}(s), \qquad
C_{U, +}(s) = L_2^+(s)\, C_{U, \rm odd}(s), \qquad
L_2^+(s) = \frac{1}{2} + \frac{1}{4} L_2^{\rm odd}(s).
```

At $s = 1$, $L_p^{\rm odd} := L_p^{\rm odd}(1)$ admits the closed-form dyadic expansion

```math
L_p^{\rm odd} = (p - 1) \sum_{j \ge 0} \frac{p^{2^j} (p^{2^{j+1}} + 1)}{(p^{2^{j+1}} - 1)^2} \qquad (\forall p \ge 2),
```

and satisfies $L_p^{\rm odd} < 1 + \frac{2}{p^2}$ for every odd prime $p \ge 3$. For $M \in \{3, 5, 6\}$, $C_U^{(M)} = \lim \frac{1}{X} \sum_{n \le X} \operatorname{odd}(\tau^{(M)}(n))$ equals $C_U / L_3^{\rm odd}$, $C_U / L_5^{\rm odd}$, and $C_{U, \rm odd} / L_3^{\rm odd}$ respectively (with $C_U^{(6)} = C_U^{(12)} = C_U^{(24)}$). Outward-rounded scale-$2^{-96}$ integer arithmetic over primes $p \le 20{,}000$ ($s = 1$) and $p \le 6{,}000$ ($s = 1/2$) in [`scripts/phase25_lambert_eplus.py`](../../scripts/phase25_lambert_eplus.py) certifies:

| Constant | Certified outward-rounded enclosure (`[encl]`) | Key threshold certified |
| --- | --- | --- |
| $L_2^{\rm odd}$ | $[1.480492,\, 1.480493]$ | — |
| $L_2^+$ | $[0.870123,\, 0.870124]$ | — |
| $C_{U, \rm odd}$ | $[1.402443,\, 1.402514]$ | $< 2$ ($E_{\rm odd}(4)$); $C_{U,\rm odd}/3 < 1/2$ |
| $C_U$ | $[2.076306,\, 2.076411]$ | $< 3$ ($E(8)$); $C_U/4 < 8/15$; $C_U/5 < 1/2$ |
| $C_{U, +}$ | $[1.220298,\, 1.220360]$ | $C_{U,+}/6 < 1/4 - 1/128$ |
| $C_U^{(3)}$ | $[1.740214,\, 1.740302]$ | $< 2$ ($A_{r, 3}(4)$) |
| $C_U^{(5)}$ | $[1.940549,\, 1.940647]$ | $< 2$ ($A_{r, 5}(4)$) |
| $C_U^{(6)}$ | $[1.175429,\, 1.175489]$ | $< 3/2$ |
| $C_U(1/2)$ | $[1.316604,\, 1.316742]$ | Used in B2 ($D^-(E(2^k); 2^k)$) |
| $C_{U, \rm odd}(1/2)$ | $[1.133634,\, 1.133754]$ | Used in B2 |
| $C_{U, +}(1/2)$ | $[0.895968,\, 0.896062]$ | $E_+(32)$ base-32 simple nonnormality |

*Proof.* Every positive integer $m$ has a unique dyadic representation $m = 2^j (2r + 1)$ ($j, r \ge 0$), so $\sum_{m \ge 1} \operatorname{odd}(m) x^m = \sum_{j \ge 0} \sum_{r \ge 0} (2r + 1) x^{2^j(2r+1)} = \sum_{j \ge 0} \frac{x^{2^j}(1 + x^{2^{j+1}})}{(1 - x^{2^{j+1}})^2}$ (verified identically through $x^{255}$). Multiplying by $\frac{1 - x}{x}$ and substituting $x = 1/p$ yields $L_p^{\rm odd} = (p - 1) \sum_{j \ge 0} \frac{p^{2^j}(p^{2^{j+1}} + 1)}{(p^{2^{j+1}} - 1)^2}$ (checked directly at $p = 2$ in the script). For the upper bound $L_p^{\rm odd} < 1 + 2/p^2$ ($p \ge 3$), note that $\operatorname{odd}(e + 1) - 1$ vanishes at $e = 0, 1, 3$, equals $2$ at $e = 2$, and is at most $e$ for $e \ge 4$; hence

```math
L_p^{\rm odd} - 1 \le \left(1 - \frac{1}{p}\right)\left(\frac{2}{p^2} + \sum_{e \ge 4} \frac{e}{p^e}\right)
= \frac{2(p-1)}{p^3} + \frac{4p - 3}{p^4(p - 1)}
= \frac{2}{p^2} - \frac{2p^2 - 6p + 3}{p^4(p - 1)} < \frac{2}{p^2},
```

since $2p^2 - 6p + 3 > 0$ for every $p \ge 3$ (verified in the script). For $L_2^+(s)$, $\Pr(B_2 = 0) = 1/2$ contributes $1$, $\Pr(B_2 = 1) = 1/4$ contributes $0$, and $\Pr(B_2 = e) = 2^{-(e+1)}$ ($e \ge 2$) contributes $\operatorname{odd}(e - 1)^s$, which after shifting $e' = e - 2 \ge 0$ equals $\frac{1}{4} \cdot \frac{1}{2} \sum_{e' \ge 0} \operatorname{odd}(e' + 1)^s 2^{-e'} = \frac{1}{4} L_2^{\rm odd}(s)$. For $s = 1/2$, $\sqrt{e + 1} - 1 \le e/2$ at $e \ge 2$ gives $L_p^{\rm odd}(1/2) - 1 \le \frac{1}{2}(1 - \frac{1}{p})\sum_{e \ge 2} e p^{-e} = \frac{2p - 1}{2 p^2(p - 1)} \le \frac{5}{4 p^2}$ for $p \ge 3$ (strictly $< \frac{5}{4 p^2}$ for all $p \ge 5$, and applied only for $p > 6{,}000$). Multiplying the finite prime products by the elementary tail bound $\sum_{p > P} p^{-2} < \frac{1}{2(P - 1)}$ (even $P \ge 6$) and $e^t \le (1 - t)^{-1}$ ($0 \le t < 1$) gives every certified interval in the table. $\square$

**Lemma B1.2 (Exact Displaced Carry Conservation, Dead-Block Reduction, and Universal Exit Discrepancy Bound; Paper proof, zero external inputs).**
Let $b \ge 2$, $k \ge 1$, and let $a : \mathbb{N} \to \mathbb{Z}_{\ge 0}$ satisfy $a(m) = b^{V(m)} U(m)$ ($b \nmid U(m)$ whenever $a(m) > 0$), $a(m) \ll_\varepsilon m^\varepsilon$ (more generally $\sum_{m > M} a(m) b^{kM - km} = o(M)$), and $km - V(m) \ge 1$ for all large $m$. Put $F = F_{b^k}(a) = \sum_{m \ge 1} a(m) b^{-km}$, $d_n = d_n(F; b)$, $C_k(0) = \sum_{km - V(m) \le 0} U(m) b^{V(m) - km} \in \mathbb{Z}_{\ge 0}$, $C_k(n) = \sum_{km - V(m) = n} U(m)$ ($n \ge 1$), and $Y_n = \sum_{j \ge 1} C_k(n + j) b^{-j} \ge 0$, $q_n = \lfloor Y_n \rfloor \in \mathbb{Z}_{\ge 0}$ ($n \ge 0$, with $q_0 = \lfloor F \rfloor - C_k(0) \ge 0$). Then:

1. *(Exact column carry identity & mass conservation.)* For every $n \ge 1$ and every $N \ge 1$,

```math
C_k(n) + q_n = d_n + b\, q_{n-1}, \qquad
\sum_{n=1}^N \bigl(d_n + (b - 1)\, q_{n-1}\bigr) = \sum_{n=1}^N C_k(n) + q_N - q_0,
```

   with $0 \le q_N \le \sum_{m > \lfloor N/k \rfloor} a(m) b^{N - km} = o(N)$. In particular, if $C_U = \lim_{X \to \infty} \frac{1}{X} \sum_{m \le X} U(m) < \infty$, then $\lim_{N \to \infty} \frac{1}{N} \sum_{n=1}^N C_k(n) = C_U / k$.

2. *(Dead positions and guaranteed transitions.)* Define the **dead-position set** $\mathcal{D}_N := \{1 \le n \le N : d_n = 0 \text{ and } q_{n-1} = 0\}$. Then:
   - $|\mathcal{D}_N| \ge N - \sum_{n=1}^N C_k(n) - q_N + q_0 = \bigl(1 - \frac{C_U}{k} - o(1)\bigr) N$;
   - every $n \in \mathcal{D}_N$ forces $C_k(n) = 0$ and $q_n = 0$;
   - every exit $n \in \mathcal{D}_N$ ($n < N$) with $n + 1 \notin \mathcal{D}_N$ forces $d_n = 0$ and $d_{n+1} \ne 0$;
   - for every integer $G \ge 2$ and every $N \ge G$,

```math
(G - 1)\, \#\{1 \le n < N : d_n = 0,\, d_{n+1} \ne 0\}
  \ge |\mathcal{D}_N| - (G - 1) - \#\{1 \le a \le N - G + 1 : C_k(a) = \cdots = C_k(a + G - 1) = 0\}.
```

3. *(Universal base-$b$ exit-to-discrepancy inequality.)* For **every** real $x \in \mathbb{R}$, every radix $b \ge 2$, and every $N \ge 2$,

```math
1 - D_N(x; b) \ge \min\!\left(\frac{b - 1}{b^2},\; \frac{\#\{1 \le n < N : d_n(x; b) = 0,\, d_{n+1}(x; b) \ne 0\}}{N}\right).
```

*Proof.*
(1) Reindexing the nonnegative series $F = C_k(0) + \sum_{n \ge 1} C_k(n) b^{-n}$ gives $b^n F = A_n + Y_n$ with $A_n = C_k(0) b^n + \sum_{j=1}^n C_k(j) b^{n-j} \in \mathbb{Z}$, hence $\lfloor b^n F \rfloor = A_n + q_n$ for all $n \ge 0$. Since $d_n = \lfloor b^n F \rfloor - b \lfloor b^{n-1} F \rfloor$ and $A_n - b A_{n-1} = C_k(n)$, we obtain $C_k(n) + q_n = d_n + b q_{n-1}$ identically. Summing over $1 \le n \le N$ telescopes $\sum (q_n - q_{n-1}) = q_N - q_0$, giving the conservation identity. For every $m$ with $km - V(m) > N$ we have $km > N$ and $U(m) b^{N - (km - V(m))} = a(m) b^{N - km}$, so $0 \le q_N \le Y_N \le \sum_{m > \lfloor N/k \rfloor} a(m) b^{N - km} = o(N)$. Moreover, every $m \le N/k$ satisfies $km - V(m) \le N$, while every $m$ with $km - V(m) \le N$ satisfies $m \le (N + V(m))/k \le N/k + O(\log N)$, so $\frac{1}{N} \sum_{n=1}^N C_k(n) = \frac{1}{N} \sum_{m \le N/k} U(m) + o(1) \to C_U / k$.

(2) For every $n \in [1, N]$, $d_n + (b - 1) q_{n-1} \in \mathbb{Z}_{\ge 0}$ vanishes iff $n \in \mathcal{D}_N$, and is $\ge 1$ otherwise; thus $N - |\mathcal{D}_N| \le \sum_{n=1}^N (d_n + (b - 1) q_{n-1}) = \sum_{n=1}^N C_k(n) + q_N - q_0$. If $n \in \mathcal{D}_N$, then $C_k(n) + q_n = 0 + b \cdot 0 = 0$, forcing $C_k(n) = q_n = 0$ by nonnegativity. Hence if $n \in \mathcal{D}_N$ ($n < N$) and $n + 1 \notin \mathcal{D}_N$, $q_n = 0$ is already forced, so $n + 1 \notin \mathcal{D}_N$ implies $d_{n+1} \ne 0$. Partition $\mathcal{D}_N$ into maximal contiguous intervals $R = [u, v]$. Every $R$ with $|R| \ge G$ contributes $|R| - G + 1$ empty $G$-windows $[a, a + G - 1] \subseteq R \subseteq \mathcal{D}_N$ (on which $C_k \equiv 0$), leaving $G - 1$ elements; every $R$ with $|R| \le G - 1$ has at most $G - 1$ elements. Every $R$ with $v < N$ has an exit at $v$ with $(d_v, d_{v+1}) = (0, \text{nonzero})$, while at most one run ends at $v = N$ (accounting for at most $G - 1$ elements). Summing over all runs gives the stated inequality.

(3) Set $S = \{1 \le n < N : d_n = 0,\, d_{n+1} \ne 0\}$, $M = |S|$, and $\delta = \frac{b - 1}{b^2}$. The 2-element sets $\{n - 1, n\} \subseteq \{0, \ldots, N - 1\}$ ($n \in S$) are **pairwise disjoint**: if $n' = n + 1$ with $n, n' \in S$, then $d_{n+1} \ne 0$ (from $n \in S$) contradicts $d_{n+1} = 0$ (from $n' \in S$). For each $n \in S$, put $y_{n-1} = \{b^{n-1} x\}$ and $y_n = \{b^n x\}$. Since $d_n = 0$ and $d_{n+1} \ge 1$ (and the expansion does not end in $(b-1)^\infty$), we have $y_n = b y_{n-1}$ and $\frac{1}{b^2} \le y_{n-1} < \frac{1}{b}$, hence

```math
\delta = \frac{b - 1}{b^2} \le y_n - y_{n-1} = (b - 1) y_{n-1} < \frac{b - 1}{b} = 1 - \frac{1}{b} < 1 - \delta.
```

Now take any interval $[u, v) \subseteq [0, 1)$ of length $\ell = v - u$:
- *Upper bound on $F_N([u, v)) - \ell$:* If $\ell \ge \delta$, then $F_N([u, v)) - \ell \le 1 - \delta$. If $\ell < \delta$, no pair $\{y_{n-1}, y_n\}$ ($n \in S$) can both lie inside $[u, v)$ (since $y_n - y_{n-1} \ge \delta > \ell$); by disjointness, at least $M$ orbit points lie outside $[u, v)$, so $F_N([u, v)) - \ell \le 1 - M/N$.
- *Upper bound on $\ell - F_N([u, v))$:* If $\ell \le 1 - \delta$, then $\ell - F_N([u, v)) \le 1 - \delta$. If $\ell > 1 - \delta$, then the complement $[0, u) \cup [v, 1)$ has total length $1 - \ell < \delta$: neither $[0, u)$ nor $[v, 1)$ can contain both $y_{n-1}$ and $y_n$ (as $y_n - y_{n-1} \ge \delta$), and having $y_{n-1} < u$ with $y_n \ge v$ would force $y_n - y_{n-1} > v - u = \ell > 1 - \delta$, contradicting $y_n - y_{n-1} < 1 - \delta$. Hence every pair $\{y_{n-1}, y_n\}$ ($n \in S$) contributes at least one point to $[u, v)$, so $F_N([u, v)) \ge M/N$ and $\ell - F_N([u, v)) \le 1 - M/N$.

Taking the supremum over $0 \le u < v \le 1$ yields $D_N(x; b) \le 1 - \min(\delta, M/N)$. $\square$

*(Exact check: `scripts/phase25_lambert_eplus.py` verifies $2m - V(m) \ge 1$ for all $1 \le m \le 30{,}000$ on $\tau, \tau_{\rm odd}, 2^\omega$, certifies exact prefixes of length $N = 4000$ for $E(8), E(16), E_{\rm odd}(4), E_{\rm odd}(8), E^*(4), E^*(8)$ and $N = 2000$ for $E_3^*(9)$ by scaling every source $m \le \lfloor N_{\rm guard}/k \rfloor$ directly with rigorous tail bound $4(M_{\rm tot} + 2)$, and checks the non-tautological consequences of Lemma B1.2(1)–(2): carry nonnegativity $q_n \ge 0$, dead-position forcing $C_k(n) = q_n = 0$, exit transitions, and the exact dead-block inequality for $G \in \{2, 4, 8, 16\}$; note that once $q_n$ is reconstructed from the column recurrence, the column identity and mass conservation hold tautologically.)*

### 1.2 Zero-external-input transition and discrepancy-gap bound

**Corollary B1.2a (Zero-external-input $(\log\log N)^{-1/2}$ gap; Paper proof, zero external inputs).**
In the setting of Lemma B1.2, assume that $k > C_U$ and that $V(m)$ satisfies the elementary Turán–Kubilius variance bound $\sum_{m \le M} (V(m) - \alpha \log\log M)^2 \ll M \log\log M$ for some $\alpha > 0$ (which holds with $\alpha = 1$ for $\tau, \tau_{\rm odd}, b^\omega, \tau_p$ and $\alpha = m$ for $\tau_{2^m}$). Then for all sufficiently large $N$,

```math
\#\{1 \le n < N : d_n = 0,\, d_{n+1} \ne 0\} \gg_k \frac{N}{\sqrt{\log\log N}}, \qquad
1 - D_N(F_{b^k}(a); b) \gg_k \frac{1}{\sqrt{\log\log N}}.
```

*Proof.* Put $M = \lfloor N/k \rfloor$, $\mu_M = \alpha \log\log M$, and $G = \lceil C_0 \sqrt{\log\log M} \rceil$. Call $a \in [1, N - G + 1]$ *interior* if $\mu_M + G < a < N - \mu_M - G$ (omitting $O(\log\log N)$ indices). For each interior $a$, the set $J(a) = \{m \in [1, M] : a + \frac{G}{4} \le km - \mu_M \le a + \frac{3G}{4}\}$ has cardinality $|J(a)| = \frac{G}{2k} + O(1)$. If $C_k(a) = \cdots = C_k(a + G - 1) = 0$, then every $m \in J(a)$ must satisfy $km - V(m) \notin [a, a + G - 1]$, forcing $|V(m) - \mu_M| > G/4$. Since each $m$ belongs to $J(a)$ for at most $\frac{G}{2} + 1$ values of $a$, double counting gives

```math
\left(\frac{G}{2k} - 1\right) \#\{\text{empty interior } a\}
  \le \left(\frac{G}{2} + 1\right) \#\bigl\{m \le M : |V(m) - \mu_M| > G/4\bigr\}
  \ll G \cdot \frac{M \log\log M}{G^2}.
```

Hence $\#\{\text{empty } G\text{-windows}\} \le O(k M \frac{\log\log M}{G^2}) + O(\log\log N) = O(\frac{N}{C_0^2})$. Choosing $C_0$ sufficiently large makes this strictly below $\frac{1}{2}(1 - C_U/k) N$, and Lemma B1.2(2)–(3) immediately yield the stated bounds. $\square$

### 1.3 Unconditional positive lower transition density, $D^+ < 1$, and $F \notin K_b$

**Theorem B1.3 (Unconditional $D^+ < 1$ and non-membership in $K_b$ for nonnegative displaced Lambert series; Paper proof + Finite certificate; External input: upper bound of the 2-D Fundamental Lemma of the Combinatorial Sieve).**
Let $b \ge 2$, $k \ge 1$, and $a(m) = b^{V(m)} U(m) \ge 0$ satisfy Lemma B1.2, with **$a(m) \ge 1$ for all sufficiently large $m$** (full support), $V$ additive, $V(p) = \alpha \in \mathbb{Z}_{\ge 1}$ for all primes $p > p_0$, $V(p^e) = O(\log(e + 1))$, and $k > C_U$. Then:

1. $\displaystyle \lim_{G \to \infty} \limsup_{N \to \infty} \frac{1}{N} \#\{1 \le a \le N - G + 1 : C_k(a) = \cdots = C_k(a + G - 1) = 0\} = 0$.
2. $\displaystyle \liminf_{N \to \infty} \frac{\#\{1 \le n < N : d_n = 0,\, d_{n+1} \ne 0\}}{N} > 0$, hence **$D^+(F_{b^k}(a); b) < 1$** and **$F_{b^k}(a) \notin K_b$** (and in base $2$, $\liminf f_{1, N} > 0$).

In particular, combining with the certified enclosures of Proposition B1.1 and the $D^- > 0$ results of `GF-36`:
- **$E(2^k)$ ($k \ge 3$):** $0 < D^-(E(2^k); 2) \le D^+(E(2^k); 2) < 1$ and $E(2^k) \notin K_2$.
- **$E_{\rm odd}(2^k)$ ($k \ge 2$):** $D^+(E_{\rm odd}(2^k); 2) < 1$ and $E_{\rm odd}(2^k) \notin K_2$ (**including $E_{\rm odd}(4)$ at the $k = 2$ boundary!**), and $0 < D^- \le D^+ < 1$ for every $k \ge 3$.
- **$E^*(2^k)$ ($k \ge 2$):** $D^+(E^*(2^k); 2) < 1$ and $E^*(2^k) \notin K_2$ (**including $E^*(4)$ at $k = 2$!**), and $0 < D^- \le D^+ < 1$ for every $k \ge 3$.
- **$E_b^*(b^k)$ (every base $b \ge 2$, every $k \ge 2$):** $D^+(E_b^*(b^k); b) < 1$ and $E_b^*(b^k) \notin K_b$, with $0 < D^- \le D^+ < 1$ for every $(b, k)$ with $b \ge 3, k \ge 2$ or $b = 2, k \ge 3$ (note that $D^- > 0$ already holds at $k = 1$ for $b \ge 4$ by `GF-36`, Phase 24 Theorem 5.2(1)).

*Proof.* By Lemma B1.2(2)–(3), assertion (2) follows immediately from (1) by fixing $G \ge 2$ large enough that the empty-$G$-window upper density is strictly below $\frac{1}{2}(1 - C_U/k)$. We prove (1) via a good-source second moment and the Paley–Zygmund inequality (1932), taking limits in the strict order: fix $\varepsilon \in (0, \frac{1}{10})$ first (which fixes $p_1, K_0, \eta$, and $B_0$); next fix $G \ge 2$ large enough that $B_0/G < \varepsilon$ and $k/G < \varepsilon$; then let $N \to \infty$ (with $M = \lfloor N/k \rfloor \to \infty$, so all $O_{G, \alpha, B_0}(\cdot)$ terms vanish with no hidden uniformity in $N$); finally let $G \to \infty$ and $\varepsilon \to 0$.

**Step 1 (Good source subset $\mathcal{G}$).** Fix any $\varepsilon \in (0, \frac{1}{10})$. Set $M = \lfloor N/k \rfloor$ and $L = \log\log M$. Choose fixed parameters:
- $p_1 \ge \max(5, p_0, \lceil 200/\varepsilon \rceil)$ so that $\sum_{p > p_1} p^{-2} < \varepsilon/4$;
- $K_0 \ge 1$ so that $\#\{m \le M : V_{\le p_1}(m) > K_0\} \le (\varepsilon/4 + o(1)) M$, where $V_{\le p_1}(m) = \sum_{p \le p_1} V(p^{v_p(m)})$;
- $\eta \in (0, \varepsilon/32]$ small enough that the uniform 2-D Fundamental Lemma sieve error factor $1 + O(e^{-s \log s + O(s)})$ at $s = \frac{3}{8\eta}$ is at most $1 + \varepsilon$.

Define $\mathcal{G} = \mathcal{G}(M)$ as the set of integers $m \in ((\log_2 M)/k, M]$ with $a(m) \ge 1$ (automatic for all large $m$) such that:
1. $p^2 \nmid m$ for all $p > p_1$;
2. $V_{\le p_1}(m) \le K_0$;
3. $u(m) := \prod_{p_1 < p \le M^\eta,\, p \mid m} p \le M^{1/8}$.

To bound the complement of condition (3) elementarily (without Dickman's function), note by Mertens' first theorem that $\sum_{m \le M} \log u(m) = \sum_{p_1 < p \le M^\eta} (\log p) \lfloor M/p \rfloor \le M (\eta \log M + O(1))$, so Markov's inequality gives $\#\{m \le M : u(m) > M^{1/8}\} \le (8\eta + o(1)) M \le (\frac{\varepsilon}{4} + o(1)) M$. Combining (1)–(3) yields $|\mathcal{G}| \ge (1 - \varepsilon) M$ for all large $M$. Moreover, every $m \in \mathcal{G}$ has at most $\lfloor 1/\eta \rfloor$ prime divisors $> M^\eta$ (all simple), so

```math
V(m) = \alpha\, \omega_{(p_1, M^\eta]}(m) + V_{\rm bdd}(m), \qquad 0 \le V_{\rm bdd}(m) \le K_0 + \alpha \lfloor 1/\eta \rfloor =: B_0.
```

**Step 2 (Window count and diagonal/tail split).** Fix an integer $G \ge 2$ with $B_0/G < \varepsilon$ and $k/G < \varepsilon$, and define $Z_a^{\mathcal{G}} = \#\{m \in \mathcal{G} : a \le km - V(m) < a + G\}$ for $1 \le a \le N$. Every $m \in \mathcal{G}$ satisfies $1 \le km - V(m) \le N$ and $a(m) \ge 1$ (so $U(m) \ge 1$), giving $\frac{1}{N} \sum_{a=1}^N Z_a^{\mathcal{G}} = \frac{G |\mathcal{G}|}{N} - O(\frac{G^2}{N}) \ge \frac{G}{k}(1 - \varepsilon) - o(1)$. Expanding the second moment gives

```math
\sum_{a=1}^N \bigl(Z_a^{\mathcal{G}}\bigr)^2
  \le G |\mathcal{G}| + 2 \sum_{d \ge 1} \sum_{\substack{m,\, m + d \in \mathcal{G}}} \bigl(G - |kd - (V(m+d) - V(m))|\bigr)_+.
```

Set $G' = G + B_0$ and $D_0 = \lceil (10 \alpha L + G + B_0)/k \rceil$. For the tail $d > D_0$: whenever $G - |kd - (V(n) - V(m))| > 0$ with $n = m + d \in \mathcal{G}$, nonnegativity $V(m) \ge 0$ forces $kd < V(n) + G$, so $V(n) > k D_0 - G \implies \omega(n) > 10 L$, and for fixed $n$ at most $(V(n) + G)/k$ values of $d > D_0$ can occur. Using $\omega(n) \le 2^{\omega(n)}$ and the elementary bound $\sum_{n \le M} 4^{\omega(n)} \le \sum_{n \le M} \tau_4(n) \ll M (\log M)^3$,

```math
\sum_{d > D_0} \sum_{m, m+d \in \mathcal{G}} \bigl(G - |kd - (V(m+d) - V(m))|\bigr)_+
  \le G \sum_{\substack{n \le M \\ \omega(n) > 10 L}} \frac{\alpha \omega(n) + B_0 + G}{k}
  \ll_{G, \alpha, B_0} 2^{-10 L} M (\log M)^3
  \ll M (\log M)^{3 - 10 \ln 2} = o(M),
```

since $3 - 10 \ln 2 \approx -3.93 < 0$.

**Step 3 (2-D Fundamental Lemma sieve for $1 \le d \le D_0$).** Fix $1 \le d \le D_0$ and put $\mathcal{P}_d = \{p \text{ prime} : p_1 < p \le M^\eta,\, p \nmid d\}$. Every prime $p \in (p_1, M^\eta]$ dividing $d$ divides $m$ iff it divides $m + d$, so its contribution to $\omega_{(p_1, M^\eta]}(m+d) - \omega_{(p_1, M^\eta]}(m)$ cancels identically! For $m, m+d \in \mathcal{G}$, writing $u_1 = \prod_{p \in \mathcal{P}_d, p \mid m} p$ and $u_2 = \prod_{p \in \mathcal{P}_d, p \mid (m+d)} p$, we have $\gcd(u_1, u_2) = 1$ (since $\gcd(m, m+d) \mid d$), $u_1 u_2 \le u(m) u(m+d) \le M^{1/4}$, and $|V(m+d) - V(m) - \alpha(\omega(u_2) - \omega(u_1))| \le B_0$, hence

```math
\bigl(G - |kd - (V(m+d) - V(m))|\bigr)_+ \le \bigl(G' - |kd - \alpha(\omega(u_2) - \omega(u_1))|\bigr)_+.
```

Moreover, every such $m$ belongs to the sifted set

```math
A_d(u_1, u_2) := \left\{m \le M : u_1 \mid m,\ u_2 \mid (m+d),\ \gcd\!\left(\frac{m}{u_1} \cdot \frac{m+d}{u_2},\, P_d(u_1, u_2)\right) = 1\right\},
\qquad P_d(u_1, u_2) = \prod_{\substack{p \in \mathcal{P}_d \\ p \nmid u_1 u_2}} p.
```

Since $\gcd(u_1, u_2) = 1$, the congruences $u_1 \mid m$ and $u_2 \mid (m+d)$ define a unique progression modulo $u_1 u_2$ of length $X = M/(u_1 u_2)$, and each prime $p \mid P_d(u_1, u_2)$ excludes two distinct residues $m \equiv 0, -d \pmod p$ (distinct because $p \nmid d$), so the local density function is $g(p) = 2/p$ for $p \mid P_d(u_1, u_2)$ and $g(p) = 0$ otherwise. Because $p_1 \ge 5$, $0 \le g(p) \le \frac{2}{5} < 1$ uniformly, and for all $2 \le w < z$ the sieve dimension condition of dimension $\kappa = 2$ holds with an **absolute** constant $K$ independent of $(d, u_1, u_2)$:

```math
\prod_{w \le p < z} \bigl(1 - g(p)\bigr)^{-1}
  \le \prod_{w \le p < z} \left(1 - \frac{2}{p}\right)^{-1}
  \le \left(\frac{\log z}{\log w}\right)^2 \left(1 + \frac{K}{\log w}\right).
```

Also, for every squarefree $q \mid P_d(u_1, u_2)$, the congruence count has remainder $|R_q| \le 2^{\omega(q)}$. Applying the **upper bound of the Fundamental Lemma of the Combinatorial Sieve** at dimension $\kappa = 2$ (Halberstam–Richert, *Sieve Methods*, Academic Press, 1974, Theorem 2.5, pp. 82–85; Tenenbaum, *Introduction to Analytic and Probabilistic Number Theory*, 3rd ed., AMS GSM 163, 2015, Ch. I.4, Theorem 3, p. 60; Iwaniec–Kowalski, *Analytic Number Theory*, AMS Colloq. Publ. Vol. 53, 2004, §6.4, pp. 158–160; *External input*) with level $D = M^{3/8}$ and sifting limit $z = M^\eta$ (so $s = \frac{\log D}{\log z} = \frac{3}{8\eta}$ is fixed, giving an error factor $1 + O(e^{-s \log s + O(s)}) \le 1 + \varepsilon$ **uniformly** in $(d, u_1, u_2)$) yields

```math
|A_d(u_1, u_2)|
  \le (1 + \varepsilon) \frac{M}{u_1 u_2} \prod_{\substack{p \in \mathcal{P}_d \\ p \nmid u_1 u_2}} \left(1 - \frac{2}{p}\right)
      + O\!\left(\sum_{\substack{q \le M^{3/8} \\ q \mid P_d(u_1, u_2)}} 2^{\omega(q)}\right).
```

Summing the remainder over all $1 \le d \le D_0 = O(L)$ and all coprime squarefree pairs $u_1 u_2 \le M^{1/4}$ (of which there are $\le \sum_{w \le M^{1/4}} \tau(w) \ll M^{1/4} \log M$) gives total sieve remainder $\ll G' L \cdot (M^{1/4} \log M) \cdot (M^{3/8} \log M) = O(M^{5/8} (\log M)^3) = o(M)$. Meanwhile, the main term $\frac{1}{u_1 u_2} \prod_{p \in \mathcal{P}_d, p \nmid u_1 u_2} (1 - \frac{2}{p})$ equals **identically** $\Pr(\{p : \xi_p = -1\} = \{p \mid u_1\},\, \{p : \xi_p = +1\} = \{p \mid u_2\})$ for independent trinomial random variables $\xi_p \in \{-1, 0, +1\}$ ($p \in \mathcal{P}_d$) with $\Pr(\xi_p = \pm 1) = \frac{1}{p}$ and $\Pr(\xi_p = 0) = 1 - \frac{2}{p}$! Putting $S_d = \sum_{p \in \mathcal{P}_d} \xi_p$ and extending the nonnegative sum over $u_1 u_2 \le M^{1/4}$ to all pairs $(u_1, u_2)$ gives

```math
\sum_{\substack{m, m+d \in \mathcal{G}}} \bigl(G - |kd - (V(m+d) - V(m))|\bigr)_+
  \le (1 + \varepsilon) M \sum_{\substack{|r| < G' \\ \alpha \mid (kd - r)}} (G' - |r|)\, \Pr\!\left(S_d = \frac{kd - r}{\alpha}\right) + \text{rem}_d.
```

**Step 4 (Cramér Fourier-shift bound on $\Pr(S_d = h)$ and Paley–Zygmund).** Put $E_d = \sum_{p \in \mathcal{P}_d} \frac{1}{p}$. Uniformly for $1 \le d \le D_0 = O(L)$, $\sum_{p \mid d, p > p_1} \frac{1}{p} = O(\log\log\log L)$, so $E_d = L - O_{\eta, p_1}(1) - O(\log\log\log L)$ uniformly for $1 \le d \le D_0$ (in particular $E_{\min} := \min_{1 \le d \le D_0} E_d$ and $E_{\max} := \max_{1 \le d \le D_0} E_d$ satisfy $E_{\min}/L \to 1$ and $E_{\max}/E_{\min} \to 1$). For any real $\lambda \ge 0$ and $h \in \mathbb{Z}$, shifting the Fourier inversion contour $t \mapsto t - i\lambda$ gives

```math
\Pr(S_d = h) = \frac{e^{-\lambda h}}{2\pi} \int_{-\pi}^{\pi} e^{-i h t} \prod_{p \in \mathcal{P}_d} \left(1 + \frac{2(\cosh(\lambda + i t) - 1)}{p}\right) dt.
```

For each $p \in \mathcal{P}_d$, write $a = \frac{2(\cosh\lambda \cos t - 1)}{p}$ and $b = \frac{2\sinh\lambda \sin t}{p}$; then $a^2 + b^2 = \frac{4}{p^2}(\cosh^2\lambda - 2\cosh\lambda \cos t + \cos^2 t) \le \frac{16 \cosh^2\lambda}{p^2}$, so $\sqrt{(1 + a)^2 + b^2} \le \exp\bigl(a + \frac{8 \cosh^2\lambda}{p^2}\bigr)$. Multiplying over $p \in \mathcal{P}_d$ (using $\sum_{p > p_1} p^{-2} < 1/p_1 \le \varepsilon/200$) and bounding $\frac{1}{2\pi} \int_{-\pi}^{\pi} e^{-A(1 - \cos t)} dt \le (1 + O(A^{-1/3}))/\sqrt{2\pi A}$ at $A = 2 E_d \cosh\lambda$:
- At $\lambda = 0$, $\Pr(S_d = h) \le \frac{1 + \varepsilon}{\sqrt{4\pi E_d}}$ for all $h \in \mathbb{Z}$ and all large $M$.
- For $0 \le h \le E_d^{2/3}$, choose $\lambda = \frac{h}{2 E_d} \in [0, \frac{1}{2} E_d^{-1/3}]$: then $-\lambda h + 2 E_d(\cosh\lambda - 1) = -\frac{h^2}{4 E_d} + O(E_d^{-1/3})$, yielding $\Pr(S_d = h) \le \frac{1 + \varepsilon}{\sqrt{4\pi E_d}} \exp\bigl(-\frac{h^2}{4 E_d}\bigr)$ for all large $M$.
- For $h > E_d^{2/3}$, choose $\lambda = \frac{1}{2} E_d^{-1/3}$: since $\cosh\lambda - 1 \le \frac{3}{5}\lambda^2$ on $[0, 1]$, $-\lambda h + 2 E_d(\cosh\lambda - 1) \le (-\frac{1}{2} + \frac{3}{10}) E_d^{1/3} = -\frac{1}{5} E_d^{1/3}$, so summing over all $d \le D_0$ with $(kd - r)/\alpha > E_d^{2/3}$ contributes $\ll (G')^2 L E_{\min}^{-1/2} e^{-\frac{1}{5} E_{\min}^{1/3}} = o(1)$.

For the main sum over $1 \le d \le D_0$ with $(kd - r)/\alpha \le E_d^{2/3}$:
- First, the finitely many $d$ with $1 \le d \le d_0 := \lfloor G'/k \rfloor$ (which include every pair $(d, r)$ with $kd - r \le 0$) satisfy $\Pr(S_d = h) \le \frac{1 + \varepsilon}{\sqrt{4\pi E_{\min}}}$ and contribute at most $O((G')^3 / (k \sqrt{E_{\min}})) = o(1)$ as $M \to \infty$ (since $G'$ is fixed while $E_{\min} \to \infty$).
- Second, for every $d > d_0$ and $|r| < G'$, we have $(kd - r)/\alpha \ge (kd - G')/\alpha \ge k(d - d_0 - 1)/\alpha \ge 0$, and for each fixed $d$ the weight sum satisfies $\sum_{|r| < G',\, \alpha \mid (kd - r)} (G' - |r|) = \frac{(G')^2}{\alpha} + O(G')$. Writing $d' = d - d_0 \ge 1$, monotonicity of $u \mapsto e^{-u^2/(4 E_{\max})}$ on $u \ge 0$ bounds the Riemann sum of step $\Delta u = k/\alpha$ by its $d' = 1$ boundary term plus the integral:

```math
2 \left(\frac{(G')^2}{\alpha} + O(G')\right) \sum_{d' \ge 1} \frac{1}{\sqrt{4\pi E_{\min}}} \exp\!\left(-\frac{(k(d' - 1)/\alpha)^2}{4 E_{\max}}\right)
  \le 2 \left(\frac{(G')^2}{\alpha} + O(G')\right) \left(\frac{1}{\sqrt{4\pi E_{\min}}} + \frac{\alpha}{k} \int_0^\infty \frac{e^{-u^2/(4 E_{\max})}}{\sqrt{4\pi E_{\min}}}\, du\right)
  = \left(\frac{(G')^2}{k} + O\!\left(\frac{\alpha G'}{k}\right)\right)\!\left(\sqrt{\frac{E_{\max}}{E_{\min}}} + O\!\left(\frac{k}{\alpha\sqrt{E_{\min}}}\right)\right).
```

Since $E_{\max}/E_{\min} \to 1$ as $M \to \infty$, dividing the second moment by $N = kM + O(1)$ and letting $N \to \infty$ (with $\varepsilon, G$ fixed, and choosing $G$ large enough that $\alpha G' / (G')^2 < \varepsilon$ as well as $B_0/G < \varepsilon, k/G < \varepsilon$) yields

```math
\limsup_{N \to \infty} \frac{1}{N} \sum_{a=1}^N \bigl(Z_a^{\mathcal{G}}\bigr)^2
  \le \frac{G}{k} + (1 + \varepsilon)^4 \frac{(G + B_0)^2}{k^2}.
```

Applying the Paley–Zygmund inequality gives

```math
\liminf_{N \to \infty} \frac{1}{N} \#\{a \le N : Z_a^{\mathcal{G}} > 0\}
  \ge \frac{\bigl(\frac{G}{k}(1 - \varepsilon)\bigr)^2}{\frac{G}{k} + (1 + \varepsilon)^4 \frac{(G + B_0)^2}{k^2}}
  \ge \frac{(1 - \varepsilon)^2}{\varepsilon + (1 + \varepsilon)^6} = 1 - O(\varepsilon).
```

Since $Z_a^{\mathcal{G}} > 0$ implies $C_k(a + j) \ge 1$ for some $0 \le j < G$ (because every $m \in \mathcal{G}$ has $a(m) \ge 1$, hence $U(m) \ge 1$), letting $G \to \infty$ and then $\varepsilon \to 0$ yields assertion (1).

*Remark (necessity of the sharp constant).* Obtaining the exact leading constant $1 + O(\varepsilon)$ in the second moment is essential: a non-sharp Erdős–Pomerance–Sárközy-type upper bound $\Pr(S_d = h) \le C/\sqrt{L}$ with an unspecified constant $C > 1$ would give only $\liminf \#\{Z_a^{\mathcal{G}} > 0\}/N \ge 1/C$, which cannot force the empty-window upper density below $1 - C_U/k$ unless $C < k/C_U$—failing at the $k = 2$ boundary ($k/C_{U, \rm odd} \approx 1.426$ for $E_{\rm odd}(4)$ and $k/C_{U^*} = 2$ for $E^*(4)$). $\square$

### 1.4 Signed Isolated-Odd-Arrival Theorem for $E_+(2^k)$ and cubic $L_\pm(2^k)$

Because $a_+(n)$ changes sign, Lemma B1.2(2) does not apply directly to $E_+(2^k)$. Nevertheless, a clean parity-and-tail criterion replaces dead blocks and proves $D^+ < 1$ and $\notin K_2$ for all sufficiently large $k$—resolving the open $D^+ < 1$ questions for $E_+(2^k)$ (`GF-36`, `GF-40`) and for cubic-character series $L_\pm(2^k)$ (`GF-31`) at large $k$.

**Theorem B1.4 (Signed Isolated-Odd-Arrival Theorem; Paper proof + Finite certificate; External inputs: 2-D and $\kappa = \frac{2}{3}$ Fundamental Lemma, plus Dirichlet's theorem / Halász for $L_-$).**
1. *(Isolated-odd-arrival transition lemma.)* Let $x = \sum_{n \ge 1} C_k(n) 2^{-n}$ ($C_k(n) \in \mathbb{Z}$) with $Y_n = \sum_{j \ge 1} C_k(n + j) 2^{-j}$. For every $n \ge 1$, if **$C_k(n)$ is odd** and **$|Y_n| < \frac{1}{2}$**, then $\{2^{n-1} x\} \in (\frac{1}{4}, \frac{3}{4})$ and therefore $d_n(x; 2) \ne d_{n+1}(x; 2)$ is a binary transition.
2. *(Application to $E_+(2^k)$.)* There exists an effective (but unspecified) constant $k_0 \ge 3$ such that for every $k \ge k_0$,

```math
\liminf_{N \to \infty} \frac{\mathrm{tr}_N(E_+(2^k))}{N} \ge \frac{1}{2k} > 0, \qquad
0 < D^-(E_+(2^k); 2) \le D^+(E_+(2^k); 2) < 1, \qquad
E_+(2^k) \notin K_2.
```

3. *(Application to cubic-character Lambert series $L_\pm(2^k)$.)* For every cubic Dirichlet character $\chi \bmod M$ and both projections $L_+(2^k), L_-(2^k)$ of `GF-31`, there exists an effective (but unspecified) $k_0(\chi)$ such that for every $k \ge k_0(\chi)$, $0 < D^-(L_\pm(2^k); 2) \le D^+(L_\pm(2^k); 2) < 1$ and $L_\pm(2^k) \notin K_2$.

*Proof.*
(1) Write $2^{n-1} x = I_{n-1} + \frac{C_k(n) + Y_n}{2}$ with $I_{n-1} \in \mathbb{Z}$. Since $C_k(n)$ is odd and $|Y_n| < \frac{1}{2}$, $\frac{C_k(n) + Y_n}{2} \in \mathbb{Z} + (\frac{1}{4}, \frac{3}{4})$, so $\{2^{n-1} x\} \in (\frac{1}{4}, \frac{3}{4})$, meaning $(d_n, d_{n+1}) \in \{01, 10\}$. *(Verified across 570, 450, 360 isolated arrivals in certified 2,400-bit prefixes of $E_+(8), E_+(16), E_+(32)$ in `scripts/phase25_lambert_eplus.py`.)*

(2) For $E_+(2^k)$, the support $\{m \ge 1 : a_+(m) \ne 0\} = \{m : m \not\equiv 2 \pmod 4\}$ has natural density $\delta = \frac{3}{4}$, and every nonzero $a_+(m)$ has odd part $U_+(m)$ with finite second moment $M_2 := \mathbb{E}[U_+(m)^2] = \bigl(\frac{1}{2} + \sum_{e \ge 2} \operatorname{odd}(e-1)^2 2^{-(e+1)}\bigr) \prod_{p > 2} (1 - \frac{1}{p})\sum_{e \ge 0} \operatorname{odd}(e+1)^2 p^{-e} < \infty$ (via Wintner's squarefull convolution lemma). Fix a single concrete $\varepsilon \in \bigl(0, \min\bigl(\frac{1}{40},\, \frac{1}{320^2 (M_2 + 1)}\bigr)\bigr)$ (in particular $\varepsilon < 10^{-5}$, ensuring $\eta_1 := \sqrt{\varepsilon M_2} < \frac{1}{320}$) and corresponding fixed constants $p_1, K_0, \eta$ (hence fixed $B_0 = K_0 + \lfloor 1/\eta \rfloor$) as in Theorem B1.3 Step 1, so that the good-support subset $\mathcal{G}_+ = \{m \in \mathcal{G} : m \not\equiv 2 \pmod 4\}$ satisfies $|\mathcal{G}_+| \ge (\frac{3}{4} - \varepsilon) M$ and Cauchy–Schwarz gives the bad-source $L^1$ mass bound $\limsup_{M \to \infty} \frac{1}{M} \sum_{m \le M,\, m \notin \mathcal{G}} |U_+(m)| \le \sqrt{\varepsilon M_2} = \eta_1 < \frac{1}{320}$. Next, using the certified mean $C_{U, +} \in [1.220298, 1.220360]$ of Proposition B1.1, set the explicit cutoff

```math
j_0 := \bigl\lceil \log_2(320\, C_{U, +}) \bigr\rceil = 9 \qquad \bigl(256 < 320\, C_{U, +} < 512\bigr),
```

which depends only on $C_{U, +}$ (asserted in `scripts/phase25_lambert_eplus.py`). Split all sources $m \ge 1$ into $\mathcal{G}(M)$, the bad sources $m \in [1, M] \setminus \mathcal{G}(M)$, and the tail $m > M$ (whose total contribution to $\sum_{n=1}^N |Y_n|$ and to arrivals in $[1, N]$ is $O(M^\varepsilon \log M) = o(M)$):
- At most $\varepsilon M + O(\log M)$ positions $n \le N$ receive any source $m' \notin \mathcal{G}(M)$ directly. Writing $Y_n^{\rm bad}$ for the tail sum $\sum_{j \ge 1} |C_k^{\rm bad}(n + j)| 2^{-j}$ from all sources $m' \notin \mathcal{G}(M)$, we have $\sum_{n=1}^N Y_n^{\rm bad} \le (\eta_1 + o(1)) M$, so Markov's inequality bounds the positions with $Y_n^{\rm bad} \ge \frac{1}{8}$ by $(8 \eta_1 + o(1)) M \le \frac{1}{40} M$ for all large $M$.
- For the far good tail ($j > j_0 = 9$), writing $Y_n^{\rm far} := \sum_{j > j_0} |C_k^{\mathcal{G}}(n + j)| 2^{-j}$, summing over $1 \le n \le N$ and applying Markov's inequality with the mean $C_{U, +}$ yields

```math
\sum_{n=1}^N Y_n^{\rm far}
  \le 2^{-j_0} \sum_{m \in \mathcal{G}(M)} |U_+(m)|
  \le 2^{-9} (C_{U, +} + o(1)) M < \frac{1}{320} M,
```

  so at most $8 \cdot 2^{-9} (C_{U, +} + o(1)) M < \frac{1}{40} M$ positions have $Y_n^{\rm far} \ge \frac{1}{8}$ for all large $M$.
- A source $m \in \mathcal{G}_+$ landing at $n = km - V_+(m)$ outside the above exceptions fails to be an isolated odd arrival with $|Y_n| < \frac{1}{4} < \frac{1}{2}$ **only if** some $m' \in \mathcal{G}_+ \setminus \{m\}$ lands at $n + j$ for some $0 \le j \le j_0$. By Steps 2–4 of Theorem B1.3 applied to each fixed $0 \le j \le j_0$ (summing over both signs of $d = m' - m \ne 0$ and the $2 B_0 + 1$ values of $\Delta_{\rm bdd}$; each sign contributes $\le \frac{(1+\varepsilon)^2 (2 B_0 + 1)}{2k} M$ per $j$), the number of such colliding $m \in \mathcal{G}_+$ is at most $\frac{(1 + \varepsilon)^2 (j_0 + 1)(2 B_0 + 1) + o(1)}{k} M < \frac{2(j_0 + 1)(2 B_0 + 1)}{k} M$ for all large $M$.

Setting $k_0 = \lceil 80 (j_0 + 1)(2 B_0 + 1) \rceil = \lceil 800 (2 B_0 + 1) \rceil$ (effective, with $k_0 > 3.05 \times 10^{10}$ under these fixed parameters), for every $k \ge k_0$ at least $(\frac{3}{4} - 2\varepsilon - \frac{1}{40} - \frac{1}{40} - \frac{1}{40} - o(1)) M > \frac{1}{2} M = \frac{N}{2k} - O(1)$ distinct positions $n \in [1, N]$ satisfy $d_n \ne d_{n+1}$ (accounting for both the $\le \varepsilon M$ bad-source exclusions from $\mathcal{G}_+$ and the $\le \varepsilon M$ positions hit directly by bad sources, with $|a_+(m)| \ge 1$ on $\mathcal{G}_+$). Applying `CC-04` (or noting that binary transitions alternate $(0, 1)$ and $(1, 0)$ and applying Lemma B1.2(3)) yields $D^+(E_+(2^k); 2) < 1$ and $E_+(2^k) \notin K_2$; `GF-40` supplies $D^- > 0$.

(3) For a cubic character $\chi \bmod M$, $c_\pm(n) = \varepsilon_\pm(t(n)) A(n)$ on its support $S_\chi = \{n : v_p(n) \not\equiv 2 \pmod 3\ \forall \chi(p) \in \{\omega, \bar\omega\}\}$, where $A(n) = \prod_{\chi(p) = 1} (v_p(n) + 1) = 2^{V_\chi(n)} U_\chi(n)$ and $\varepsilon_\pm \in \{0, \pm 1, \pm 2\}$. Here $\mathbb{E}[U_\chi^2] < \infty$, $V_\chi(p) = 1$ on the split primes $\chi(p) = 1$ (density $1/3$) and $V_\chi(p) = 0$ on non-split primes. Because $V_\chi(p) = 0$ at non-split primes, we run the Step 3 Fundamental Lemma sieve over **split primes only**: $\mathcal{P}_d^{\rm split} = \{p \in (p_1, M^\eta] : \chi(p) = 1,\, p \nmid d\}$, with $g(p) = 2/p$ on $\mathcal{P}_d^{\rm split} \setminus \{p \mid u_1 u_2\}$ and $g(p) = 0$ otherwise. This is a sieve of dimension $\kappa = 2/3$ (with sieve constant $K = K(\chi)$ verified via the Prime Number Theorem in Arithmetic Progressions), to which the Fundamental Lemma applies identically (with $E_d = \sum_{p \in \mathcal{P}_d^{\rm split}} \frac{1}{p} = \frac{1}{3} \log\log M + O_{\chi, \eta, p_1}(1) - O(\log\log\log L) \to \infty$, and the exact same Gaussian local bound and Riemann sum, while $d > D_0$ still forces $\omega(n) > 10 L$). The nonzero support has positive density $\delta_+ = \prod_{\chi(p) \in \{\omega, \bar\omega\}} \frac{1 - p^{-2}}{1 - p^{-3}} > 0$ for $L_+$ and $\delta_- = \frac{2}{3} \delta_+ > 0$ for $L_-$ (via Halász on $\mathbf{1}_{S_\chi} e^{2\pi i t/3}$). Replacing $C_{U, +}$ by $C_{U, \chi}$ in the Markov cutoff $j_0(\chi) = \lceil \log_2(320 C_{U, \chi}/\delta_\pm) \rceil$ and absorbing the $\le 1$-bit shift from $\varepsilon_+ = \pm 2$ into $B_0 + 1$, the same argument gives $\liminf \mathrm{tr}_N(L_\pm(2^k))/N \ge \delta_\pm/(2k) > 0$, $D^+(L_\pm(2^k); 2) < 1$, and $L_\pm(2^k) \notin K_2$ for all $k \ge k_0^{\rm iso}(\chi)$. For the lower discrepancy bound, `GF-36` Proposition 8.1 gives $W_\chi < \infty$ for every cubic character $\chi$ (with $W_\chi < 1$ certified for $M \in \{7, 9, 13\}$, giving $D^- > 0$ already for $k \ge 4$), and the signed transition-count transfer of `GF-36` Theorem 7.1 yields $D^-(L_\pm(2^k); 2) > 0$ for every $k > 4 W_\chi$; taking $k_0(\chi) := \max(k_0^{\rm iso}(\chi), \lfloor 4 W_\chi \rfloor + 1)$ gives $0 < D^-(L_\pm(2^k); 2) \le D^+(L_\pm(2^k); 2) < 1$ for every cubic $\chi$ and every $k \ge k_0(\chi)$. $\square$

### 1.5 Higher-kernel exclusions $x \notin K_{2^j}$

**Theorem B1.5 (Exclusion from the higher kernel tower $K_{2^j}$; Paper proof + Finite certificate; External inputs: Halász 1968 and Theorem B1.3 for $K_2$).**
Let $a(m) = 2^{V(m)} U(m) \ge 0$ satisfy Lemma B1.2 and Theorem B1.3 with $V(p) = 1$ for all $p > p_0$ (e.g. $a \in \{\tau, \tau_{\rm odd}, 2^\omega\}$). Fix $k > C_U$ (so $F_{2^k}(a) \notin K_2$ by Theorem B1.3) and $j \ge 2$. If

```math
\frac{C_U}{k} < \frac{2^{j-1}}{2^j - 1},
```

then **$F_{2^k}(a) \notin K_{2^j}$**. In particular, whenever **$C_U / k \le \frac{1}{2}$**, we have **$F_{2^k}(a) \notin K_{2^j}$ for every $j \ge 1$ simultaneously**. Consequently:
1. **$E(2^k) \notin K_{2^j}$ for every $k \ge 5$ and every $j \ge 1$** ($C_U / 5 \le 0.415283 < \frac{1}{2}$);
2. **$E(16) \notin K_2, K_4, K_8, K_{16}$** ($C_U / 4 \le 0.519103 < \frac{8}{15}$);
3. **$E(8) \notin K_2, K_4$** (with $E(8) \notin K_4 \setminus K_2$ following directly from `GF-36`: every $x \in K_4 \setminus K_2$ has $f_{1, N}(x; 2) \to \frac{1}{2}$, whereas $\limsup f_{1, N}(E(8); 2) \le C_{\rm true}/3 \le 0.44638 < \frac{1}{2}$, where $C_{\rm true} := \lim_{X \to \infty} \frac{1}{X} \sum_{n \le X} s_2(\tau(n)) \in [1.339103, 1.339116]$);
4. **$E_{\rm odd}(2^k) \notin K_{2^j}$ for every $k \ge 3$ and every $j \ge 1$** ($C_{U, \rm odd}/3 \le 0.467505 < \frac{1}{2}$);
5. **$E^*(2^k) \notin K_{2^j}$ for every $k \ge 2$ and every $j \ge 1$**—including **$E^*(4) \notin K_{2^j}$ for all $j \ge 1$**, since $C_{U^*}/2 = \frac{1}{2} < \frac{2^{j-1}}{2^j - 1}$ for every $j \ge 2$ and $E^*(4) \notin K_2$ by Theorem B1.3!

*Proof.* Suppose for contradiction that $F = F_{2^k}(a) \in K_{2^j} \setminus K_2$. By `GF-29` (`kernel_eq_fixedPoint_add_zeroOrbit`), $F \equiv \frac{R}{2^j - 1} + w \pmod{1}$ for some integer $0 \le R \le 2^j - 2$ and $w \in M_{2^j}$. Note that $M_{2^j} \subseteq M_2 \subseteq K_2$: since $\|2y\| \le 2\|y\|$, averaging over $0 \le n < jM$ gives $\frac{1}{jM} \sum_{n < jM} \|2^n w\| \le \frac{2^j - 1}{j} \cdot \frac{1}{M} \sum_{m < M} \|2^{jm} w\| \to 0$ (cf. `GF-23` `zeroOrbitSubgroup_pow_eq`). Hence $R = 0$ would force $F \in M_2 \subseteq K_2$, contradicting $F \notin K_2$; thus $1 \le R \le 2^j - 2$. Letting $b_1 \cdots b_j \in \{0, 1\}^j$ be the periodic binary digits of $R/(2^j - 1)$, a density-1 set of blocks $m$ has $d_{jm + r + 1}(F; 2) = b_{r+1}$, so $\lim_{N \to \infty} \frac{j}{N} \sum_{n \le N,\, n \equiv r+1 (j)} d_n = b_{r+1}$ for each $r \in \{0, \ldots, j - 1\}$.

Now average the exact carry identity $C_k(n) + q_n = d_n + 2 q_{n-1}$ of Lemma B1.2(1) along $n \equiv r + 1 \pmod j$. We claim that the phase-restricted arrival average satisfies

```math
\lim_{N \to \infty} \frac{j}{N} \sum_{\substack{1 \le n \le N \\ n \equiv r + 1 \pmod j}} C_k(n) = \frac{C_U}{k} =: c \qquad (\forall r \in \{0, \ldots, j - 1\}).
```

Indeed, by Fourier orthogonality mod $j$, this reduces to showing $\frac{1}{X} \sum_{m \le X} U(m)\, e\!\left(\frac{u(km - V(m))}{j}\right) \to 0$ for every $1 \le u \le j - 1$. Truncating $m = m_y r'$ to $y$-good squarefree-tail integers ($P^-(r') > y$, $r'$ squarefree, where $U(m) = U(m_y)$ and the bad-tail $U$-mass vanishes as $y \to \infty$ by `GF-36` Lemma 3.2) reduces the sum to $\frac{1}{Y} \sum_{r' \le Y} \mathbf{1}_{\rm good}(r')\, e(\frac{u k m_y}{j} r')\, e(-\frac{u}{j} V(r'))$. Since $\frac{u k m_y}{j}$ is rational, $r' \mapsto e(\frac{u k m_y}{j} r')$ is periodic modulo $j$ and expands as a finite linear combination of Dirichlet characters $\chi \bmod d$ ($d \mid j$). For every Dirichlet character $\chi \bmod d$ ($d \mid j$), every $1 \le u \le j - 1$, and every $t \in \mathbb{R}$, on the primes $p \equiv 1 \pmod j$ (Dirichlet density $1/\varphi(j) > 0$) we have $\chi(p) e(-u V(p)/j) = e(-u/j) \ne 1$, so $\sum_p \frac{1 - \Re(\chi(p) e(-u/j) p^{-it})}{p} = \infty$. By **Halász's theorem** (1968; *External input*), every term tends to $0$, proving the claim.

Since $0 \le x_r(N) := \frac{j}{N} \sum_{n \le N,\, n \equiv r (j)} q_n \le \frac{j}{N} \sum_{n=1}^N q_n = O(1)$, extracting a convergent subsequence $x_r(N_\nu) \to x_r \ge 0$ gives the $j \times j$ cyclic linear system

```math
2 x_r - x_{(r + 1) \bmod j} = c - b_{r + 1} \qquad (r = 0, 1, \ldots, j - 1).
```

The circulant matrix $2I - S$ is invertible (determinant $2^j - 1 \ne 0$), and $z_r := \{2^r R / (2^j - 1)\}$ satisfies $2 z_r - z_{(r+1) \bmod j} = b_{r+1}$, so the unique solution is $x_r = c - z_r$ (verified identically for $2 \le j \le 8$ and all $1 \le R \le 2^j - 2$ in `scripts/phase25_lambert_eplus.py`). Since $1 \le R \le 2^j - 2$, some bit $b_{r^* + 1} = 1$, forcing $z_{r^*} \ge \frac{2^{j-1}}{2^j - 1}$; combined with $x_{r^*} \ge 0$, this contradicts $c < \frac{2^{j-1}}{2^j - 1}$. $\square$

---

## 2. Track B2: Construction-Radix Discrepancy $D^-(F_{2^k}(a); 2^k) \to 1$

In Phase 24 (`GF-36` §4), radix descent and popcount-$\le 1$ blocks gave $D^-(E(2^k); 2^k) \to 0$ as $k \to \infty$ (e.g. only $\ge 0.00524$ at $k = 64$). Adapting the displaced odd-part method of `GF-31` (`notes/phase23/dense-characters-and-nonfundamental-forms.md` Theorem 4A) together with an exact $s$-moment integral discrepancy inequality completely reverses this behavior: $D^-(F_{2^k}(a); 2^k)$ tends to **$1$** at rate $O(\frac{\log k}{k})$.

### 2.1 Weighted residue law and exact $s$-moment integral bound

**Theorem B2.1 (Construction-radix discrepancy $D^-(F_{b^k}(a); b^k) \to 1$; Paper proof + Finite certificate; External input: Halász 1968).**
Let $b \ge 2$, $k \ge 1$, and $a(n) = b^{V(n)} U(n)$ ($U(n) \in \mathbb{Z}$, $b \nmid U(n)$ when $a(n) \ne 0$, $|a(n)| \ll_\varepsilon n^\varepsilon$) with $V$ additive, $V(p) = \alpha \in \mathbb{Z}_{\ge 1}$ for all $p > p_0$, $U$ depending only on prime powers (with $U(p) = 1$ for $p > p_0$), and $C_U(s) = \lim \frac{1}{X} \sum_{n \le X} |U(n)|^s < \infty$ ($0 < s \le 1$). Put $g = \gcd(\alpha, k)$. Then:

1. *(Weighted $s$-moment orbit bound.)* When $g = 1$ (including $E(2^k), E_{\rm odd}(2^k), E^*(2^k), E_+(2^k)$, $E_b^*(b^k)$ for all $b \ge 2$, and $\tau_p$ in prime base $p$), for every $s \in (0, 1]$,

```math
\limsup_{N \to \infty} \frac{1}{N} \sum_{j = 0}^{N - 1} \bigl\|b^{kj} F_{b^k}(a)\bigr\|^s \le \frac{C_U(s)}{k(b^s - 1)}.
```

   For general $g = \gcd(\alpha, k) \ge 1$ at $s = 1$, the bound holds with an extra coset factor $\frac{g\, b^{g-1}}{b^g - 1}$:

```math
\limsup_{N \to \infty} \frac{1}{N} \sum_{j = 0}^{N - 1} \bigl\|b^{kj} F_{b^k}(a)\bigr\| \le \frac{g\, b^{g-1}}{b^g - 1} \cdot \frac{C_U}{k}.
```

2. *(Exact $s$-moment integral discrepancy inequality.)* For every probability measure $\mu$ on $[0, 1)$ with extreme discrepancy $D = D(\mu)$ and every $s \in (0, 1]$,

```math
\int_0^1 \|t\|^s\, d\mu(t) \ge \frac{(1 - D)^{s + 1}}{2^s (s + 1)}.
```

3. *(Construction-radix $D^- \to 1$ at rate $O(\frac{\log k}{k})$.)* Consequently, when $g = 1$,

```math
1 - D^-\bigl(F_{b^k}(a); b^k\bigr) \le \inf_{0 < s \le 1} \left(\frac{2^s (s + 1)\, C_U(s)}{k(b^s - 1)}\right)^{1/(s + 1)} \ll_{a, b} \frac{\log k}{k} \longrightarrow 0 \qquad (k \to \infty),
```

   and for general $g \ge 1$ (with $g \mid \alpha$ bounded as $k \to \infty$), $1 - D^-(F_{b^k}(a); b^k) \le 2\sqrt{\frac{g b^{g-1} C_U}{k(b^g - 1)}} \to 0$. In particular, for $E_b^*(b^k)$ ($C_U = 1$ for every $b \ge 2$),

```math
D^-\bigl(E_b^*(b^k); b^k\bigr) \ge \max\!\left(0,\; 1 - \frac{2}{\sqrt{k(b - 1)}}\right) \longrightarrow 1.
```

*Proof.*
(1) Write $V(n) = k q_k(n) + r_k(n)$ ($0 \le r_k(n) < k$), $\ell_k(n) = n - q_k(n)$, and $W_k(n) = U(n) b^{r_k(n)}$, so $a(n) b^{-kn} = W_k(n) b^{-k \ell_k(n)}$ (verified in `scripts/phase25_lambert_eplus.py`). Using subadditivity $\|x + y\|^s \le \|x\|^s + \|y\|^s$ ($0 < s \le 1$) and omitting the integer terms $\ell_k(n) \le j$ gives $\|b^{kj} F_{b^k}(a)\|^s \le \sum_{\ell_k(n) > j} |U(n)|^s b^{-s(k(\ell_k(n) - j) - r_k(n))}$. Summing over $0 \le j < N$ and exchanging sums (noting that $\ell_k(n) \le N$ implies $n \le N + O(\log N)$, while terms with $\ell_k(n) > N$ contribute $O(N^\varepsilon) = o(N)$):

```math
\frac{1}{N} \sum_{j = 0}^{N - 1} \bigl\|b^{kj} F_{b^k}(a)\bigr\|^s
  \le \frac{1}{N} \sum_{n \le N} |U(n)|^s \frac{b^{-s(k - r_k(n))}}{1 - b^{-sk}} + o(1).
```

When $g = \gcd(\alpha, k) = 1$, for every $1 \le u < k$ the $y$-good squarefree-tail truncation of `GF-36` Lemma 3.2 reduces $\frac{1}{N} \sum_{n \le N} |U(n)|^s e(u V(n)/k) \to 0$ to Halász's theorem on 1-bounded multiplicative functions $\mathbf{1}_{\rm good}(r) e(u V(r)/k)$ (since $e(u \alpha / k) \ne 1$ at every prime $p > y$). Thus $u_n := k - r_k(n)$ equidistributes over $\{1, \ldots, k\}$ weighted by $|U(n)|^s$, giving limit

```math
C_U(s) \cdot \frac{1}{k(1 - b^{-sk})} \sum_{u = 1}^k b^{-su} = \frac{C_U(s)}{k(b^s - 1)}.
```

For general $g = \gcd(\alpha, k) \ge 1$ at $s = 1$, $V(r) \bmod k$ equidistributes on each coset $r_0 + g \mathbb{Z}/k\mathbb{Z}$, and the coset average of $b^{-(k - r)}/(1 - b^{-k})$ over $u = k - r \equiv u_0 \pmod g$ ($1 \le u_0 \le g$) is $\frac{g\, b^{g - u_0}}{k(b^g - 1)} \le \frac{g\, b^{g - 1}}{k(b^g - 1)}$ (maximal at $u_0 = 1$).

(2) By layer-cake integration and $\mu([u, 1 - u]) \ge (1 - 2u - D)_+$ for $0 < u < a := (1 - D)/2$,

```math
\int_0^1 \|t\|^s\, d\mu(t)
  = \int_0^{1/2} s u^{s - 1} \mu([u, 1 - u])\, du
  \ge \int_0^a s u^{s - 1}(2a - 2u)\, du
  = \frac{2}{s + 1} a^{s + 1} = \frac{(1 - D)^{s + 1}}{2^s (s + 1)}.
```

(3) Combine (1) and (2), using $\limsup (1 - D_N) = 1 - D^-$. Setting $s = 1/\log k$ ($k \ge 3$) with $C_U(s) \le C_U$ and $b^s - 1 \ge s \log b$ gives $1 - D^- \ll_{a, b} (\log k)/k \to 0$. $\square$

### 2.2 Certified construction-radix discrepancy table and direct base-32 simple nonnormality

The table below compares certified outward-rounded lower bounds on $D^-(F_{2^k}(a); 2^k)$ from Theorem B2.1 (best of $s = 1$ and $s = 1/2$, certified via exact rational `isqrt` and integer cube-root brackets in [`scripts/phase25_lambert_eplus.py`](../../scripts/phase25_lambert_eplus.py)) against Phase 24 (`GF-36` §4):

| $k$ | Phase 24 $E(2^k)$ | **B2 $E(2^k)$** ($s=1$, $s=\frac{1}{2}$) | **B2 $E_{\rm odd}(2^k)$** ($s=1$, $s=\frac{1}{2}$) | **B2 $E^*(2^k)$** ($s=1$, $s=\frac{1}{2}$) | **B2 $E_+(2^k)$** ($s=1$, $s=\frac{1}{2}$) |
| --- | --- | --- | --- | --- | --- |
| $5$ | $0.03744$ | — | — | **$0.1055$** ($s=1$) | **$0.0555$** ($0.0119$, $0.0555$) |
| $6$ | $0.04421$ | — | **$0.0330$** ($0.0330$, $0.0216$) | **$0.1835$** ($0.1835$, $0.1001$) | **$0.1636$** ($0.0980$, $0.1636$) |
| $8$ | $0.04218$ | **$0.1076$** ($0$, $0.1076$) | **$0.1923$** ($0.1625$, $0.1923$) | **$0.2928$** ($0.2928$, $0.2572$) | **$0.3096$** ($0.2188$, $0.3096$) |
| $10$ | $0.03552$ | **$0.2310$** ($0.0886$, $0.2310$) | **$0.3040$** ($0.2509$, $0.3040$) | **$0.3675$** ($0.3675$, $0.3598$) | **$0.4050$** ($0.3013$, $0.4050$) |
| $12$ | — | **$0.3190$** ($0.1680$, $0.3190$) | **$0.3836$** ($0.3162$, $0.3836$) | **$0.4331$** ($0.4226$, $0.4331$) | **$0.4731$** ($0.3622$, $0.4731$) |
| $16$ | $0.02201$ | **$0.4378$** ($0.2795$, $0.4378$) | **$0.4912$** ($0.4078$, $0.4912$) | **$0.5320$** ($0.5000$, $0.5320$) | **$0.5650$** ($0.4476$, $0.5650$) |
| $32$ | — | **$0.6458$** ($0.4905$, $0.6458$) | **$0.6794$** ($0.5812$, $0.6794$) | **$0.7052$** ($0.6464$, $0.7052$) | **$0.7260$** ($0.6094$, $0.7260$) |
| $64$ | $0.00524$ | **$0.7769$** ($0.6397$, $0.7769$) | **$0.7980$** ($0.7039$, $0.7980$) | **$0.8143$** ($0.7500$, $0.8143$) | **$0.8274$** ($0.7238$, $0.8274$) |

At $k = 64$, the certified lower bound on $D^-(E(2^{64}); 2^{64})$ improves Phase 24 by **$148\times$** ($0.7769$ vs $0.00524$).

**Corollary B2.2 (Direct construction-radix simple nonnormality via $s$-moments; Paper proof + Finite certificate; External input: Halász 1968).**
If $x$ is simply normal in base $B = 2^k$, then $\liminf_{N \to \infty} \frac{1}{N} \sum_{j < N} \|B^j x\|^s \ge \frac{1}{B} \sum_{d = 0}^{B - 1} \bigl(\frac{\min(d, B - 1 - d)}{B}\bigr)^s$ (at $s = 1$, this equals $\frac{1}{4} - \frac{1}{2B}$, kernel-verified in `GF-31`). Comparing with Theorem B2.1(1) at $s = 1$ certifies direct construction-radix simple nonnormality in base $2^k$ of $E_+(2^k)$ for every $k \ge 6$ (starting at $E_+(64)$ in base $64$), $E_{\rm odd}(2^k)$ for every $k \ge 6$, $E^*(2^k)$ for every $k \ge 5$, and $E(2^k)$ for every $k \ge 9$; at $s = 1/2$, it reaches **$E_+(32)$ in base $32$** directly ($\text{ub} \le 0.432658 < 0.447125 \le \text{unif}_{32}$). *(In §3.2 below, disjoint-block NAF transfer reaches $E_+(16)$ in base $16$ with zero external inputs.)*

---

## 3. Track B3: $E_+(8)$ Simple Normality Investigation, Exact Koksma Variation, Asymmetric 7-State Transducer, and Lean 4 Blueprint

In `GF-40` (`notes/phase24/classical-constants-and-joint-numerators.md` §3.2), the 4-state minimal-support NAF transducer established $D^-(E_+(8); 2) \ge 2.34 \times 10^{-7} > 0$, closing the $k = 3$ nonnormality gap for $E_+(2^k)$ while leaving base-2 simple normality of $E_+(8)$ open. Here we prove why no signed-digit transducer can settle base-2 simple normality, prove higher-base simple nonnormality of $E_+(2^k)$ (down to $E_+(16)$ in base $16$ and $E_+(8)$ in base $2^{13}$) with zero external inputs, sharpen $D^-(E_+(8); 2)$ by **$> 61\times$** via exact circular total variation and by **$> 101\times$** via an asymmetric 7-state transducer, and present a minimal DP-free Lean 4 formalization blueprint for Stage 3.

### 3.1 Universal transducer obstruction for base-2 simple normality

**Theorem B3.1 (Universal Transducer Obstruction; Paper proof + Finite certificate, zero external inputs; Objective 4).**
For **every** nonnegative cost pair $(c_+, c_-) \in \mathbb{R}_{\ge 0}^2$, there exists an explicit real number $x$ which is **simply normal in base $2$** ($f_{1, N}(x; 2) \to \frac{1}{2}$) while satisfying $\sigma_{c_+, c_-}(x; N) = O(\sqrt{N}) = o(N)$. Consequently, **no** upper bound on $\limsup_{N \to \infty} \sigma_{c_+, c_-}(x; N)/N$—not even $o(1)$—can rule out base-2 simple normality of $E_+(8)$ or any other real number.

*Proof.* Take Euler's pentagonal value $E_2 = \prod_{m \ge 1} (1 - 2^{-m}) = 1 + \sum_{j \ge 1} (-1)^j (2^{-j(3j-1)/2} + 2^{-j(3j+1)/2})$. By `GF-03`, $E_2 \in K_2$ is **simply normal in base $2$** (its binary digits consist of alternating long runs of $0$s and $1$s whose cumulative lengths balance to $1/2$). Yet the pentagonal expansion itself is a valid signed binary representation with at most $2\sqrt{2N/3} + 2$ nonzero digits in $[1, N]$ (checked explicitly up to $N = 4000$, where exactly $102$ nonzero fractional terms appear), so $\sigma_{c_+, c_-}(E_2; N) \le \max(c_+, c_-)(2\sqrt{2N/3} + 2) = O(\sqrt{N}) = o(N)$. $\square$

Thus **simple nonnormality of $E_+(8)$ in base $2$ remains Open** and requires a signed mechanism sensitive to the asymmetry between $0$-runs and $1$-runs (not merely the cost of transitions or signed-digit weight).

### 3.2 Higher-base simple nonnormality of $E_+(2^k)$ with zero external inputs

Although signed-digit cost cannot rule out base-2 simple normality, it **does** rule out simple normality in every base $2^L$ where the length-$L$ uniform word cost $A_L$ exceeds the series NAF rate!

**Theorem B3.2 (Disjoint-block simple nonnormality of $E_+(2^k)$; Paper proof + Finite certificate, zero external inputs).**
Let $x \in \mathbb{R}$ and $L \ge 1$. If $\limsup_{N \to \infty} \sigma_1(x; N)/N < A_L = \frac{1}{3} - \frac{7 - (-1/2)^{L-1}}{18 L}$, then **$x$ is simply nonnormal in base $2^L$** (and in every base $2^{mL}$, $m \ge 1$). Applying this with the certified bounds $W_+ \in [0.908078, 0.908260]$ and even the DP-free majorant $W_+^{\rm maj} \in [0.936405, 0.936453]$ (`scripts/phase25_lambert_eplus.py`):
1. **$E_+(2^k)$ is simply nonnormal in its construction radix $2^k$ for every $k \ge 4$** (in particular **$E_+(16)$ in base $16$**, certified even from the DP-free majorant since $W_+^{\rm maj} \le 0.936453 < \frac{15}{16} = 4 A_4$);
2. **$E_+(2^k)$ is simply nonnormal in base $8$ for every $k \ge 5$** ($W_+^{\rm maj}/5 \le 0.187291 < \frac{5}{24} = A_3$);
3. **$E_+(2^k)$ is simply nonnormal in base $4$ for every $k \ge 8$** ($W_+^{\rm maj}/8 \le 0.117057 < \frac{1}{8} = A_2$);
4. **$E_+(8)$ is simply nonnormal in base $2^L$ for every $L \ge 13$** ($W_+/3 \le 0.302754 < A_{13} = \frac{32313}{106496} \approx 0.303420$, in particular in base $8192 = 2^{13}$).

*Proof.* Partition $[1, LM]$ into $M$ disjoint length-$L$ blocks (the first $M$ base-$2^L$ digits of $x$). Restricting any optimal signed-digit path for $\sigma_1(x; LM)$ to each disjoint block $w^{(m)}$ costs at least $\sigma_{\rm free}(w^{(m)})$, so

```math
\frac{\sigma_1(x; LM)}{LM} \ge \frac{1}{L} \sum_{w \in \{0, 1\}^L} \sigma_{\rm free}(w)\, f_{w, M}(x; 2^L).
```

If $x$ were simply normal in base $2^L$, then $f_{w, M}(x; 2^L) \to 2^{-L}$ for every $w \in \{0, 1\}^L$, forcing $\liminf_{M \to \infty} \sigma_1(x; LM)/(LM) \ge \frac{1}{L \cdot 2^L} \sum_w \sigma_{\rm free}(w) = A_L$, contradicting $\limsup \sigma_1(x; N)/N < A_L$. Since $k A_k = \frac{k}{3} - \frac{7 - (-1/2)^{k-1}}{18}$ increases strictly for $k \ge 4$ with $4 A_4 = \frac{15}{16}$, and $A_L$ increases strictly for $L \ge 1$, the four inequalities certified by `scripts/phase25_lambert_eplus.py` yield (1)–(4). $\square$

### 3.3 Exact circular total variation of the 4-state automaton and $> 61\times$ discrepancy boost

In `GF-40` Theorem 3.2(b), bounding each of the $2^L$ dyadic cylinders separately gave $D^-(x; 2) \ge (A_L - \alpha)/(2^L A_L)$. Treating $g_L(t) = \sigma_{\rm free}(\lfloor 2^L t \rfloor)/L$ as a single piecewise-constant function on $\mathbb{R}/\mathbb{Z}$ and computing its **exact circular total variation** improves this by a factor of **$2L$** ($> 61\times$ at the re-optimized $L = 14$)!

**Theorem B3.3 (Exact Circular Variation & Discrete Circular Koksma Boost; Paper proof + Finite certificate, zero external inputs).**
1. *(Exact circular total variation of $\sigma_{\rm free}$.)* For every integer $L \ge 2$, indexing $\{0, 1\}^L$ lexicographically by $j \in \{0, \ldots, 2^L - 1\}$,

```math
V_{\rm circ}(\sigma_{\rm free}; L) := \sum_{j = 0}^{2^L - 1} \bigl|\sigma_{\rm free}(j + 1 \bmod 2^L) - \sigma_{\rm free}(j)\bigr|
  = \frac{2^L + 2(-1)^L}{3}.
```

   Every nonzero jump has magnitude $1$, with exactly $\frac{2^{L-1} + (-1)^L}{3}$ jumps of $+1$ and $\frac{2^{L-1} + (-1)^L}{3}$ jumps of $-1$.

2. *(Discrete circular Koksma inequality.)* Let $g : [0, 1) \to \mathbb{R}$ be constant on each dyadic interval $I_j = [j/2^L, (j+1)/2^L)$ with value $c_j$, average $\bar{g} = 2^{-L} \sum_j c_j$, and circular total variation $V_{\rm circ}(g) = \sum_{j=0}^{2^L - 1} |c_{j+1 \bmod 2^L} - c_j|$. For every probability measure $\mu_N$ on $[0, 1)$ with extreme discrepancy $D_N$,

```math
\left|\int_0^1 g\, d\mu_N - \bar{g}\right| \le \frac{V_{\rm circ}(g)}{2}\, D_N.
```

3. *(Sharpened 4-state discrepancy bound.)* Consequently, for every real $x$ with $\limsup_{N \to \infty} \sigma_1(x; N)/N \le \alpha < A_L$ ($L \ge 2$),

```math
D^-(x; 2) \ge \frac{6 L\, (A_L - \alpha)}{2^L + 2(-1)^L}.
```

   At $L = 14$ ($A_{14} = \frac{70087}{229376} \approx 0.30555507$, $V_{\rm circ}(\sigma_{\rm free}; 14) = 5462$) with certified $W_+ \in [0.908078, 0.908260]$, this certifies

```math
D^-(E_+(8); 2) \ge 1.4362 \times 10^{-5}
```

   — more than **$61\times$ sharper** than `GF-40`'s $2.34 \times 10^{-7}$.

*Proof.*
(1) Recall the minimal 4-state automaton $\{A, B, C, D\}$ of `GF-40` Theorem 3.2(a): $A$ (start) $\xrightarrow{0} (C, 0), \xrightarrow{1} (B, 0)$; $B \xrightarrow{0} (A, 1), \xrightarrow{1} (B, 0)$; $C \xrightarrow{0} (C, 0), \xrightarrow{1} (D, 0)$; $D \xrightarrow{0} (C, 1), \xrightarrow{1} (B, 1)$. For the wrap-around $j = 2^L - 1$, $\sigma_{\rm free}(0^L) = \sigma_{\rm free}(1^L) = 0$ (zero jump). For $0 \le j \le 2^L - 2$, write $j = u\, 0\, 1^t$ and $j + 1 = u\, 1\, 0^t$ with $t = v_2(j + 1) \in \{0, \ldots, L - 1\}$, and let $s \in \{A, B, C, D\}$ be the state after prefix $u$. Direct evaluation of $\Delta(s, t) := \mathrm{cost}(s, 1 0^t) - \mathrm{cost}(s, 0 1^t)$ across all four states gives:
- $t = 0$: $\Delta(B, 0) = 0 - 1 = -1$, and $\Delta(s, 0) = 0$ for $s \in \{A, C, D\}$;
- $t = 1$: $\Delta(B, 1) = 1 - 1 = 0$, and $\Delta(s, 1) = +1$ for $s \in \{A, C, D\}$ ($1 - 0$ from $A, C$; $2 - 1$ from $D$);
- $t \ge 2$: $\mathrm{cost}(s, 1 0^t) = \mathrm{cost}(s, 10) = \mathrm{cost}(s, 0 1^t)$ for every $s \in \{A, B, C, D\}$ (equal to $1$ from $A, B, C$ and $2$ from $D$), so **$\Delta(s, t) = 0$ identically for all $t \ge 2$**!

Using the exact Markov occupation probability $b_m = \frac{1}{3} + \frac{1}{6}(-\frac{1}{2})^{m-1}$ ($m \ge 1$, $b_0 = 0$) of state $B$ from `GF-40` Theorem 3.2(a): the $-1$ jumps occur at $t = 0$ with prefix in $B$, count $2^{L-1} b_{L-1} = \frac{2^{L-1} + (-1)^L}{3}$; the $+1$ jumps occur at $t = 1$ with prefix in $\{A, C, D\}$, count $2^{L-2}(1 - b_{L-2}) = \frac{2^{L-1} + (-1)^L}{3}$. Summing gives $V_{\rm circ}(\sigma_{\rm free}; L) = \frac{2^L + 2(-1)^L}{3}$ for every $L \ge 2$. *(Exhaustively verified in `scripts/phase25_lambert_eplus.py` for $2 \le L \le 15$.)*

(2) Put $t_j = j/2^L$ and $F(t) = \mu_N([0, t)) - t$ ($F(0) = F(1) = 0$). Since $D_N = \sup_t F(t) - \inf_t F(t)$, setting $M = \frac{1}{2}(\sup_t F(t) + \inf_t F(t))$ gives $|F(t) - M| \le D_N / 2$ for all $t \in [0, 1]$. Summing by parts using $\sum_j (c_j - c_{j+1 \bmod 2^L}) M = 0$ and $F(t_{2^L}) = F(t_0) = 0$:

```math
\int_0^1 g\, d\mu_N - \bar{g}
  = \sum_{j = 0}^{2^L - 1} c_j \bigl(F(t_{j+1}) - F(t_j)\bigr)
  = \sum_{j = 0}^{2^L - 1} \bigl(c_j - c_{j+1 \bmod 2^L}\bigr)\bigl(F(t_{j+1}) - M\bigr),
```

whose absolute value is at most $\frac{D_N}{2} \sum_j |c_{j+1 \bmod 2^L} - c_j| = \frac{V_{\rm circ}(g)}{2} D_N$. *(Checked on 200 rational empirical orbits in `scripts/phase25_lambert_eplus.py`.)*

(3) Applying (2) to $g_L(t) = \sigma_{\rm free}(\lfloor 2^L t \rfloor)/L$ (average $A_L$, circular variation $V_{\rm circ}(\sigma_{\rm free}; L)/L$) and $\frac{\sigma_1(x; N)}{N} \ge \int_0^1 g_L\, d\mu_N - \frac{L}{N}$ along a subsequence realizing $D^-(x; 2)$ gives $\alpha \ge A_L - \frac{V_{\rm circ}(\sigma_{\rm free}; L)}{2 L} D^-(x; 2)$, yielding the formula. $\square$

### 3.4 Minimal 7-state asymmetric $(1, 3/2)$ transducer and $> 101\times$ boost

Because $a_+(n) = +\tau_{\rm odd}(n) > 0$ on all odd $n$ (density $1/2$) while $a_+(n) < 0$ only on $4 \mid n$ (density $1/4$), penalizing negative signed digits by $\lambda > 1$ exploits the sign asymmetry of $E_+$.

**Theorem B3.4 (Minimal 7-state asymmetric $(1, 3/2)$ transducer; Paper proof + Finite certificate, zero external inputs).**
1. *(Algebraic submultiplicativity.)* For every $\lambda \ge 1$, $w_{1, \lambda}$ is subadditive, 2-scale invariant ($w_{1, \lambda}(2c) = w_{1, \lambda}(c)$), and **submultiplicative**: $w_{1, \lambda}(a b) \le w_{1, \lambda}(a) w_{1, \lambda}(b)$ for all $a, b \in \mathbb{Z}$. Moreover, $\limsup_{N \to \infty} \sigma_{1, \lambda}(E_+(2^k); N)/N \le \mu_{1, \lambda}(a_+)/k$, where $\mu_{1, \lambda}(a_+) = \lim_{X \to \infty} \frac{1}{X} \sum_{n \le X} w_{1, \lambda}(a_+(n))$.
2. *(Exact 7-state closure at $\lambda = 3/2$.)* At $(c_+, c_-) = (1, \frac{3}{2})$ (integer-scaled to $(2, 3)$), determinizing the 3-state carry DP closes at **13 reachable vectors** and Moore-minimizes to a **7-state deterministic automaton** with exact transition table (unscaled costs in parentheses):

| State $s$ | On bit `0`: (next, cost) | On bit `1`: (next, cost) | Stationary weight $\pi_s$ |
| --- | --- | --- | --- |
| `0` (start) | `(2, 0)` | `(3, 0)` | $5/62$ |
| `1` | `(2, 0)` | `(4, 0)` | $2/31$ |
| `2` | `(2, 0)` | `(5, 0)` | $11/31$ |
| `3` | `(1, 1)` | `(6, 0)` | $4/31$ |
| `4` | `(2, 1)` | `(6, 1/2)` | $1/31$ |
| `5` | `(2, 1)` | `(3, 1)` | $11/62$ |
| `6` | `(0, 3/2)` | `(6, 0)` | $5/31$ |

   Its exact stationary asymptotic rate is

```math
A_\infty(1, 3/2) = \frac{12}{31} \approx 0.387097,
```

   and at $L = 14$ its exact uniform average and circular variation are $A_{14}(1, 3/2) = \frac{80897}{229376} \approx 0.352683$ and $V_{\rm circ}(g_{14}^{(1, 3/2)}) = 453$ (an exact integer!). Moreover, because restricting an optimal free-boundary path on a concatenated word $w_1 w_2$ gives valid free-boundary paths on $w_1$ and $w_2$, $L A_L(1, 3/2) = \mathbb{E}[\sigma_{\rm free}^{(1, 3/2)}(W_L)]$ is superadditive in $L$; by Fekete's lemma and ergodicity of the irreducible aperiodic 7-state Markov chain (verified in the script along with strict monotonicity $A_1 < A_2 < \cdots < A_{14} < \frac{12}{31}$), $\sup_{L \ge 1} A_L(1, 3/2) = \lim_{L \to \infty} A_L(1, 3/2) = A_\infty(1, 3/2) = \frac{12}{31}$.
3. *(Certified $> 101\times$ boost for $E_+(8)$.)* Exact outward-rounded DP over $3 \le p \le 5000$ ($U \le 1024$) certifies $\mu_{1, 3/2}(a_+) \in [1.041775,\, 1.041984]$, giving via Theorem B3.3(2):

```math
D^-(E_+(8); 2) \ge \frac{A_{14}(1, 3/2) - \mu_{1, 3/2}^{\rm hi}/3}{453 / 2} \ge 2.3642 \times 10^{-5}
```

   — more than **$101\times$ sharper** than `GF-40`'s $2.34 \times 10^{-7}$!

*Proof.*
(1) Multiplying minimal representations of $a$ and $b$ produces signed powers of $2$ with sign-cost products $(+)(+) \mapsto 1 = 1\cdot 1$, $(+)(-) \mapsto \lambda = 1\cdot \lambda$, $(-)(+) \mapsto \lambda = \lambda \cdot 1$, and $(-)(-) \mapsto 1 \le \lambda^2$ (using $\lambda \ge 1$), proving submultiplicativity (verified exhaustively on $[-40, 40]^2$ in the script). Subadditivity and 2-scale invariance follow as for $w_\pm$. For the prefix bound on $E_+(2^k)$: take $N = k N_0$, $H = \lceil \frac{2}{k} \log_2(N_0 + 2) \rceil + 4$, $M = N_0 + H$, and let $S_M^+ = \sum_{j \ge 0} \eta_j 2^j$ ($\eta_j \in \{-1, 0, 1\}$) be a minimal $(1, \lambda)$-representation of $S_M^+$. Put $H_N = \sum_{j \ge kH} \eta_j 2^{j - kH} \in \mathbb{Z}$; then the low sum satisfies $|2^{-kH} \sum_{j < kH} \eta_j 2^j| < 1$, and the omitted series tail satisfies $|2^N \sum_{n > M} a_+(n) 2^{-kn}| < \frac{1}{4}$ (`GF-40` Theorem 3.1(c)). Thus $r = 2^N E_+(2^k) - H_N \in (-\frac{5}{4}, \frac{5}{4})$, so picking $c \in \{-1, 0, 1\}$ with $|r - c| < 1$ lets us write $r - c = \sum_{t \ge 1} \tilde{\eta}_t 2^{-t}$ ($\tilde{\eta}_t \in \{-1, 0, 1\}$), while $H_N + c$ has minimal $(1, \lambda)$-weight at most $w_{1, \lambda}(H_N) + w_{1, \lambda}(c) \le w_{1, \lambda}(S_M^+) + \lambda$. Retaining bits $0 \le j < N$ of a minimal representation of $H_N + c$ and appending $\tilde{\eta}_t$ exhibits an admissible representation showing $\sigma_{1, \lambda}(E_+(2^k); k N_0) \le w_{1, \lambda}(S_M^+) + \lambda \le \sum_{n=1}^M w_{1, \lambda}(a_+(n)) + \lambda$. Dividing by $N$ and letting $N \to \infty$ gives $\limsup \sigma_{1, \lambda}/N \le \mu_{1, \lambda}(a_+)/k$.

(2)–(3) Exact transition closure, Moore minimization, exact rational solution of $\pi P = \pi$, evaluation of $A_\infty = \frac{12}{31}$, $A_{14}$, $V_{\rm circ} = 453$, and outward-rounded DP certification of $\mu_{1, 3/2}(a_+)$ are verified in `scripts/phase25_lambert_eplus.py` (with overflow bounded rigorously by $w_{1, \lambda}(o_2 u) \le w_{1, \lambda}(o_2) s_2(u)$ for $u > 0$). $\square$

### 3.5 Lean 4 formalization blueprint for $E_+(2^k)$ ($k \ge 3$) (Stage 3 handoff)

*Status: uncompiled Lean 4 blueprint. Every underlying inequality and finite certificate is checked by [`scripts/phase25_lambert_eplus.py`](../../scripts/phase25_lambert_eplus.py).*

To formalize unconditional nonnormality and $D^-(E_+(2^k); 2) > 0$ for all $k \ge 3$ cleanly in Lean 4 on top of `NormalityChecker/DigitMassTransfer.lean` (`GF-36`), **two drastic simplifications** eliminate both infinite signed tails (`\sigma_1` gauge machinery) and the 5,000-prime DP:

**Lemma B3.5 (Exact Prefix-Boundary Simplification — Paper proof + Finite certificate, zero external inputs).**
For every $k \ge 1$ and $N_0 \ge 1$, put $N = k N_0$, $H = \lceil \frac{2}{k} \log_2(N_0 + 2) \rceil + 4$, $M = N_0 + H$, $S_M^+ = \sum_{n=1}^M a_+(n) 2^{k(M-n)}$, let $H_N = \sum_{j \ge kH} \epsilon_j 2^{j - kH}$ be the high NAF integer of $S_M^+$, and let $X_N = \lfloor 2^N E_+(2^k) \rfloor$. Then:

```math
H_N - X_N \in \{0, 1\}, \qquad w_\pm(X_N) \le w_\pm(S_M^+) + 1 \le \sum_{n=1}^M w_\pm(a_+(n)) + 1.
```

*Proof.* By `GF-40` Theorem 3.1(c), $|2^N E_+(2^k) - H_N| < \frac{1}{4} + \frac{2}{3} = \frac{11}{12}$, while $2^N E_+(2^k) - X_N \in [0, 1)$. Adding gives $H_N - X_N \in (-\frac{11}{12}, \frac{23}{12}) \cap \mathbb{Z} = \{0, 1\}$! Therefore $X_N = H_N$ or $X_N = H_N - 1$, giving $w_\pm(X_N) \le w_\pm(H_N) + 1 \le w_\pm(S_M^+) + 1$. *(Verified across all $250$ cases $k \in \{1..5\}$, $N_0 \in \{1..50\}$ in `scripts/phase25_lambert_eplus.py`.)* $\square$

**Consequence for Lean 4:** Because $X_N = \lfloor 2^N E_+(2^k) \rfloor$ is a plain integer whose low $N$ bits are the exact canonical digits $d_N, \ldots, d_1$ of $E_+(2^k)$, the 4-state transducer only needs to lower-bound the **integer NAF weight $w_\pm(X_N)$** directly from the word counts of $X_N$'s $N$ bits (zero infinite signed tails, zero carry-gauge equivalence classes!).

**Three DP-free certified majorant tiers (reusing `local_factor_digitSum_two` from `DigitMassTransfer.lean`):**
Because $w_\pm(a_+(n)) \le w_\pm(|1 - v_2(n)|) \prod_{p > 2} s_2(v_p(n) + 1)$ (`signedWeight_le_digitSum`), we reuse the existing Lean theorem `local_factor_digitSum_two` on odd primes with zero new DP:

| Lean Majorant Tier | Primes explicitly summed | Certified upper bound on $W_+^{\rm maj}$ | Optimal $L$ | Certified $D^-(E_+(8); 2) \ge$ | Bonus |
| --- | --- | --- | --- | --- | --- |
| **Tier 1 (Ultra-compact `s_2`)** | **10 odd primes** ($p \le 31$) | $\le 0.946830 < \frac{23671}{25000}$ | $L = 23$ | $1.3412 \times 10^{-8}$ *(from $\frac{23671}{25000}$: $1.3354 \times 10^{-8} \ge 13/10^9$)* | Shortest Lean proof! |
| **Tier 2 (Compact `s_2`)** | **34 odd primes** ($p \le 150$) | $\le 0.939378 < \frac{47}{50}$ | $L = 21$ | $1.0147 \times 10^{-7}$ *(from $\frac{47}{50}$: $8.9009 \times 10^{-8}$)* | Reuses `local_factor_digitSum_two` |
| **Tier 3 (DP-free NAF)** | **77 odd primes** ($p \le 400$) | $\le 0.937255 < \frac{15}{16} = 4 A_4$ | $L = 20$ | $1.6830 \times 10^{-7}$ *(from $\frac{15}{16}$: $1.5894 \times 10^{-7}$)* | Also proves $E_+(16)_{16}$ simply nonnormal! |

*(For reference, the full DP-free majorant $W_+^{\rm maj} \le 0.936453$ gives $D^-(E_+(8); 2) \ge 1.9891 \times 10^{-7}$ at its optimal window $L = 20$. At Tier 1, $\frac{23671}{25000} = 0.94684$ clears $13/10^9$ at both $L = 23$ and $L = 24$, where $1.3014 \times 10^{-8} \ge 13/10^9$.)*

**Blueprint Lean 4 declarations (for `NormalityChecker/SignedTransducer.lean`, uncompiled):**

```lean
-- 1. Four-state deterministic transducer (4 states: A, B, C, D)
inductive NafState : Type | A | B | C | D deriving DecidableEq, Fintype

def nafStep : NafState → Bool → NafState × ℕ
  | .A, false => (.C, 0) | .A, true => (.B, 0)
  | .B, false => (.A, 1) | .B, true => (.B, 0)
  | .C, false => (.C, 0) | .C, true => (.D, 0)
  | .D, false => (.C, 1) | .D, true => (.B, 1)

def nafRun (s : NafState) : List Bool → NafState × ℕ
  | [] => (s, 0)
  | b :: bs => let (s', c) := nafStep s b; let (s'', c') := nafRun s' bs; (s'', c + c')

def sigFree (w : List Bool) : ℕ := (nafRun .A w).2

def bitsOf (L j : ℕ) : List Bool :=
  (List.range L).map fun i => Nat.testBit j (L - 1 - i)

-- 2. Invariant connecting sigFree to signed-digit carry paths (δ ∈ {-1, 0, 1})
theorem sigFree_le_pathCost (w : List Bool) (δ : Fin (w.length + 1) → Int)
    (hδ : ∀ i, |δ i| ≤ 1)
    (hstep : ∀ i : Fin w.length, |(if w[i] then (1 : Int) else 0) + 2 * δ i.castSucc - δ i.succ| ≤ 1) :
    sigFree w ≤ (Finset.univ.filter fun i : Fin w.length =>
      (if w[i] then (1 : Int) else 0) + 2 * δ i.castSucc - δ i.succ ≠ 0).card

-- 3. Closed-form uniform average A_L (proved by induction on L via the 4-state Markov law)
theorem sum_sigFree_eq (L : ℕ) (hL : 1 ≤ L) :
    (∑ w : Fin L → Bool, (sigFree (List.ofFn w) : ℚ)) =
      (2 : ℚ) ^ L * ((L : ℚ) / 3 - (7 - (-1 / 2 : ℚ) ^ (L - 1)) / 18)

-- 4. Exact circular total variation (Theorem B3.3(1)) & discrete circular Koksma (Theorem B3.3(2))
theorem circVar_sigFree_eq (L : ℕ) (hL : 2 ≤ L) :
    (∑ j : Fin (2 ^ L), Int.natAbs ((sigFree (bitsOf L ((j.1 + 1) % 2 ^ L)) : Int) -
      (sigFree (bitsOf L j.1) : Int))) = (2 ^ L + 2 * (-1 : Int) ^ L).toNat / 3

-- 5. Exact prefix-boundary bound (Lemma B3.5) and DP-free majorant (reusing DigitMassTransfer.lean)
theorem signedWeight_floor_erdosBorweinPlus_le (k N₀ : ℕ) (hk : 1 ≤ k) (hN : 1 ≤ N₀) :
    let H := Nat.ceil ((2 : ℝ) / k * Real.logb 2 (N₀ + 2)) + 4
    signedWeight ⌊(2 : ℝ) ^ (k * N₀) * erdosBorweinPlus (2 ^ k)⌋ ≤
      (∑ n ∈ Finset.Icc 1 (N₀ + H), signedWeight (erdosBorweinPlusCoeff n)) + 1

theorem tsum_ePlusMajorant_lt_23671_div_25000 :
    ePlusMajorantMean < (23671 : ℝ) / 25000  -- Tier 1: 10 odd primes p ≤ 31 (certified ≤ 0.946830)

-- 6. Final kernel-verified target theorems (all k ≥ 3, zero external inputs; L = 23 gives ≥ 1.3354e-8 ≥ 13/10^9)
theorem erdosBorweinPlus_two_pow_lowerDiscrepancy_pos (k : ℕ) (hk : 3 ≤ k) :
    (13 : ℝ) / 10 ^ 9 ≤ lowerRadixDiscrepancy (erdosBorweinPlus (2 ^ k)) 2

theorem erdosBorweinPlus_two_pow_not_normal (k : ℕ) (hk : 3 ≤ k) :
    ¬ IsNormal (erdosBorweinPlus (2 ^ k)) 2
```

---

## 4. Track B4: The $E_+(4)$ Signed Carry Cancellation Frontier & Fixed-Window Barrier

### 4.1 Exact normalization and sharpened NAF cancellation threshold

For $E_+(4) = \sum_{n \ge 1} a_+(n) 4^{-n}$ ($k = 2$), define the exact finite NAF cancellation rate of the partial sum $S_M^+ = \sum_{n=1}^M a_+(n) 2^{2(M-n)}$:

```math
\bar{c}_2^{\rm NAF}(M) := \frac{1}{2 M} \left(\sum_{n=1}^M w_\pm(a_+(n)) - w_\pm(S_M^+)\right) \ge 0.
```

By Lemma B3.5 and Theorem B3.3(3), $\limsup_{N \to \infty} \sigma_1(E_+(4); N)/N + \liminf_{M \to \infty} \bar{c}_2^{\rm NAF}(M) \le \frac{W_+}{2}$. Since $A_L \nearrow \frac{1}{3}$, proving $D^-(E_+(4); 2) > 0$ via the 4-state NAF transducer is **implied** by the sufficient cancellation threshold

```math
\liminf_{M \to \infty} \bar{c}_2^{\rm NAF}(M) > \frac{W_+}{2} - \frac{1}{3} \in [0.120705,\, 0.120797] < 0.1208
```

(sharpening `GF-40`'s $0.1231$ using our tighter DP enclosure $W_+ \in [0.908078, 0.908260]$). Since $\sup_{L \ge 1} A_L(1, 3/2) = A_\infty(1, 3/2) = 12/31$ (by superadditivity and Fekete's lemma, §3.4), switching to the asymmetric $(1, 3/2)$ 7-state transducer reduces the **relative** deficit required from $\frac{W_+/2}{1/3} - 1 \le 0.36239$ to $\frac{\mu_{1,3/2}/2}{12/31} - 1 \le 0.34590$, but remains well short of zero cancellation.

### 4.2 Fixed-Window Cancellation Barrier and the finite-scale illusion

At first glance, grouping $S_M^+$ into fixed-size blocks of $B$ consecutive terms $\mathcal{B}_r = \sum_{j=1}^B a_+(Br + j) 2^{k(B-j)}$ ($0 \le r < \lfloor M/B \rfloor$) looks extraordinarily promising: opposite-sign terms ($n$ odd vs $4 \mid n$) collide at small shifts, and **every** same-column opposite-sign collision between odd integers $(U_1, U_2)$ saves at least $1$ in NAF weight ($w_\pm(U_1) + w_\pm(U_2) - w_\pm(U_1 - U_2) \ge 1$, verified exhaustively for all odd $1 \le U_1, U_2 \le 63$, with exact cancellation saving $2 w_\pm(U_1)$ when $U_1 = U_2$). Indeed, on finite prefixes up to $M = 2^{16}$, the $B = 8$ and $B = 16$ block cancellation rates **increase at the four sampled $M \in \{2^{10}, 2^{12}, 2^{14}, 2^{16}\}$** and exceed $0.1208$ cleanly!

The following theorem proves that this is a **pure finite-scale illusion**: every fixed-width block grouping has **zero asymptotic NAF cancellation**.

**Theorem B4.1 (Fixed-Window Cancellation Barrier; Paper proof + Finite certificate; External input: 2-D Fundamental Lemma; Objective 4).**
For every fixed integer $k \ge 1$ and every fixed block length $B \ge 1$, define the $B$-block NAF cancellation rate

```math
\bar{c}_{k, B}^{\rm block}(M) := \frac{1}{k B \lfloor M/B \rfloor} \sum_{r = 0}^{\lfloor M/B \rfloor - 1} \left(\sum_{j=1}^B w_\pm(a_+(Br + j)) - w_\pm(\mathcal{B}_r)\right) \ge 0.
```

Then for **every** fixed $B \ge 1$ and **every** fixed $k \ge 1$,

```math
\lim_{M \to \infty} \bar{c}_{k, B}^{\rm block}(M) = 0, \qquad
\text{quantitatively }\; \bar{c}_{k, B}^{\rm block}(M) = O_{k, B}\!\left(\frac{\sqrt{\log\log\log\log M}}{(\log\log M)^{1/8}}\right).
```

*Proof.* We first record **Separated-Support NAF Additivity (Lemma B4.2)**: if $X_i = s_i U_i 2^{L_i}$ ($s_i \in \{\pm 1\}$, $U_i \ge 1$ odd) satisfy $L_{i+1} \ge L_i + \lfloor \log_2 U_i \rfloor + 3$ for every $i$, then $w_\pm(\sum X_i) = \sum w_\pm(X_i)$ identically. Indeed, the canonical NAF of $s_i U_i$ is supported on $[0, \lfloor \log_2 U_i \rfloor + 1]$, so the shifted NAF supports $[L_i, L_i + \lfloor \log_2 U_i \rfloor + 1]$ are separated by at least one zero bit; concatenating them produces a valid NAF representation of $\sum X_i$, which by uniqueness and minimality of NAF (Reitwiesner 1960) is minimal. *(Verified across 400 random signed triples in `scripts/phase25_lambert_eplus.py`.)*

Now fix $k, B \ge 1$, put $L = \log\log M$, and choose $M$-dependent good-set parameters $\eta = L^{-1/4}$, $p_1 = \lceil L^{1/2} \rceil$, $K_0 = \lceil L^{1/4} \rceil$, and $T = \lceil L^{1/2} \rceil$. Call a block $r < R := \lfloor M/B \rfloor$ *bad* if some $n_j = Br + j$ ($1 \le j \le B$) violates $p^2 \nmid n_j$ ($\forall p > p_1$), $V_{\le p_1}(n_j) \le K_0$, $u(n_j) \le M^{1/8}$, or $|U_+(n_j)| \le T$. The individual exception probabilities are bounded by:
- $\sum_{p > p_1} p^{-2} \ll L^{-1/2}$;
- $\Pr(V_{\le p_1} > K_0) \ll \frac{\log\log p_1}{K_0} \ll \frac{\log\log L}{L^{1/4}}$;
- $\Pr(u(n) > M^{1/8}) \le 8\eta = 8 L^{-1/4}$ (elementary Markov on $\log u(n)$);
- $\Pr(|U_+(n)| > T) \le \mathbb{E}[U_+^2]/T^2 \ll L^{-1}$.

By Cauchy–Schwarz and $\mathbb{E}[w_\pm(a_+)^2] \le \mathbb{E}[U_+^2] < \infty$, the total cancellation contributed by all bad blocks is at most $O_{k, B}\bigl(\sqrt{(\log\log L)/L^{1/4}}\bigr) = O_{k, B}((\log\log\log\log M)^{1/2}/(\log\log M)^{1/8})$ (which is also $\le O_{k, B}((\log\log\log M)^{1/2}/(\log\log M)^{1/8})$).

For any **good** block $r$, every nonzero summand $a_+(n_j) 2^{k(B-j)} = s_j |U_+(n_j)| 2^{L_j}$ has $L_j = V_+(n_j) + k(B - j)$ and $\lfloor \log_2 |U_+(n_j)| \rfloor \le \frac{1}{2} \log_2 L$. By Lemma B4.2, the block has nonzero cancellation **only if** some pair $1 \le i < j \le B$ ($d = j - i \in [1, B - 1]$) has $|V_+(n_j) - V_+(n_i) - kd| \le \frac{1}{2} \log_2 L + 2$. On good blocks, $V_+(n_j) - V_+(n_i)$ differs from $\omega_{\mathcal{P}_d}(n_j) - \omega_{\mathcal{P}_d}(n_i)$ by at most $B_0 = K_0 + \lfloor 1/\eta \rfloor \le 2 L^{1/4}$, so $|\omega_{\mathcal{P}_d}(n_j) - \omega_{\mathcal{P}_d}(n_i) - kd| \le W := k B + 2 L^{1/4} + \log_2 L + 2$. Applying the 2-D Fundamental Lemma (Step 3 of Theorem B1.3, now with $s = \frac{3}{8\eta} = \frac{3}{8} L^{1/4} \to \infty$) and the Fourier bound $\Pr(S_d = h) \ll L^{-1/2}$ bounds the fraction of colliding good blocks by $\binom{B}{2} \cdot O(W / \sqrt{L}) = O_{k, B}(L^{-1/4})$. Since each good block has $\sum_{j=1}^B w_\pm(a_+(n_j)) \ll_B \log L$, the good-block cancellation contribution is $O_{k, B}((\log L)/L^{1/4})$. Combining both bounds completes the proof. $\square$

**Why `GF-40` two-point correlations cannot close $E_+(4)$.**
`GF-40` Theorem 3.3 proved unconditionally (via Topacogullari 2017) that $C_+(h; X) = \frac{1}{X} \sum_{n \le X} a_+(n) a_+(n+h) \sim \rho(h) \frac{6}{\pi^2} \sigma_{-1}(h) \log^2 X$ for every fixed shift $h \ge 1$. That archimedean correlation is dominated by the rare large-$V_+$ integers ($V_+(n) \approx 2\log\log X$) and measures products at **fixed** shifts $h = O(1)$, whereas Theorem B4.1 proves that all fixed-shift block cancellations vanish asymptotically! Any positive lower bound on $\liminf \bar{c}_2^{\rm NAF}$ must capture column collisions $V_+(n+h) - V_+(n) = 2h + O(1)$ summed over **growing shifts $h \asymp \sqrt{\log\log M}$**. *(Heuristic comparison: unlike Theorem B1.3—where the upper-bound side on collisions is unobstructed and closes unconditionally via the 2-D Fundamental Lemma—what is missing here is a **lower bound** on growing-shift bivariate collisions, paralleling the open collision lower-bound barrier for $E^*(4)$ in `GF-36` §10.)*

### 4.3 Finite measurements only (strictly separated; never asymptotic evidence)

The following two tables from [`scripts/phase25_lambert_eplus.py`](../../scripts/phase25_lambert_eplus.py) (`[finite]`) illustrate the Theorem B4.1 finite-scale illusion and record certified 12,000-bit prefix statistics of $E_+(2^k)$. They prove nothing about limiting behavior.

**Table 4.1 (`[finite]`): $E_+(4)$ fixed-block NAF cancellation $\bar{c}_{2, B}^{\rm block}(M)$ (rises above $0.1208$ through $M = 2^{16}$, yet provably $\to 0$ as $M \to \infty$ by Theorem B4.1):**

| Block width $B$ | $M = 1024$ | $M = 4096$ | $M = 16384$ | $M = 65536$ | True limit ($M \to \infty$, Thm. B4.1) |
| --- | --- | --- | --- | --- | --- |
| $B = 1$ | $0.00000$ | $0.00000$ | $0.00000$ | $0.00000$ | $0$ |
| $B = 2$ | $0.10156$ | $0.10608$ | $0.10962$ | $0.11025$ | $0$ |
| $B = 4$ | $0.10254$ | $0.10742$ | $0.11093$ | $0.11207$ | $0$ |
| $B = 8$ | $0.13867$ | $0.14392$ | $0.14603$ | $0.14735$ | **$0$** *(illusion $> 0.1208$!)* |
| $B = 16$ | $0.14404$ | $0.14929$ | $0.15204$ | $0.15390$ | **$0$** *(illusion $> 0.1208$!)* |

**Table 4.2 (`[finite]`): Certified 12,000-bit prefix frequencies of $E_+(2^k)$ in base $2$:**

| $k$ | $1$ ($E_+(2)$) | $2$ ($E_+(4)$) | $3$ ($E_+(8)$) | $4$ ($E_+(16)$) | $5$ ($E_+(32)$) | $6$ ($E_+(64)$) | $8$ ($E_+(256)$) |
| --- | --- | --- | --- | --- | --- | --- | --- |
| $f_{1, 12000}$ | $0.49400$ | $0.40000$ | $0.33325$ | $0.30558$ | $0.29517$ | $0.28800$ | $0.27917$ |
| $\mathrm{tr}_{12000}/11999$ | $0.50629$ | $0.43529$ | $0.37103$ | $0.30753$ | $0.24802$ | $0.20618$ | $0.15501$ |

---

## 5. Track B5: Broader Lambert Classifications (Strictly Respecting Senge–Straus)

### 5.1 Higher divisor functions $\tau_{2^m}$ (base 2), prime-base $\tau_p$, and unitary $E_b^*(b^k)$

**Theorem B5.1 (Higher-divisor and prime-base displaced classifications; Paper proof + Finite certificate; External inputs: 2-D Fundamental Lemma, Halász 1968, and Senge–Straus 1973 for barrier).**
1. *(Certified odd-part / $b$-stripped means.)* For $F_{2^k}(\tau_{2^m})$ ($b = 2$, $V(p) = m$) and prime-base $F_{p^k}(\tau_p)$ ($b = p$, $V(q) = 1$ for all primes $q$), the $b$-stripped mean $C_U = \prod_q (1 - \frac{1}{q}) \sum_{e \ge 0} u_b\bigl(\binom{e+r-1}{r-1}\bigr) q^{-e}$ is finite, with certified outward-rounded enclosures (`scripts/phase25_lambert_eplus.py`):

| Family | Base $b$ | Certified $C_U$ (`[encl]`) | $D^- > 0$ (`GF-36`) | **$D^+ < 1$ & $\notin K_b$ (Thm. B1.3)** | **Full $0 < D^- \le D^+ < 1$** | **$D^-(\cdot; b^k) \to 1$ (Thm. B2.1)** |
| --- | --- | --- | --- | --- | --- | --- |
| $F_{2^k}(\tau_4)$ | $2$ | $[9.42224,\, 9.43286]$ | $k \ge 4$ | **$k \ge 10$** | **$k \ge 10$** | Yes (coset $g = \gcd(2, k)$) |
| $F_{2^k}(\tau_8)$ | $2$ | $[440.50019,\, 444.39685]$ | $k \ge 4$ | **$k \ge 445$** | **$k \ge 445$** | Yes (coset $g = \gcd(3, k)$) |
| $F_{3^k}(\tau_3)$ | $3$ | $[3.65171,\, 3.65400]$ | $k \ge 2$ | **$k \ge 4$** | **$k \ge 4$** | Yes ($g = 1$) |
| $F_{5^k}(\tau_5)$ | $5$ | $[13.51915,\, 13.54287]$ | $k \ge 2$ | **$k \ge 14$** | **$k \ge 14$** | Yes ($g = 1$) |
| $F_{7^k}(\tau_7)$ | $7$ | $[66.18231,\, 66.48186]$ | $k \ge 1$ | **$k \ge 67$** | **$k \ge 67$** | Yes ($g = 1$) |
| $E_b^*(b^k)$ ($\forall b \ge 2$) | $b$ | $1$ (exact) | $k \ge 1$ ($b \ge 4$), $k \ge 2$ ($b = 3$), $k \ge 3$ ($b = 2$) | **$k \ge 2$** | $b \ge 3, k \ge 2$; $b = 2, k \ge 3$ | Yes ($D^- \ge 1 - \frac{2}{\sqrt{k(b-1)}}$) |

2. *(Senge–Straus / multiplicative-independence boundary.)* Whenever $r \ge 2$ and $b \ge 2$ are **multiplicatively independent** ($\log r / \log b \notin \mathbb{Q}$), **both** digit-mass transfer ($\frac{1}{X} \sum_{n \le X} w_b(\tau_r(n)) \to \infty$, `GF-36` Theorem 6.2 via Senge–Straus) **and** displaced-unit transfer ($\frac{1}{X} \sum_{n \le X} u_b(\tau_r(n)) \to \infty$, directly from $u_b(a) \ge w_b(a)$—or elementarily without Senge–Straus since $u_b(r^{\omega(n)}) \ge q^{c \omega(n)}$ for some prime $q \mid r$ with $v_q(r)/v_q(b) > \min_{p \mid b} v_p(r)/v_p(b)$) diverge identically. Thus $E(9)_3, E(25)_5, E(100)_{10}$ remain completely outside both methods and **Open**.

*Proof.* For each prime $q$, the tail $(1 - \frac{1}{q}) \sum_{e \ge E} \binom{e+r-1}{r-1} q^{-e} = (1 - \frac{1}{q})^{-(r-1)} - (1 - \frac{1}{q}) \sum_{e < E} \binom{e+r-1}{r-1} q^{-e}$ is exact, and for $q > P > 2r$ the local excess satisfies $L_q - 1 \le \bigl(r - 1 + \binom{r}{2}(1 - \frac{r}{2P})^{-1}\bigr) q^{-2}$ (since $\binom{e+r-2}{r-2}/\binom{e+r-3}{r-2} = \frac{e+r-2}{e} \le \frac{r}{2}$ for all $e \ge 2$). Applying Theorems B1.3 and B2.1 gives every column of the table. $\square$

### 5.2 Fermat-power-of-two moduli ($\varphi(M) = 2^t$): extending `GF-07` beyond $M \mid 24$

In `GF-07`, residue-class Lambert transfers $2^t A_{r, M} \equiv E^{(M)} \pmod{K_b}$ were established when $(\mathbb{Z}/M\mathbb{Z})^\times$ is 2-elementary ($M \mid 24$). Combining `GF-13` (which places **every** even-order character Lambert series—not just quadratic ones!—into $K_b$) with our Theorems B1.3, B1.5, and B2.1 extends this classification to **every Fermat-product modulus**.

**Theorem B5.2 (Fermat-power-of-two residue-class Lambert classification; Paper proof + Finite certificate; External inputs: `GF-13` [Wirsing / Selberg–Delange], 2-D Fundamental Lemma, Halász 1968).**
Let $M \ge 2$ satisfy $\varphi(M) = 2^t$ (equivalently $M = 2^a \prod F_i$ for distinct Fermat primes $F_i \in \{3, 5, 17, 257, 65537, \ldots\}$; complete list for $2 \le M \le 257$: $M \in \{2, 3, 4, 5, 6, 8, 10, 12, 15, 16, 17, 20, 24, 30, 32, 34, 40, 48, 51, 60, 64, 68, 80, 85, 96, 102, 120, 128, 136, 160, 170, 192, 204, 240, 255, 256, 257\}$, asserted exactly in the script), and let $\gcd(r, M) = 1$. Then:

1. For every integer $k \ge 1$, $2^t A_{r, M}(2^k) - E^{(M)}(2^k) \in K_2 \cap K_{2^k}$ with $1 - D_N \ll (\log\log N)/(\log N)^{1/\lambda(M)}$ (verified algebraically for $M = 5$ in `scripts/phase25_lambert_eplus.py`: $4 \delta_r(u) = 1 + \chi_2(r)\chi_2(u) + 2\Re(\overline{\chi_4(r)}\chi_4(u))$).
2. *(Exact base-2 identity of $D^\pm$ and direct simple nonnormality.)* $D^\pm(A_{r, M}(2^k); 2) = D^\pm(E^{(M)}(2^k); 2)$ for every $k \ge 1$. Consequently:
   - for **every $k \ge 3$**, $0 < D^-(A_{r, M}(2^k); 2) \le D^+(A_{r, M}(2^k); 2) < 1$ and $A_{r, M}(2^k) \notin K_2$; moreover, by direct dense digit-mass transfer on $A_{r, M}(2^k) = \sum_{n \ge 1} \tau_{r, M}(n) 2^{-kn}$, $\limsup_{N \to \infty} f_{1, N}(A_{r, M}(2^k); 2) \le C_{\rm true}^{(M)}/k \le C/k < \frac{29}{20 k} < \frac{1}{2}$, so **$A_{r, M}(2^k)$ is simply nonnormal in base $2$ and in every base $2^j$ ($j \ge 1$)**;
   - at **$k = 2$** ($A_{r, M}(4)$), **$D^+(A_{r, M}(4); 2) < 1$ and $A_{r, M}(4) \notin K_2$** for $M = 3$ ($C_U^{(3)} \le 1.740302 < 2$), $M = 5$ ($C_U^{(5)} \le 1.940647 < 2$), and **every even Fermat-product modulus $M$** ($C_U^{(M)} \le C_{U, \rm odd} \le 1.402514 < 2$)!
3. *(Full construction-radix limit.)* For every Fermat-product $M$ and every $\gcd(r, M) = 1$, **$\lim_{k \to \infty} D^-(A_{r, M}(2^k); 2^k) = 1$** at rate $O(\frac{\log k}{k})$.

*Proof.* Since $(\mathbb{Z}/M\mathbb{Z})^\times$ is a 2-group of order $2^t$, every nonprincipal character $\chi \bmod M$ has even order $2^s \ge 2$. Character orthogonality gives $2^t A_{r, M}(2^k) - E^{(M)}(2^k) = \sum_{\chi \ne \chi_0} \overline{\chi(r)} L_\chi(2^k)$, an integer-valued linear combination of even-order character Lambert series, which lies in $K_2 \cap K_{2^k}$ and preserves discrepancy in every base $b \ge 2$ by `GF-13` (together with `GF-01` and `GF-23` for $M_2 = M_{2^k} \subseteq K_{2^k}$). Multiplying by $2^t$ is a pure $t$-bit shift in base $2$, so $D^\pm(A_{r, M}(2^k); 2) = D^\pm(E^{(M)}(2^k); 2)$, transferring `GF-36` ($D^- > 0$ for $k \ge 3$) and Theorem B1.3 ($D^+ < 1$ for $k > C_U^{(M)}$).

Since translation by an element of $K_2$ does not in general preserve binary digit frequencies, we prove simple nonnormality for $k \ge 3$ directly via dense digit-mass transfer (`GF-36` Corollary 2.3 and Proposition 2.4(5)) on the nonnegative series $A_{r, M}(2^k) = \sum_{n \ge 1} \tau_{r, M}(n) 2^{-kn}$, where $\tau_{r, M}(n) = \#\{d \mid n : d \equiv r \pmod M\}$ satisfies $0 \le \tau_{r, M}(n) \le \tau(n) \le 2\sqrt{n}$. By character orthogonality, $2^t \tau_{r, M}(n) = \tau^{(M)}(n) + \sum_{\chi \ne \chi_0} \overline{\chi(r)} (1 * \chi)(n)$. Letting $\mathcal{E}_M := \{n \ge 1 : \exists \chi \ne \chi_0 \bmod M \text{ with } (1 * \chi)(n) \ne 0\}$, `GF-13` gives $|\mathcal{E}_M \cap [1, X]| \ll_M X / (\log X)^{1/2^t} = o(X)$. For every $n \notin \mathcal{E}_M$, $2^t \tau_{r, M}(n) = \tau^{(M)}(n)$ holds identically, so 2-scale invariance of binary popcount yields $s_2(\tau_{r, M}(n)) = s_2(\tau^{(M)}(n))$ (verified for $M = 5$ through $n \le 1000$ in `scripts/phase25_lambert_eplus.py`). On $\mathcal{E}_M$, both $\tau_{r, M}(n)$ and $\tau^{(M)}(n)$ are at most $\tau(n)$, so $s_2(\tau_{r, M}(n)) \le \log_2(\tau(n) + 1) + 1 \le \Omega(n) + 2$, where $\Omega(n) = \sum_{p^a \mid n} 1$ satisfies the elementary bound $\sum_{n \le X} (\Omega(n) + 2)^2 \ll X(\log\log X)^2$. By Cauchy–Schwarz, the exceptional set $\mathcal{E}_M$ contributes at most $\ll_M (\log\log X)/(\log X)^{1/2^{t+1}} \to 0$ to the mean of $s_2(\tau_{r, M}(n))$ (and likewise to $s_2(\tau^{(M)}(n))$). Therefore

```math
\lim_{X \to \infty} \frac{1}{X} \sum_{n \le X} s_2\bigl(\tau_{r, M}(n)\bigr)
  = \lim_{X \to \infty} \frac{1}{X} \sum_{n \le X} s_2\bigl(\tau^{(M)}(n)\bigr)
  =: C_{\rm true}^{(M)}
  \le \prod_{p \nmid M} L_p^{\rm pop}
  \le \prod_{p} L_p^{\rm pop} = C < \frac{29}{20},
```

using `GF-36` Lemma 3.2 and the fact that every local popcount factor $L_p^{\rm pop} = \sum_{j \ge 0} \frac{p}{p^{2^j} + 1} > 1$ (`GF-36` `DigitMassTransfer.lean`). Dense digit-mass transfer (`GF-36` Corollary 2.3) immediately gives $\limsup_{N \to \infty} f_{1, N}(A_{r, M}(2^k); 2) \le C_{\rm true}^{(M)}/k < \frac{29}{20 k} < \frac{1}{2}$ for every $k \ge 3$, establishing simple nonnormality in base $2$, and hence in every base $2^j$ ($j \ge 1$) by radix descent (`GF-36` Proposition 2.4(5)).

For base $2^k$, write $t = k q + r_0$ ($0 \le r_0 < k$) and multiply by $2^{k - r_0}$: $2^{k(q+1)} A_{r, M}(2^k) = 2^{k - r_0} E^{(M)}(2^k) + 2^{k - r_0} Z$ with $2^{k - r_0} Z \in K_{2^k}$. Shifting $V(n) \mapsto V(n) + (k - r_0)$ leaves the uniform distribution of $V(n) \bmod k$ invariant, so Theorem B2.1 gives $1 - D^-(A_{r, M}(2^k); 2^k) = 1 - D^-(2^{k - r_0} E^{(M)}(2^k); 2^k) \ll (\log k)/k \to 0$. $\square$

### 5.3 General periodic integer weights with $\operatorname{odd}(\lambda(M)) \mid 3$ and compatible $\mathbb{Z}$-linear combinations

**Theorem B5.3 (Periodic integer weights with $\operatorname{odd}(\lambda(M)) \mid 3$; Paper proof + Finite certificate; External inputs: `GF-13`, Halász 1968).**
Let $M \ge 1$ be any modulus whose Carmichael exponent satisfies **$\operatorname{odd}(\lambda(M)) \mid 3$** (so every Dirichlet character modulo every divisor of $M$ has order $1$, $3$, or even; the complete set of all $50$ such moduli $M \le 100$ is $\{1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 13, 14, 15, 16, 17, 18, 20, 21, 24, 26, 28, 30, 32, 34, 35, 36, 39, 40, 42, 45, 48, 51, 52, 56, 60, 63, 64, 65, 68, 70, 72, 78, 80, 84, 85, 90, 91, 96, 97\}$, asserted for exact equality in the script, with first excluded moduli $11, 19, 22, 23, 25, 27, 29, 31$). Let $w : \mathbb{N} \to \mathbb{Z}$ be any $M$-periodic integer weight, set $D_M = 2 \varphi(M) = 2^a D_{\rm odd}$ ($D_{\rm odd}$ odd), and put $F_{2^k}(1 * w) = \sum_{m \ge 1} w(m)/(2^{km} - 1)$. Then:

1. *(Exact integer decomposition modulo $K_2 \cap K_{2^k}$.)* $D_M F_{2^k}(1 * w) = Y_w(2^k) + Z_w(2^k)$, where $Z_w(2^k) \in K_2 \cap K_{2^k}$ (`GF-13`) and $Y_w(2^k)$ is an explicit $\mathbb{Z}$-linear combination of dilated principal series $E^{(M/g)}(2^{kg})$ and cubic character projections $L_{\pm, \chi}(2^{kg})$ ($g \mid M$).
2. *(Nonnormality in base $2$ and base $2^k$.)* Putting $W_{\rm eff}(w) = \limsup \frac{1}{X} \sum_{n \le X} w_\pm(y_w(n)) < \infty$ (where $y_w$ are the coefficients of $Y_w$): for every $k > 3 W_{\rm eff}(w)$,

```math
D^-\bigl(F_{2^k}(1 * w); 2\bigr) \ge \frac{1}{D_{\rm odd}}\, D^-\bigl(Y_w(2^k); 2\bigr) > 0, \qquad
\liminf_{k \to \infty} D^-\bigl(F_{2^k}(1 * w); 2^k\bigr) \ge \frac{1}{D_{\rm odd}} > 0
```

   (with $\lim_{k \to \infty} D^-(F_{2^k}(1 * w); 2^k) = 1$ whenever $D_{\rm odd} = 1$, or whenever $w$ is given directly as a $\mathbb{Z}$-combination of principal, cubic $c_\pm$, and even-order weights without clearing odd denominators).

*Proof.* Partition $m$ by $g = \gcd(m, M) \mid M$, writing $m = g m'$ with $\gcd(m', M') = 1$ ($M' = M/g$ also satisfies $\operatorname{odd}(\lambda(M')) \mid 3$). Expanding $w(g m')$ in characters $\chi \bmod M'$: all even-order characters have $L_\chi \in K_2 \cap K_{2^k}$ (`GF-13`), while for each conjugate cubic pair $(\chi, \bar\chi)$ with coefficient $c_\chi = A + B\omega \in \mathbb{Z}[\omega]$ and $1 * \chi = x + y\omega$, the exact algebraic trace identity

```math
2 \cdot 2\Re\bigl((A + B\omega)(x + y\omega)\bigr) = (2A - B)\, c_+ - 3B\, c_- \qquad (c_+ = 2x - y,\ c_- = y)
```

(verified across all $9^4 = 6{,}561$ tuples in `scripts/phase25_lambert_eplus.py`, together with the full mod-7 orthogonal basis reconstruction of $12 \delta_r$) clears denominators upon multiplying by $D_M = 2 \varphi(M)$. Thus $D_M F_{2^k}(1 * w) = Y_w(2^k) + Z_w(2^k)$ with $Z_w \in K_2 \cap K_{2^k}$. If $Y_w \equiv 0$, then $F_{2^k}(1 * w) \in K_2 \cap K_{2^k}$ directly (`GF-13`, $D^- = 1$). Otherwise, `GF-13` (together with `GF-01` for $K_b$ discrepancy preservation in every radix $b \ge 2$ and `GF-23` for $M_2 = M_{2^k}$) gives $D^\pm(D_M F_{2^k}(1 * w); 2) = D^\pm(Y_w(2^k); 2)$ and $D^\pm(2^{k - r_0} D_M F_{2^k}(1 * w); 2^k) = D^\pm(2^{k - r_0} Y_w(2^k); 2^k)$. Using $D_N(m x; B) \le m D_N(x; B)$ for $m = D_{\rm odd}$ (note that the factor $1/D_{\rm odd}$ cannot be dropped in general, as shown by $x = 1/3, D_{\rm odd} = 3$ where $D_\infty(3x; 2) = 1$ while $D_\infty(1/3; 2) = 2/3$) and applying Theorem B3.3(3) (in base 2) and Theorem B2.1 (in base $2^k$) completes the proof. $\square$

**Corollary B5.4 (Compatible $\mathbb{Z}$-linear combinations; Paper proof; External input: Halász 1968 for base-$2^k$ part).**
Let $X_k = \sum_{i=1}^r c_i F_{2^k}(a_i)$ ($c_i \in \mathbb{Z}$) be any fixed $\mathbb{Z}$-linear combination of series from our bounded-NAF / bounded-$C_U$ families ($\tau, \tau_{\rm odd}, 2^\omega, a_+, \tau_{2^m}, c_{\pm, \chi}$, and even-order character series). Put $W_{\rm comb} = \sum_{i=1}^r w_\pm(c_i) W(a_i)$ and $C_{\rm comb}(s) = \sum_{i=1}^r |c_i|^s C_U(a_i; s)$ (and at $s = 1$, $C_{\rm comb}^{\rm coset}(1) := \sum_{i=1}^r \frac{g_i 2^{g_i - 1}}{2^{g_i} - 1} |c_i| C_U(a_i; 1)$ with $g_i = \gcd(\alpha_i, k)$, which equals $C_{\rm comb}(1)$ whenever every summand has $g_i = 1$). Then:
1. *(Zero external inputs.)* For every $k > 3 W_{\rm comb}$, $D^-(X_k; 2) > 0$ (and $X_k$ is nonnormal in every base $2^j$, simply nonnormal in base $2^L$ once $W_{\rm comb}/k < A_L$, with $\lim_{k \to \infty} D^-(X_k; 2) = 1$).
2. *(Construction radix, via Halász.)* $\lim_{k \to \infty} D^-(X_k; 2^k) = 1$ at rate $O(\frac{\log k}{k})$ (with coset factor if any $\tau_{2^m}$ with $m \ge 2$ appears), and $X_k$ is directly simply nonnormal in base $2^k$ whenever $\frac{C_{\rm comb}^{\rm coset}(1)}{k} < \frac{1}{4} - \frac{1}{2^{k + 1}}$ (with no $1/D_{\rm odd}$ loss).

*Proof.* Subadditivity and submultiplicativity of $w_\pm$ give $\limsup_{N \to \infty} \sigma_1(X_k; N)/N \le \alpha_k := W_{\rm comb}/k$, yielding $D^-(X_k; 2) > 0$ for $k > 3 W_{\rm comb}$ via Theorem B3.3(3) and base-$2^L$ simple nonnormality via Theorem B3.2. To deduce $\lim_{k \to \infty} D^-(X_k; 2) = 1$, fix any integer $r \ge 2$: in any admissible signed binary representation of $X_k$ achieving $\sigma_1(X_k; N + r)$, each nonzero signed digit in $[1, N + r]$ falls in at most $r$ length-$r$ windows $(n+1, \ldots, n+r]$ ($0 \le n < N$). Whenever a window $(n+1, \ldots, n+r]$ contains only zeros, $|\sum_{j > r} a'_{n+j} 2^{-j}| \le 2^{-r}$, so $\{2^n X_k\} \notin [2^{-r} + \delta, 1 - 2^{-r})$ for every $\delta > 0$. Hence $F_N([2^{-r} + \delta, 1 - 2^{-r})) \le r \sigma_1(X_k; N + r)/N$, giving $D_N(X_k; 2) \ge 1 - 2^{1-r} - \delta - r \sigma_1(X_k; N + r)/N$; letting $\delta \downarrow 0$ and $N \to \infty$ gives $D^-(X_k; 2) \ge 1 - 2^{1-r} - r \alpha_k$. Choosing $r = \max(2, \lceil \log_2(1/\alpha_k) \rceil)$ yields $1 - D^-(X_k; 2) \ll (\log k)/k \to 0$. Assertion (2) follows immediately from subadditivity of $\|\cdot\|^s$ on $\mathbb{R}/\mathbb{Z}$ together with Theorem B2.1 and Corollary B2.2. $\square$

---

## 6. Prior Art, Attribution, and External Inputs Audit

### 6.1 Prior art and repository lineage

- **Erdős–Borwein constant $E(2)$ and irrationality:** Erdős (1948) proved $E(q) \notin \mathbb{Q}$ for integers $q \ge 2$; Borwein (1991, 1992) extended irrationality to $E_+(q)$ and $q$-series. For $E(2)$, `CC-20`–`CC-22` audit Captain Sude's elementary Lean disjunctivity release (covering $E(2)$ only; disjunctivity of $E(2^k)$ for $k \ge 3$ remains open) and Mira Cult's November 2026 short-window word-density theorem (which uses Perelli–Pintz–Salerno's short-interval Bombieri–Vinogradov theorem). Our B1 proof of $D^+(E(2^k); 2) < 1$ ($k \ge 3$) and $D^+(E_{\rm odd}(4); 2), D^+(E^*(4); 2) < 1$ provides a different, independent route for $k \ge 2$ via exact carry conservation + the 2-D Fundamental Lemma without Perelli–Pintz–Salerno, while saying nothing about $E(2)$ (where $C_U > 1 = k$).
- **Dense digit-mass transfer and $E_+(8)$:** Built directly on Phase 23 `GF-31` (displaced odd-part method on cubic $L_\pm(2^k)$), `GF-32` (carry-gauge and 3-state minimal-support transducer), `GF-35` (arithmetic correlations of $E_+$), Phase 24 `GF-36` (kernel-verified `DigitMassTransfer.lean` for $E(2^k)$, Senge–Straus barrier, signed transition-count transfer for $E_+(2^k)$ $k \ge 4$), and `GF-40` (4-state transducer for $E_+(8)$ with $D^- \ge 2.34 \times 10^{-7}$, elimination of Hypothesis (H2) via Topacogullari 2017).
- **Kernel tower and character transfers:** Uses `GF-01` (all-base $K_b$ discrepancy preservation), `GF-03` ($E_2 \in K_2$ base-2 simply normal), `GF-05` (base-2 sharp translation), `GF-07` (mod-24 2-elementary transfer, extended here to all $\varphi(M) = 2^t$), `GF-13` (even-order character Lambert series in $K_b$ preserving discrepancy in every base $b \ge 2$), `GF-23` ($M_b = M_{b^k}$), `GF-29` ($K_b = \mathrm{Fix}_b + M_b$), and `CC-04` (positive binary transition density $\iff D^+ < 1$).
- **Classical probabilistic, discrepancy, and binary-recoding foundations:** Paley–Zygmund second-moment inequality (R. E. A. C. Paley and A. Zygmund, *On some series of functions (3)*, Proc. Camb. Phil. Soc. 28(2) (1932), 190–205, used in Theorem B1.3); Koksma's inequality (J. F. Koksma, *Een algemeene stelling uit de theorie der gelijkmatige verdeeling modulo 1*, Mathematica (Zutphen) 11B (1942), 7–11; L. Kuipers and H. Niederreiter, *Uniform Distribution of Sequences*, Wiley, 1974, Ch. 2, Theorem 5.1; discrete circular total-variation variant proved directly in Theorem B3.3(2)); uniqueness and minimality of the non-adjacent form (NAF) (G. W. Reitwiesner, *Binary Arithmetic*, Advances in Computers, Vol. 1, Academic Press, 1960, pp. 231–308, used in Lemma B4.2 and §3).

### 6.2 External inputs and hypothesis verification

| External Input | Exact Statement Used | Where Used | Hypothesis Verification |
| --- | --- | --- | --- |
| **Fundamental Lemma of the Combinatorial Sieve** (H. Halberstam & H.-E. Richert, *Sieve Methods*, Academic Press, 1974, Theorem 2.5, pp. 82–85; G. Tenenbaum, *Introduction to Analytic and Probabilistic Number Theory*, 3rd ed., AMS GSM 163, 2015, Ch. I.4, Theorem 3, p. 60; H. Iwaniec & E. Kowalski, *Analytic Number Theory*, AMS Colloq. Publ. Vol. 53, 2004, §6.4, pp. 158–160) | Upper bound for dimension $\kappa = 2$ sieve (and $\kappa = 2/3$ split-prime sieve in Thm. B1.4(3)) with $g(p) = 2/p$ ($p \in \mathcal{P}_d \setminus \{p \mid u_1 u_2\}$), level $D = M^{3/8}$, sifting limit $z = M^\eta$, $s = \frac{3}{8\eta}$: $|A_d(u_1, u_2)| \le (1 + O(e^{-s \log s + O(s)})) \frac{M}{u_1 u_2} \prod_{p} (1 - \frac{2}{p}) + O(\sum_{q \le D} 2^{\omega(q)})$ | Thm. B1.3, Thm. B1.4, Thm. B4.1, Thm. B5.1–B5.2 | Verified: $\gcd(u_1, u_2) = 1$, $p \nmid d$ ensures $0 \not\equiv -d \pmod p$ ($p_1 \ge 5$ gives $g(p) \le 2/5 < 1$ and dimension bound uniform in $(d, u_1, u_2)$), $u_1 u_2 \le M^{1/4}$ leaves $M/(u_1 u_2) \ge M^{3/4} \gg D = M^{3/8}$, total remainder $\ll M^{5/8}(\log M)^3 = o(M)$, $s = \frac{3}{8\eta}$ chosen arbitrarily large. |
| **Halász's Mean-Value Theorem** (G. Halász, *Über die Mittelwerte multiplikativer zahlentheoretischer Funktionen*, Acta Math. Acad. Sci. Hungar. 19 (1968), 365–403) | If $f$ is 1-bounded multiplicative and $\sum_p (1 - \Re(f(p) p^{-it}))/p = \infty$ for all $t \in \mathbb{R}$, then $\frac{1}{X} \sum_{n \le X} f(n) \to 0$ | Thm. B1.4(3) ($L_-$ support), Thm. B1.5, Thm. B2.1, Thm. B5.1–B5.4 | Verified: after $y$-good squarefree-tail truncation (`GF-36` Lemma 3.2), $f(r) = \mathbf{1}_{\rm good}(r) \chi(r) e(u V(r)/k)$ is 1-bounded multiplicative; on $p \equiv 1 \pmod j$ (or split primes for $L_-$), $\chi(p) e(u \alpha/k) = e(u \alpha/k) \ne 1$ on positive prime density, forcing divergence for every $t \in \mathbb{R}$ (using $L(1+it, \chi) \ne 0$). |
| **Dirichlet's Theorem on Primes in Arithmetic Progressions** (classical) | $\sum_{p \le x,\, p \equiv a (M)} 1/p = \frac{1}{\varphi(M)} \log\log x + O_M(1)$ for $\gcd(a, M) = 1$ | Thm. B1.4(3), Thm. B1.5 | Verified: applied only for fixed moduli $M, j \ge 2$ and $\gcd(a, M) = 1$. |
| **`GF-13` (Wirsing / Selberg–Delange even-order character support)** | Every integer-valued linear combination of even-order character Lambert series lies in $K_b$ with $1 - D_N \ll (\log\log N)/(\log N)^{1/h_{\max}}$ | Thm. B5.2, Thm. B5.3 | Verified: every nonprincipal character of a Fermat-product modulus has order $2^s \ge 2$; for $\operatorname{odd}(\lambda(M)) \mid 3$, all characters other than principal and cubic have even order; integer-valued combinations verified explicitly. |
| **Senge–Straus (1973) / Stewart (1980)** | Only finitely many integers have bounded $s_a$ and $s_b$ when $\log a / \log b \notin \mathbb{Q}$ | Thm. B5.1(2) (barrier remark only) | Verified: invoked solely for the digit-mass barrier (`GF-36` Thm. 6.2); the displaced-unit $u_b$ divergence is proved elementarily without Senge–Straus. |
| **None (zero external inputs)** | Self-contained elementary proofs | Lem. B1.2, Cor. B1.2a, Thm. B3.1, Thm. B3.2, Thm. B3.3, Thm. B3.4, Lem. B3.5, Cor. B5.4(1) | All numerical bounds are exact rational/integer certificates in `scripts/phase25_lambert_eplus.py`. |

---

## 7. Reproduction Instructions and Verification Record

Run the standalone verification and certificate suite (Python 3.10+, standard library only, no third-party dependencies):

```powershell
python -B scripts/phase25_lambert_eplus.py
```

**Verified run record:**
- **Exit code:** `0` (elapsed ~3.5–6 s on Windows).
- **Total assertions passed:** **188,766**:
  - **186,311 `[exact]`** (exact integer / `Fraction` algebraic identities, $km - V(m) \ge 1$ through $m = 30{,}000$, direct-scaled certified 4,000-bit prefixes with explicit $4(M_{\rm tot} + 2)$ tail bounds and non-tautological checks of $q_n \ge 0$, dead-position/exit forcing, and the exact Lemma B1.2(2) dead-block inequality, cyclic phase-average systems for $2 \le j \le 8$, isolated-odd-arrival checks on $E_+(8), E_+(16), E_+(32)$, 4-state and 7-state automaton closure, Moore minimization, irreducibility/aperiodicity and exact stationary distribution $\pi_7$, exact $A_L$ and $V_{\rm circ}(L) = (2^L + 2(-1)^L)/3$ for $2 \le L \le 15$, exact $A_1 < \cdots < A_{14}(1, 3/2) = \frac{80897}{229376} < \frac{12}{31}$ and $V_{\rm circ} = 453$, 200 empirical Koksma checks, 250 exact-integer-ceiling Lean prefix-boundary checks $H_N - X_N \in \{0, 1\}$, $E_2$ pentagonal bound $3(102-2)^2 \le 8 \cdot 4000$, 400 separated-NAF additivity checks, all odd collision pairs $\le 63$, exact completeness of both moduli lists $2 \le M \le 257$ and $1 \le M \le 100$, mod-5 character and off-$\mathcal{E}_5$ popcount identities, mod-7 character reconstructions, and $6{,}561$ cubic trace identity tuples);
  - **2,428 `[encl]`** (scale-$2^{-96}$ outward-rounded integer intervals and integer `isqrt`/cube-root brackets—with zero floating-point formatting or checks—for $L_2^{\rm odd}, L_2^+, C_{U, \rm odd}, C_U, C_{U, +}, C_U^{(3)}, C_U^{(5)}, C_U^{(6)}$, Theorem B1.4(2) Markov cutoff $j_0 = 9$, $s = 1/2$ moments, $E_+(32)$ base-32 simple nonnormality, all 56 nonzero floored B2 $D^-(\cdot; 2^k)$ table endpoints, $W_+, W_+^{\rm maj}, \mu_{1, 3/2}$, all three DP-free Lean majorants including Tier-1 $< 23671/25000$ clearing $\ge 13/10^9$ at $L = 23$ and $L = 24$, all optimal-$L$ $D^-(E_+(8); 2)$ bounds, $W_+^{\rm maj}$ disjoint-block simple-nonnormality inequalities, $E_+(4)$ deficit and relative-deficit enclosures, and $\tau_4, \tau_8, \tau_3, \tau_5, \tau_7$ enclosures);
  - **27 `[finite]`** (clearly separated finite-prefix measurements of fixed-block cancellation on $E_+(4)$ and 12,000-bit base-2 prefix statistics of $E_+(2^k)$).

---

## 8. Explicit Open Questions and Standing Research Objectives Mapping

### 8.1 Standing objectives advanced (`docs/research-objectives.md`)

- **Objective 2 (Establish nonnormality):** Non-membership in $K_b$ (and in the full higher kernel tower $K_{2^j}$) for $E(2^k)$, $E_{\rm odd}(2^k)$, $E^*(2^k)$, $E_b^*(b^k)$, $E_+(2^k)$ ($k \ge k_0$), $L_\pm(2^k)$ ($k \ge k_0(\chi)$), and Fermat-product $A_{r, M}(2^k)$; direct base-2 and base-$2^j$ simple nonnormality of Fermat-product $A_{r, M}(2^k)$ ($k \ge 3$); zero-external-input simple nonnormality of $E_+(2^k)$ in base $2^k$ ($k \ge 4$), base $8$ ($k \ge 5$), base $4$ ($k \ge 8$), and $E_+(8)$ in base $2^L$ ($L \ge 13$); nonnormality of all periodic-weight Lambert series with $\operatorname{odd}(\lambda(M)) \mid 3$ and compatible $\mathbb{Z}$-linear combinations.
- **Objective 3 (Quantify digit distributions):** Full double-sided classification **$0 < D^- \le D^+ < 1$** across $E(2^k)$ ($k \ge 3$), $E_{\rm odd}(2^k)$ ($k \ge 3$), $E^*(2^k)$ ($k \ge 3$), $E_b^*(b^k)$ ($b \ge 3, k \ge 2$), $E_+(2^k)$ ($k \ge k_0$), $L_\pm(2^k)$ ($k \ge k_0(\chi)$), and $F_{2^k}(\tau_4)$ ($k \ge 10$), $F_{3^k}(\tau_3)$ ($k \ge 4$); $D^+ < 1$ at the $k = 2$ boundary for $E_{\rm odd}(4)$, $E^*(4)$, $E_b^*(b^2)$, and $A_{r, M}(4)$ ($M = 3, 5$, and even Fermat products); construction-radix limit **$D^-(\cdot; 2^k) \to 1$ at rate $O(\frac{\log k}{k})$** ($148\times$ sharper at $k=64$); $> 61\times$ and $> 101\times$ explicit discrepancy boosts for $E_+(8)$ ($D^- \ge 1.4362 \times 10^{-5}$ and $\ge 2.3642 \times 10^{-5}$).
- **Objective 4 (Establish rigorous mathematical limitations):** Two sharp limitation theorems—Theorem B3.1 (**Universal Transducer Obstruction**, proving no $(c_+, c_-)$-weighted signed-digit cost bound can establish base-2 simple nonnormality) and Theorem B4.1 (**Fixed-Window Cancellation Barrier**, proving every fixed-width $B$-block NAF grouping has zero asymptotic cancellation, exposing the $B = 8, 16$ finite-scale illusion)—plus the explicit Senge–Straus / multiplicative-independence boundary in Theorem B5.1(2).

### 8.2 Explicit open questions

1. **Base-2 simple nonnormality of $E_+(8)$ and $E_+(2^k)$ ($k \ge 3$):** Can a signed digit-asymmetry invariant (breaking the $0 \leftrightarrow 1$ symmetry of Theorem B3.1) prove $\limsup f_{1, N}(E_+(2^k); 2) < \frac{1}{2}$ for large $k$ or at $k = 3$?
2. **Explicit $k_0$ in Theorem B1.4 ($D^+(E_+(8); 2) < 1$):** Can $k_0$ in the Signed Isolated-Odd-Arrival Theorem be brought down to $k_0 = 3$ (proving $E_+(8) \notin K_2$ and $D^+(E_+(8); 2) < 1$)?
3. **The $k = 2$ boundary ($E(4)$, $E_{\rm odd}(4)$, $E^*(4)$, $E_+(4)$):** We proved $D^+ < 1$ and $\notin K_2$ for $E_{\rm odd}(4)$ and $E^*(4)$ (and $E^*(4) \notin K_{2^j}$ for all $j \ge 1$), while $D^-(E^*(4); 2) > 0$, $D^-(E_{\rm odd}(4); 2) > 0$, $D^\pm(E(4); 2)$, and $D^\pm(E_+(4); 2)$ remain **Open**. In each case, what is missing is a **lower bound** on growing-shift ($h \asymp \sqrt{\log\log M}$) bivariate column collisions (heuristic barrier parallel to `GF-36` §10; by contrast, the upper-bound side is unobstructed, as Theorem B1.3 demonstrates).
4. **Disjunctivity of $E(2^k)$ ($k \ge 3$):** Unlike $E(2)$ (where Captain Sude and `CC-21` establish disjunctivity), whether $E(8)$ is base-2 disjunctive remains **Open**.
5. **Exact limiting digit frequencies and exact $D_\infty$ for $E(2^k)$ ($k \ge 3$):** Proving existence of $\lim_{N \to \infty} f_{1, N}(E(2^k); 2)$ or $D_\infty(E(2^k); 2)$ remains **Open**.
6. **Non-dyadic $E(b^k)$ ($b \ne 2^j$, e.g. $E(9)_3, E(25)_5, E(100)_{10}$) and higher odd character orders ($\operatorname{odd}(\lambda(M)) \ge 5$, e.g. $M = 11, 19, 25$):** Both digit-mass and displaced-unit means diverge; all distributional properties remain **Open**.
7. **Stage 3 Lean 4 formalization:** Compile and `leanchecker`-replay the blueprint in §3.5 (`SignedTransducer.lean`) on `hail` to upgrade $E_+(2^k)$ ($k \ge 3$) nonnormality to **Kernel-verified** (`lean`).
