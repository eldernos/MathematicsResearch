# Classical constants: joint multi-prime BBP numerators for $\ln 2$, net carry complexity for quadratic irrationals, and the dyadic Lambert obstruction map

Phase 24, Track E (E1–E3). This note continues [classical-correlations-and-log2.md](../phase23/classical-correlations-and-log2.md) (`GF-35`, cited below as *P23-E*), [binary-partition-and-carry-complexity.md](../phase23/binary-partition-and-carry-complexity.md) (`GF-32`, cited as *P23-B3*), [dense-characters-and-nonfundamental-forms.md](../phase23/dense-characters-and-nonfundamental-forms.md) (`GF-31`), and [classical-targets-and-recon.md](../phase22/classical-targets-and-recon.md) (`GF-28`, cited as *P22-E*).

**Notation.** For an integer radix $b \ge 2$ and $x \in \mathbb{R}$, $D_N(x; b)$ denotes the extreme interval discrepancy of $(\{b^n x\})_{0 \le n < N}$, $D^+(x; b) = \limsup_N D_N(x; b)$, $D^-(x; b) = \liminf_N D_N(x; b)$, and $K_b = \{x : D_N(x; b) \to 1\}$. Write $e(t) = e^{2\pi i t}$, $\|t\| = \min_{k \in \mathbb{Z}} |t - k|$, $s_b(n) = \#\{i : d_i(n) \ne 0\}$ for the base-$b$ Hamming weight, $w_b^+(n) = \sum_i d_i(n)$ for the base-$b$ digit sum (so $s_2 = w_2^+$ in base $2$), and $w_2^\pm(n)$ for the minimum signed-digit (non-adjacent form, NAF) weight of $n \in \mathbb{Z}$. For the dyadic Lambert family,

```math
E(b) = \sum_{n \ge 1} \frac{1}{b^n - 1} = \sum_{n \ge 1} \tau(n) b^{-n}, \qquad
E_{\rm odd}(b) = \sum_{n\text{ odd}} \frac{1}{b^n - 1} = \sum_{n \ge 1} \tau_{\rm odd}(n) b^{-n},
```

```math
E_+(b) = \sum_{n \ge 1} \frac{1}{b^n + 1} = \sum_{n \ge 1} a_+(n) b^{-n}, \qquad
a_+(n) = \sum_{d \mid n} (-1)^{d-1} = (1 - v_2(n)) \tau_{\rm odd}(n),
```

with $E = E(2)$, $E_{\rm odd} = E_{\rm odd}(2)$, $E_+ = E_+(2)$.

**Evidence labels** (repository conventions, [`docs/research-objectives.md`](../../docs/research-objectives.md)):

- *Paper proof*: complete written proof in this note.
- *Finite certificate*: exact integer or rational computation, or a rigorous rational enclosure of an infinite sum/product, verified in [`scripts/phase24_classical.py`](../../scripts/phase24_classical.py).
- *External input*: a published theorem cited without re-proof.
- *Conditional*: proved here under a stated, unproved hypothesis.
- *Finite measurement*: finite digit or prefix statistics; bears on no asymptotic limit.
- *Numerical*: floating-point evaluation of an exact formula; not a certificate.
- *Open*.

Cross-model review is not independent human peer review.

**Scope statement.** **Nothing in this note proves normality, simple normality, simple nonnormality, $D^+ < 1$, or (non)membership in $K_2$ for $\ln 2$, $E(2)$, $E_{\rm odd}(2)$, $E_+(2)$, $\sqrt{2}$, $\sqrt{3}$, $\phi$, $\pi$, or any other unresolved constant in the fixed 50-constant benchmark roster (`BC-01`…`BC-50`). No benchmark status changes** (in particular, the existing external base-2 disjunctivity evidence recorded for `BC-37`, $E(2)$, is preserved unchanged while its normality, simple normality, $D^+ < 1$, and $K_2$ status remain open). The nonnormality results proved in §3 concern $E(2^k)$, $E_{\rm odd}(2^k)$, and $E_+(2^k)$ for $k \ge 3$ ($b = 8, 16, \dots$), which lie outside the fixed $b = 2$ entries `BC-37`–`BC-39`.

---

## Summary of conclusions

| Track | Result | Evidence |
| --- | --- | --- |
| E1 | **Same-band CRT collapse & global smooth-defect identity** (Thm. 1.1): For any surviving band-$m$ prime subset $S \subseteq I_m(N)$, the joint component $x_N^{(S)} = \sum_{p \in S} u_{N,p}/p \bmod 1$ collapses to $U_{N,S} \equiv 2^{N-m} A_m Q_m^{-1} H_S \pmod{M_S}$ ($M_S = \prod_{p \in S} p$, $H_S = \sum_{p \in S} M_S/p$). Globally for $N \ge 4$, $s_N = \sum_{1 \le m \le \sqrt{N}} 2^{N-m} s_m \sum_{p \in I_m(N)} 1/p + \widetilde{R}_N$ with explicit $\sqrt{N}$-smooth defect $\widetilde{R}_N$ in generalized Fermat quotients; across $[N, N+\Delta]$, prime-square exits $n+1 = p^2$ carry $p$-residue $-2 q_p(2)/p$, vanishing iff $p$ is Wieferich | Paper proof; finite certificate ($2{,}651$ multi-prime bands, $N \le 500$; global & shift identities verified) |
| E1 | **Unconditional $O(n^{2/3})$ dropped-prime mass bound** (Thm. 1.2): Answers *P23-E* Open Question 5 quantitatively: $\sum_{p \in D_n} \log p \le 4 n^{2/3}$ for all $n \ge 2$ (using $\operatorname{lcm}(1,\dots,m) \le 4^m$ and $\vartheta(x) \le (\log 4) x$), hence $\#D_n \ll n^{2/3}/\log n$ and every fixed-band complement satisfies $\log Q_n^{(> M_0)} = \vartheta(n/(M_0+1)) - O(n^{2/3})$ | Paper proof (+ Chebyshev/Rosser–Schoenfeld external); finite certificate ($A_m < 8^m$ & exact product bound, $n \le 1200$) + numerical check ($4 n^{2/3}$) |
| E1 | **Exact top-band real realization** (Thm. 1.3): $\ln 2 = \alpha_{\rm top} + \beta_{\rm low}$ with $\alpha_{\rm top} = \sum_{p \ge 3} (1 - 2^{1-p})/(p 2^p)$; Fermat cancellation eliminates all $p \le n/2$ identically mod $1$, giving $\{2^n \alpha_{\rm top}\} = \{\Phi_{n,1} + r_n^{\rm top}\}$ ($\Phi_{2,1} = 0$) with $|r_n^{\rm top}| < \frac{8}{3n}$ and $D^+(\alpha_{\rm top}; 2) < 1 \iff \limsup |\frac{1}{N} \sum_{n < N} e(\Phi_{n,1})| < 1$ | Paper proof; finite certificate ($\Phi_{n,1}$ recurrence $n \le 800$; fixed-point shadowing $< 2^{-43}$ with propagated tail/rounding bounds) |
| E1 | **Joint $r$-prime period identity & two model-specific barriers** (Thm. 1.4): Exact $g$-character factorization of complete-period $r = 2$ sums (exact closed form for primitive-root $g = 2$ pairs attaining $\frac{1}{2}\sqrt{p_1 p_2}$) and CRT-unit Gauss bound $|\sum| \le \sqrt{M_S}$; **Barrier 1**: for any $r \ge 2$ same-band primes, $L_W < p_1 < \sqrt{p_1 p_2} \le \sqrt{M_S}$, blocking generic completion already at $r = 2$; **Barrier 2** *(pointwise states, no required BBP recurrence)*: for any fixed $M_0 \ge 1$ and $\theta \in \mathbb{R}/\mathbb{Z}$, a single surviving prime $p^* \in P_n^{(> M_0)}$ aligns phases to $\|\tilde{x}_n - \theta\| \le 1/p^* \ll_{M_0} 1/n$ while preserving exact $Q_n$, $R_n$, and $\Phi_{n, M_0}$, yielding $|S_N(1)| \to 1$ | Paper proof; finite certificate ($19{,}487$ Barrier-1 pairs, $306$ Barrier-2 instances) + numerical check ($153$ $r=2$ pairs, $c_1=c_2=1$); **$D^+(\ln 2; 2) \le 0.9999$ Open** |
| E2 | **Exact carry-gauge quadratic residual & binary borrow dichotomy** (Thm. 2.1): For any quadratic irrational $A\alpha^2 + B\alpha + C = 0$ and any radix-equivalent $a' = d + b\delta - S\delta$, $x'_N = x_N - \delta_{N+1}$, $T_n(a') = \delta_{n+1} + \theta_n$, and $\Delta b^{2N} - (z'_N)^2 = 4 A (\theta_N + \delta_{N+1})(\sigma b^N \sqrt{\Delta} - A(\theta_N + \delta_{N+1}))$. For $\sqrt{2}$ in base $2$ ($N \ge 2$), $\delta_{N+1} = 0$ forces all `1`s in $(x'_N)^2$ on $[N+2, 2N]$, while $\delta_{N+1} = -1$ forces all `0`s | Paper proof; finite certificate ($567$ exact instances, $N = 2\dots 300$) |
| E2 | **Elementary convolution-borrow bounds & squaring carry identity** (Thm. 2.2): Explicit all-$N$ lower bounds $s_2(\lfloor 2^N \sqrt{2} \rfloor) \ge \frac{-1 + \sqrt{8N-7}}{2}$ ($N \ge 2$), $s_2(\lfloor 2^N \sqrt{3} \rfloor) \ge \frac{-1 + \sqrt{8N-15}}{2}$ ($N \ge 3$), $s_2(\lfloor 2^N \phi \rfloor) \ge \frac{1 + \sqrt{8N-31}}{2}$ ($N \ge 5$), general base-$b$ digit-sum bound, and exact squaring carry identity $(b-1)\Gamma_N = w_b^+(x_N)^2 - w_b^+(x_N^2)$ on ordinary digits of $x_N$ | Paper proof; finite certificate (from exact endpoints to $N = 1000$, $36$ base-$b$ cases); BBCP (2004) general degree $d$ cited as external |
| E2 | **Carry-gauge gap bound & signed-digit neutralization barrier** (Thm. 2.3): Elementary residual-norm bound $m_{j+1} \le 2 m_j + c_{\alpha,b}$ on fractional nonzero positions $1 \le m_1 < m_2 < \dots$ (with uniform first-position bound $m_1 \le M_1(\alpha,b)$) yields $\sigma_{B_0}(\alpha; N), \sigma_N(\alpha), \chi_N(\alpha) \ge \log_2 N - O(1)$ (and $\sigma_{B_0}/\log N, \sigma_N/\log N, \chi_N/\log N \to \infty$ via Ridout 1957, external). **Barrier**: signed-digit weight neutralizes the $N$-bit borrow cascade ($w_2^\pm(2^{2N+1}-E_N) \le 1 + w_2^\pm(E_N)$, witnesses $u_N = 2^N - 1$ have $s_2(u_N^2) = N$ yet $w_2^\pm(u_N^2) = 3$) | Paper proof (+ Ridout 1957 external); finite certificate; **$\sigma_N(\sqrt{2}) \gg N^\delta$ Open** |
| E2 | **Exponential-carry deficit barrier for binomial/Catalan/Pell series** (Thm. 2.4): Exact dyadic series for $\sqrt{2}, \sqrt{3}, \phi$ and Pell-accelerated series $q_r \sqrt{2} = p_r (1 + \epsilon/(2q_r^2))^{-1/2} = p_r \sum (-\epsilon)^k \binom{2k}{k}(8q_r^2)^{-k}$ ($\epsilon = p_r^2 - 2q_r^2 \in \{\pm 1\}$) satisfy eventual constant-sign or alternating-ratio hypotheses giving $|\delta_m| \asymp b^{\rho m} m^{-\gamma}$ ($\rho > 0$), linear raw-truncation window $L(n) \ge \frac{\rho}{1-\rho} n - O(\log n)$, and quadratic radix-$b$ displaced width $W_{U,b}(N) \sim \frac{\rho}{2s} N^2$, failing specific hypotheses of `GF-01`/`02`/`13`/`17` | Paper proof; finite certificate ($5$ series including base-200 gauge & width, Kummer $k \le 400$, Pell orders $r \le 16$) |
| E3 | **Certified popcount & NAF means and binary/NAF carry-balance inequalities** (Thm. 3.1): Unconditional outward-rounded certified enclosures $\mu_{\rm pop}(\tau) \in [1.337765, 1.346123]$, $\mu_{\rm pop}(\tau_{\rm odd}) \in [1.159430, 1.166471]$, $\mu_{\rm NAF}(a_+) \in [0.907252, 0.912845]$. Upper bound $f_{1,kM}(F_{2^k}(c); 2) + \bar{c}_{k,M} \le \frac{1}{kM}\sum_{n\le M} s_2(c(n)) + O(\frac{\log M}{M})$ proves simple nonnormality of $E(2^k)$ and $E_{\rm odd}(2^k)$ in bases $2$ and $2^k$ (with $D^-(E(2^k); 2) \ge 0.05129$) for every $k \ge 3$ | Paper proof + finite certificate (outward-rounded enclosures & independent column carry checks) |
| E3 | **Minimized 4-state NAF automaton & nonnormality of $E_+(2^k)$ for $k \ge 3$** (Thm. 3.2): Exhaustive 7-vector closure minimizes GF-32's 3-state transducer to a 4-state chain with stationary law $(\frac{1}{6}, \frac{1}{3}, \frac{1}{3}, \frac{1}{6})$ and exact closed floor $A_L = \frac{1}{3} - \frac{7 - (-1/2)^{L-1}}{18L}$ for every $L \ge 1$. Combined with $\limsup \sigma_1/N \ge A_L(1 - 2^L D^-)$ and $\mu_{\rm NAF}(a_+)/3 \le 0.304282 < A_{16} = \frac{324039}{1048576}$, this proves unconditionally that $E_+(2^k)$ is nonnormal in base $2$ and base $2^k$ with $D^-(E_+(2^k); 2) \ge 2.34 \times 10^{-7} > 0$ for every $k \ge 3$ (simple nonnormality of $E_+(8)$ remains open) | Paper proof + finite certificate (7-vector closure & 4-state lumping proof; finite cross-checks $L \le 20$, $L \le 10$) |
| E3 | **Exact finite-term reduction of $C_+(h; X)$ eliminating Hypothesis (H2)** (Thm. 3.3): Exact 3-term (odd $h$) and 4-term (even $h$, all $X \ge 1$) identities express $\sum_{n \le X} a_+(n) a_+(n+h)$ via unrestricted affine divisor sums $\sum \tau(a_1 m + b_1)\tau(a_2 m + b_2)$, reproducing $\frac{1}{4}(2 - 3 \cdot 2^{-k})$ and $\rho(h)$; combined with Topacogullari (2017) Thm. 1.2 (external) and *P23-E* Lemma 3.2's uniform majorant, this dispenses with (H2) in both *P23-E* corollaries | Paper proof; finite certificate ($128$ pairs, odd/even $X \le 2^{16}$); asymptotic uses Topacogullari (2017) Thm. 1.2 (external) |
| E3 | **Quantitative obstruction map: $E(8)$ vs $E(4), E(2), E_+(4), E_+(2)$** (§3.4): Lists certified sufficient carry-cancellation deficits and missing estimates separating $k \ge 3$ from $E(4)$ (base-4 bit-pair XOR bias; necessity/impossibility of binary popcount not proved), $E_+(4)$ (sufficient signed carry deficit $> 0.1231$), $E(2)$ (`BC-37`, external disjunctivity preserved), and $E_+(2)$ (sufficient signed carry deficit $> 0.579512$) | Paper proof + finite certificate + finite measurement; **$E(4), E(2), E_+(4), E_+(2)$ Open** |

---

## 1. Sub-track E1: Joint multi-prime BBP numerator correlations for $\ln 2$

Recall from *P23-E* §5 that the $N$-th BBP prefix of $\ln 2 = \sum_{k \ge 1} 2^{-k}/k$ is

```math
s_N = \sum_{k=1}^N \frac{2^{N-k}}{k} = \frac{A_N}{Q_N} \quad (\gcd(A_N, Q_N) = 1,\ Q_N \ge 1),
```

with $x_N = \{s_N\}$, $r_N = \sum_{k \ge 1} ((N+k)2^k)^{-1} \in (0, 1/N)$, $\{2^N \ln 2\} = \{x_N + r_N\}$, and $s_{N+1} = 2 s_N + 1/(N+1)$. By *P23-E* Theorem 5.3 (`GF-35`), every odd prime $p \in (\sqrt{N}, N]$ with band index $m = \lfloor N/p \rfloor$ satisfies $v_p(Q_N) = 1 - \mathbf{1}[p \mid A_m]$ and $p s_N \equiv 2^{N-m} s_m \pmod{p}$.

For $N \ge 2$ and $1 \le m \le \lfloor \sqrt{N} \rfloor$, define the **band-$m$ prime set** and its surviving subset:

```math
I_m(N) = \bigl\{p \text{ odd prime} : \max\bigl(\sqrt{N},\, \tfrac{N}{m+1}\bigr) < p \le \tfrac{N}{m}\bigr\}, \qquad
I_m^{\rm surv}(N) = \{p \in I_m(N) : p \nmid A_m\}.
```

Write $P_N = \bigcup_{1 \le m \le \sqrt{N}} I_m^{\rm surv}(N)$ (disjoint union) and $D_N = \{p \text{ odd prime} : \sqrt{N} < p \le N,\ p \mid A_{\lfloor N/p \rfloor}\}$ for the dropped large primes.

### 1.1 Exact same-band CRT collapse, global smooth defect, and consecutive-shift evolution

**Theorem 1.1 (Paper proof; finite certificate).** Let $N \ge 2$.

**(a) Exact same-band CRT collapse.** Fix a band $1 \le m \le \lfloor \sqrt{N} \rfloor$ and any nonempty subset $S \subseteq I_m^{\rm surv}(N)$. Set $M_S = \prod_{p \in S} p$ and $H_S = \sum_{p \in S} (M_S / p) = M_S \sum_{p \in S} 1/p \in \mathbb{Z}$. Then $\gcd(Q_m, M_S) = 1$, and the joint $S$-component $x_N^{(S)} = \sum_{p \in S} \frac{u_{N,p}}{p} \pmod{1}$ of $x_N$ equals $U_{N,S}/M_S \pmod{1}$ with exact joint numerator

```math
U_{N,S} \equiv 2^{N-m} A_m \, \overline{Q_m}^{(M_S)} H_S \pmod{M_S},
```

where $\overline{Q_m}^{(M_S)}$ is the inverse of $Q_m$ modulo $M_S$.

**(b) Exact rational lift with $Q_m$-correction.** Let $B_{N,S} = 2^{N-m} s_m \sum_{p \in S} \frac{1}{p}$. Then

```math
x_N^{(S)} \equiv B_{N,S} - \frac{2^{N-m} A_m \, \overline{M_S}^{(Q_m)} H_S}{Q_m} \pmod{1},
```

where $\overline{M_S}^{(Q_m)}$ is the inverse of $M_S$ modulo $Q_m$. In particular, for the top band $m = 1$ ($A_1 = Q_1 = s_1 = 1$), the $Q_1$-correction vanishes identically: $x_N^{(S)} \equiv 2^{N-1} \sum_{p \in S} \frac{1}{p} \pmod{1}$.

**(c) Global band decomposition with explicit $\sqrt{N}$-smooth defect.** For every $N \ge 4$, define the large-prime band sum

```math
X_N^{\rm big} = \sum_{1 \le m \le \sqrt{N}} 2^{N-m} s_m \sum_{p \in I_m(N)} \frac{1}{p}.
```

Then $s_N = X_N^{\rm big} + \widetilde{R}_N$ holds as an exact rational identity, where

```math
\widetilde{R}_N = \sum_{\substack{1 \le k \le N \\ P^+(k) \le \sqrt{N}}} \frac{2^{N-k}}{k}
  - \sum_{1 \le m \le \sqrt{N}} \sum_{p \in I_m(N)} \sum_{i=1}^m \frac{2^{N-ip}}{i} \cdot \frac{2^{i(p-1)} - 1}{p},
```

with $P^+(k)$ the largest prime factor of $k$ ($P^+(1) = 1$). Every term in the double sum has $(2^{i(p-1)} - 1)/p \in \mathbb{Z}$, and the reduced denominator of $\widetilde{R}_N$ is $\sqrt{N}$-smooth (divisible only by primes $q \le \sqrt{N}$). Dropped primes $p \in D_N$ are absorbed automatically: $s_m/p = (A_m/p)/Q_m$ is $p$-integral when $p \mid A_m$.

**(d) Exact consecutive-shift band evolution across $[N, N + \Delta]$.** For every $n \ge 4$:

```math
X_{n+1}^{\rm big} - 2 X_n^{\rm big} = \begin{cases}
  0, & P^+(n+1) \le \sqrt{n+1} \text{ and } n+1 \ne p^2 \text{ (odd prime } p\text{)}, \\
  \dfrac{2^{n+1 - (n+1)/P^+(n+1)}}{n+1}, & P^+(n+1) > \sqrt{n+1}, \\
  -\dfrac{2^{p^2 - p + 1} s_{p-1}}{p}, & n+1 = p^2 \text{ with } p \text{ an odd prime}.
\end{cases}
```

Consequently, for all $N \ge 4$ and $t \ge 1$,

```math
X_{N+t}^{\rm big} = 2^t X_N^{\rm big}
  + \sum_{\substack{N < j \le N+t \\ P^+(j) > \sqrt{j}}} \frac{2^{N+t - j/P^+(j)}}{j}
  - \sum_{\substack{N < p^2 \le N+t \\ p \text{ odd prime}}} \frac{2^{N+t - p + 1} s_{p-1}}{p}.
```

At a prime-square exit $n+1 = p^2$, the $p$-adic fractional part of the exit term $-2^{p^2-p+1} s_{p-1}/p$ equals $\langle -2 q_p(2) \bmod p \rangle / p$ by Glaisher's congruence (*P23-E* Proposition 5.4), where $q_p(2) = (2^{p-1} - 1)/p$; hence the $p$-pole of the exit jump vanishes if and only if $p$ is a **Wieferich prime**.

*Proof.* (a) Every prime factor of $Q_m$ is at most $m < \sqrt{N} < p$ for all $p \in S$, so $\gcd(Q_m, M_S) = 1$. Writing $x_N^{(S)} = U_{N,S}/M_S \pmod{1}$ with $U_{N,S} = \sum_{q \in S} u_{N,q} (M_S/q)$, reduce modulo each $p \in S$: every summand $q \ne p$ is divisible by $p$, so $U_{N,S} \equiv u_{N,p} (M_S/p) \pmod{p}$. By the same divisibility, $H_S = \sum_{q \in S} (M_S/q) \equiv M_S/p \pmod{p}$. By *P23-E* Theorem 5.3, $u_{N,p} \equiv 2^{N-m} A_m \overline{Q_m}^{(p)} \pmod{p}$. Thus $U_{N,S} \equiv 2^{N-m} A_m \overline{Q_m}^{(M_S)} H_S \pmod{p}$ simultaneously for every $p \in S$. Since $M_S$ is squarefree, CRT yields the congruence modulo $M_S$.

(b) Since $\gcd(Q_m, M_S) = 1$, pick integers $c, d$ with $c M_S + d Q_m = 1$, so $c \equiv \overline{M_S}^{(Q_m)} \pmod{Q_m}$ and $d \equiv \overline{Q_m}^{(M_S)} \pmod{M_S}$. Multiplying $1/(Q_m M_S) = c/Q_m + d/M_S$ by $2^{N-m} A_m H_S$ gives

```math
B_{N,S} = \frac{2^{N-m} A_m H_S}{Q_m M_S}
  = \frac{2^{N-m} A_m c H_S}{Q_m} + \frac{2^{N-m} A_m d H_S}{M_S}
  \equiv \frac{2^{N-m} A_m \overline{M_S}^{(Q_m)} H_S}{Q_m} + x_N^{(S)} \pmod{1}.
```

(c) For $N \ge 4$, $\sqrt{N} \ge 2$, so every integer $k \in [1, N]$ with $P^+(k) > \sqrt{N}$ has a unique prime factor $p > \sqrt{N}$ (which is odd, since $p > 2$ or $N \ge 4 \implies p \ge 3$), and $k = i p$ with $1 \le i \le m_p = \lfloor N/p \rfloor < \sqrt{N}$. Splitting $s_N$ into $P^+(k) \le \sqrt{N}$ and $P^+(k) > \sqrt{N}$ gives

```math
s_N - \sum_{\substack{1 \le k \le N \\ P^+(k) \le \sqrt{N}}} \frac{2^{N-k}}{k}
  = \sum_{1 \le m \le \sqrt{N}} \sum_{p \in I_m(N)} \sum_{i=1}^m \frac{2^{N-ip}}{ip}.
```

For each term, $2^{N-ip} - 2^{N-i} = -2^{N-ip}(2^{i(p-1)} - 1)$ with $N - ip \ge 0$ and $p \mid (2^{i(p-1)} - 1)$ by Fermat's little theorem. Dividing by $ip$ gives

```math
\frac{2^{N-ip}}{ip} = \frac{2^{N-i}}{ip} - \frac{2^{N-ip}}{i} \cdot \frac{2^{i(p-1)} - 1}{p}.
```

Summing over $i = 1, \dots, m$ yields $\sum_{i=1}^m 2^{N-i}/(ip) = 2^{N-m} s_m / p$, which gives $s_N = X_N^{\rm big} + \widetilde{R}_N$. Every denominator in $\widetilde{R}_N$ either has $P^+(k) \le \sqrt{N}$ or divides $i \le m \le \sqrt{N}$, so $\widetilde{R}_N$ has $\sqrt{N}$-smooth denominator.

(d) In $X_{n+1}^{\rm big} - 2 X_n^{\rm big}$, every prime $p > \sqrt{n+1}$ with $p \nmid (n+1)$ stays in the same band $m = \lfloor n/p \rfloor = \lfloor (n+1)/p \rfloor$ and its term $2^{n-m} s_m/p$ simply doubles, cancelling identically. The only remaining events are:
1. $n+1 = p^2$ for an odd prime $p$: then $p \in I_{p-1}(n)$ exits the large-prime set (since $p \le \sqrt{n+1}$), contributing $-2 \cdot 2^{n-(p-1)} s_{p-1}/p = -2^{p^2 - p + 1} s_{p-1}/p$, while no other prime $> \sqrt{n+1}$ divides $p^2$. By *P23-E* Proposition 5.4, $s_{p-1} \equiv 2^{p-1} q_p(2) \pmod{p}$, and $p - 1 \mid p^2 - 1$, so $-2^{p^2-p+1} s_{p-1} \equiv -2^{p^2} q_p(2) \equiv -2 q_p(2) \pmod{p}$ (since $2^{p^2} = 2 \cdot (2^{p-1})^{p+1} \equiv 2 \pmod{p}$).
2. $P^+(n+1) = p > \sqrt{n+1}$: writing $n+1 = m p$ ($1 \le m < \sqrt{n+1}$), $p$ moves from band $m - 1$ (with $s_0 = 0$ if $m = 1$) to band $m$. Its net contribution is $2^{n+1-m}(s_m - 2 s_{m-1})/p = 2^{n+1-m}/(mp) = 2^{n+1-m}/(n+1)$ by the BBP recurrence $s_m - 2 s_{m-1} = 1/m$.
3. $P^+(n+1) \le \sqrt{n+1}$ and $n+1$ is not an odd prime square: no prime enters, exits, or changes band, so $X_{n+1}^{\rm big} - 2 X_n^{\rm big} = 0$.

Iterating the one-step recurrence from $N$ to $N + t$ yields the multi-step formula (noting $(p^2 - p + 1) + (N + t - p^2) = N + t - p + 1$). $\square$

### 1.2 Unconditional $O(n^{2/3})$ bound on dropped band primes

Phase 23 (*P23-E* §5.2 and Open Question 5) observed that up to $N = 3000$, dropped primes $p \in D_N$ ($p \mid A_{\lfloor N/p \rfloor}$) carry less than $0.5\%$ of the large-prime logarithmic mass, and asked what structure they obey. The next theorem proves an elementary unconditional $O(n^{2/3})$ bound on their total mass.

**Theorem 1.2 (Paper proof; external Chebyshev/Rosser–Schoenfeld bounds; finite certificate).** For every integer $n \ge 2$,

```math
\sum_{p \in D_n} \log p \le 4\, n^{2/3}, \qquad \#D_n \le \frac{8\, n^{2/3}}{\log n}.
```

Consequently:
1. $\sum_{p \in P_n} \log p = \vartheta(n) - O(n^{2/3}) = (1 + o(1)) n$ (with the prime number theorem as external input for the asymptotic).
2. For every fixed band cutoff $M_0 \ge 1$, the surviving lower-band modulus $Q_n^{(> M_0)} = \prod_{m > M_0} \prod_{p \in I_m^{\rm surv}(n)} p$ satisfies

```math
\log Q_n^{(> M_0)} = \vartheta\!\left(\frac{n}{M_0 + 1}\right) - O(n^{2/3}) = \frac{n}{M_0 + 1}(1 + o(1)).
```

*Proof.* For every $m \ge 1$, $Q_m$ divides $\operatorname{lcm}(1, \dots, m) = e^{\psi(m)} \le 4^m$ (using $\psi(m) < 1.03883 m < (\log 4) m$ for all $m \ge 1$, Rosser–Schoenfeld 1962 Theorem 12, or Hanson 1972 $\operatorname{lcm}(1,\dots,m) \le 3^m$, external input). Also $s_m = \sum_{k=1}^m 2^{m-k}/k < 2^m \ln 2 < 2^m$, hence $A_m = s_m Q_m < 8^m$ and $\log A_m < (3 \log 2) m$.

Fix any integer cutoff $M_1 \ge 1$ and split $D_n$ into bands $1 \le m \le M_1$ and bands $m > M_1$:
- For each fixed $m \le M_1$, every prime $p \in D_n \cap I_m(n)$ divides the positive integer $A_m$, so $\prod_{p \in D_n \cap I_m(n)} p \mid A_m$, giving $\sum_{p \in D_n \cap I_m(n)} \log p \le \log A_m < (3 \log 2) m$. Summing over $1 \le m \le M_1$ gives at most $\frac{3 \log 2}{2} M_1(M_1 + 1)$.
- Every prime $p \in D_n$ in a band $m > M_1$ satisfies $p \le n/(M_1 + 1)$, so the total logarithmic mass of all primes (dropped or surviving) in bands $m > M_1$ is at most $\vartheta(n/(M_1 + 1)) \le (2 \log 2) \frac{n}{M_1 + 1}$ (using Erdős's elementary bound $\vartheta(x) \le (\log 4) x$ for all $x \ge 1$, external input).

Choose $M_1 = \max(1, \lfloor (2n/3)^{1/3} \rfloor)$. For $n \ge 2$, $(2n/3)^{1/3} \ge (4/3)^{1/3} > 1$, so $M_1 = \lfloor (2n/3)^{1/3} \rfloor \ge 1$ satisfies $M_1 \le (2n/3)^{1/3} < M_1 + 1$. Thus

```math
\sum_{p \in D_n} \log p
  \le \left[\frac{3}{2}\left(\frac{2}{3}\right)^{2/3} + 2\left(\frac{3}{2}\right)^{1/3}\right](\log 2)\, n^{2/3}
      + \frac{3}{2}\left(\frac{2}{3}\right)^{1/3}(\log 2)\, n^{1/3}
  < (2.381 + 0.909)\, n^{2/3} < 4\, n^{2/3}.
```

Since every $p \in D_n$ has $p > \sqrt{n}$ and $\log p > \frac{1}{2} \log n$, dividing by $\frac{1}{2}\log n$ gives $\#D_n \le 8 n^{2/3}/\log n$. Assertions (1)–(2) follow immediately by subtracting $\sum_{p \in D_n} \log p$ and $\vartheta(\sqrt{n}) = O(\sqrt{n})$ from $\vartheta(n)$ and $\vartheta(n/(M_0+1))$. $\square$

### 1.3 Exact top-band real realization $\ln 2 = \alpha_{\rm top} + \beta_{\rm low}$

By Theorem 1.1(b), the top-band ($m = 1$) component of $x_n$ has zero small-prime correction:

```math
\Phi_{n, 1} := \sum_{n/2 < p \le n} \frac{u_{n,p}}{p} \equiv 2^{n-1} \sum_{n/2 < p \le n} \frac{1}{p} \pmod{1} \qquad (n \ge 3,\ p \text{ odd prime}),
```

with the empty-sum convention $\Phi_{2, 1} := 0$ (since no odd prime satisfies $1 < p \le 2$). Surprisingly, $\Phi_{n,1}$ is shadowed with $O(1/n)$ error by the binary orbit of an explicit real prime series.

**Theorem 1.3 (Paper proof; finite certificate).** Define the convergent prime series and its residual

```math
\alpha_{\rm top} = \sum_{p \ge 3\text{ prime}} \frac{1 - 2^{1-p}}{p\, 2^p}, \qquad
\beta_{\rm low} = \ln 2 - \alpha_{\rm top} = \frac{5}{8} + \sum_{\substack{k \ge 4 \\ k\text{ composite}}} \frac{1}{k 2^k} + \sum_{p \ge 3\text{ prime}} \frac{2}{p\, 2^{2p}}.
```

Then:
1. For every $n \ge 3$, $\Phi_{n,1}$ obeys the exact prime-driven BBP recurrence

```math
\Phi_{n+1, 1} \equiv 2 \Phi_{n, 1} + \frac{\mathbf{1}_{\rm prime}(n+1)}{n+1} - \frac{2\,\mathbf{1}_{\rm odd\,prime}((n+1)/2)}{(n+1)/2} \pmod{1}.
```

2. For every $n \ge 2$, $\{2^n \alpha_{\rm top}\} = \{\Phi_{n,1} + r_n^{\rm top}\}$, where

```math
r_n^{\rm top} = \sum_{p > n} \frac{2^{n-p}(1 - 2^{1-p})}{p} - \sum_{n/2 < p \le n} \frac{2^{n+1-2p}}{p}, \qquad |r_n^{\rm top}| < \frac{8}{3n}.
```

3. Consequently, $\bigl|\frac{1}{N} \sum_{n=2}^{N-1} e(\Phi_{n,1}) - \frac{1}{N} \sum_{n=2}^{N-1} e(2^n \alpha_{\rm top})\bigr| \le \frac{16\pi}{3N} \sum_{n=2}^{N-1} \frac{1}{n} = O(\frac{\log N}{N})$, and by *P23-E* Proposition 5.1,

```math
\limsup_{N \to \infty} \left|\frac{1}{N} \sum_{n=2}^{N-1} e(\Phi_{n,1})\right| < 1 \iff D^+(\alpha_{\rm top}; 2) < 1.
```

*Proof.* (1) Comparing $\Phi_{n+1,1} = 2^n \sum_{(n+1)/2 < p \le n+1} 1/p$ with $2\Phi_{n,1} = 2^n \sum_{n/2 < p \le n} 1/p$: a prime $p$ enters iff $p = n+1$ is an odd prime, contributing $2^{p-1}/p \equiv 1/p \pmod{1}$ by Fermat's little theorem; a prime $p$ exits iff $p = (n+1)/2$ is an odd prime, contributing $-2^{2p-1}/p = -2 (2^{p-1})^2 / p \equiv -2/p \pmod{1}$.

(2) Expand $2^n \alpha_{\rm top} = \sum_{p \ge 3} (2^{n-p} - 2^{n+1-2p})/p$ into three ranges:
- $p > n$: yields the first sum in $r_n^{\rm top}$, which is positive and at most $\frac{1}{n+1} \sum_{k \ge 1} 2^{-k} = \frac{1}{n+1}$.
- $n/2 < p \le n$: splits into $\sum_{n/2 < p \le n} 2^{n-p}/p \equiv \sum_{n/2 < p \le n} 2^{n-1}/p = \Phi_{n,1} \pmod{1}$ (using $2^{p-1} \equiv 1 \pmod{p}$) minus the second sum in $r_n^{\rm top}$. Since $2p \ge n+1$, the nonnegative integers $2p - (n+1)$ are distinct and all have the same parity, so $\sum_{n/2 < p \le n} 2^{n+1-2p} \le \sum_{j \ge 0} 2^{-2j} = \frac{4}{3}$, while $1/p < 2/n$; hence the second sum lies in $[0, \frac{8}{3n})$.
- $3 \le p \le n/2$: here $n + 1 - 2p \ge 1$, so $(2^{n-p} - 2^{n+1-2p})/p = 2^{n+1-2p} (2^{p-1} - 1)/p = 2^{n+1-2p} q_p(2) \in \mathbb{Z}$, vanishing identically modulo $1$!

Since $r_n^{\rm top}$ is the difference of two nonnegative numbers bounded by $\frac{1}{n+1}$ and $\frac{8}{3n}$, $|r_n^{\rm top}| < \frac{8}{3n}$. Part (3) follows from $|e(t + r) - e(t)| \le 2\pi |r|$ and *P23-E* Proposition 5.1. $\square$

Thus the open problem noted in *P23-E* Open Question 4 ("even a saving restricted to the top band $m = 1$ is open") is equivalent to proving $D^+(\alpha_{\rm top}; 2) < 1$ for the explicit prime series $\alpha_{\rm top}$.

### 1.4 Joint multi-prime period factorization and two model-specific barriers

Now let $S = \{p_1, \dots, p_r\}$ be $r$ distinct odd primes in band $m$ ($p_1 < \dots < p_r$, $p_j \nmid A_m$), with $M_S = \prod_{j=1}^r p_j$, $t_j = \operatorname{ord}_{p_j}(2)$, and joint doubling period $T_S = \operatorname{ord}_{M_S}(2) = \operatorname{lcm}(t_1, \dots, t_r)$. Along the **joint band window** $W = \bigcap_{j=1}^r [m p_j, (m+1) p_j) = [m p_r, (m+1) p_1)$, the joint phase evolves by pure doubling: $x_n^{(S)} \equiv U_0 2^{n - n_0} / M_S \pmod{1}$ with $\gcd(U_0, M_S) = 1$.

**Theorem 1.4 (Paper proof; Barriers 1–2 finite certificate; $r = 2$ pairs numerical check).**

**(a) Exact $r = 2$ complete-period character factorization and general $r$-prime bound.** For two distinct odd primes $p_1 < p_2$, $g = \gcd(t_1, t_2)$, $T = t_1 t_2 / g$, and any $c_1, c_2$ with $p_j \nmid c_j$,

```math
\frac{1}{T} \sum_{k=0}^{T-1} e\!\left(\frac{c_1 2^k}{p_1} + \frac{c_2 2^k}{p_2}\right)
  = \sum_{j=0}^{g-1} \left(\frac{1}{t_1} \sum_{a=0}^{t_1 - 1} e\!\left(\frac{ja}{g} + \frac{c_1 2^a}{p_1}\right)\right)
    \left(\frac{1}{t_2} \sum_{b=0}^{t_2 - 1} e\!\left(\frac{-jb}{g} + \frac{c_2 2^b}{p_2}\right)\right).
```

If $2$ is a primitive root modulo both $p_1$ and $p_2$ with $g = 2$, this evaluates in closed form to

```math
\sum_{k=0}^{T-1} e\!\left(\frac{c_1 2^k}{p_1} + \frac{c_2 2^k}{p_2}\right)
  = \frac{1}{2}\left(1 + \left(\frac{c_1}{p_1}\right)\left(\frac{c_2}{p_2}\right)\varepsilon_{p_1}\varepsilon_{p_2}\sqrt{p_1 p_2}\right),
```

where $\varepsilon_p = 1$ if $p \equiv 1 \pmod 4$ and $\varepsilon_p = i$ if $p \equiv 3 \pmod 4$, showing that $\sqrt{p_1 p_2}$ is attained up to factor $2$. For arbitrary $r \ge 1$ and $\gcd(U_0, M_S) = 1$,

```math
\left|\frac{1}{T_S} \sum_{k=0}^{T_S - 1} e\!\left(\frac{U_0 2^k}{M_S}\right)\right| \le \frac{\sqrt{M_S}}{T_S}.
```

**(b) Barrier 1 (Joint-window completion barrier at $r \ge 2$).** For every $r \ge 2$ and every $r$-tuple of distinct primes $p_1 < \dots < p_r$ in the same band $m \ge 1$ with nonempty joint window $W = [m p_r, (m+1) p_1)$, the window length $L_W = (m+1)p_1 - m p_r$ satisfies

```math
L_W < p_1 < \sqrt{p_1 p_2} \le \sqrt{M_S}.
```

Consequently, whereas a single prime ($r = 1$) has window length $L_W = p_1 > \sqrt{p_1}$ (allowing Gauss-period cancellation when $t_1 \gg \sqrt{p_1}$), the generic character-sum completion bound $\sqrt{M_S} \log T_S$ on $(\mathbb{Z}/M_S\mathbb{Z})^\times$ exceeds the entire joint band window $L_W$ already at $r = 2$, and exceeds it exponentially ($\exp(n/4 + o(n))$ vs $n$, since the prime number theorem gives $\log \sqrt{M} = \frac{1}{2}(\vartheta(n) - \vartheta(n/2)) = n/4 + o(n)$ across the top band) across all top-band primes.

**(c) Barrier 2 (Fixed-band complement alignment barrier for pointwise states).** Fix any band cutoff $M_0 \ge 1$ and any target angle $\theta \in \mathbb{R}/\mathbb{Z}$. For every $n$ large enough that $P_n^{(> M_0)} = \{p \in P_n : \lfloor n/p \rfloor > M_0\}$ is nonempty (which holds for all large $n$ by Theorem 1.2, with $p_n^* = \max P_n^{(> M_0)} = \frac{n}{M_0+1}(1 - o(1))$), there exists a rational state $\tilde{x}_n \in \mathbb{Q}/\mathbb{Z}$ such that:
1. $\tilde{x}_n$ has the **exact same reduced denominator** $Q_n$ as $x_n$;
2. $\tilde{x}_n$ has the **exact same $\sqrt{n}$-smooth component** $R_n$ and the **exact same top-$M_0$-band phases** $\Phi_{n, M_0} = \sum_{m=1}^{M_0} \sum_{p \in I_m^{\rm surv}(n)} u_{n,p}/p \pmod{1}$ as $x_n$;
3. $\|\tilde{x}_n - \theta\| \le 1/p_n^* \ll_{M_0} 1/n$, and therefore $\bigl|\frac{1}{N} \sum_{n < N} e(\tilde{x}_n)\bigr| \ge 1 - O_{M_0}(\frac{\log N}{N}) \to 1$.

This is a **pointwise-state barrier**: the modified states $\tilde{x}_n$ are not required to satisfy a BBP recurrence between successive times $n \to n+1$. Thus no purely pointwise distributional property of the top $M_0$ bands alone (even full joint equidistribution of $\Phi_{n, M_0}$ together with exact knowledge of $Q_n$ and $R_n$) can yield any fixed saving $\eta > 0$ in $|S_N(1)|$ without simultaneous control of the complementary bands $m > M_0$ or dynamical coupling across $n$.

*Proof.* (a) As $k$ runs over $\mathbb{Z}/T\mathbb{Z}$, $(k \bmod t_1, k \bmod t_2)$ visits every $(a, b) \in (\mathbb{Z}/t_1\mathbb{Z}) \times (\mathbb{Z}/t_2\mathbb{Z})$ with $a \equiv b \pmod{g}$ once. Substituting $\mathbf{1}[a \equiv b \pmod{g}] = \frac{1}{g} \sum_{j=0}^{g-1} e(j(a-b)/g)$ and dividing by $T = t_1 t_2 / g$ cancels $g$ and gives the identity. When $t_j = p_j - 1$ and $g = 2$, the $j = 0$ term is $(-1)(-1) = 1$, and the $j = 1$ term is the product of quadratic Gauss sums $\tau(\chi_{p_1}, c_1) \tau(\chi_{p_2}, c_2) = (\frac{c_1}{p_1})(\frac{c_2}{p_2}) \varepsilon_{p_1}\varepsilon_{p_2}\sqrt{p_1 p_2}$; multiplying by $T/(t_1 t_2) = 1/2$ gives the closed form. For general $r \ge 1$, let $H = \langle 2 \rangle \le (\mathbb{Z}/M_S\mathbb{Z})^\times$ have index $K_S = \varphi(M_S)/T_S$; expanding $\mathbf{1}_H$ in Dirichlet characters $\chi \bmod M_S$ gives

```math
\sum_{k=0}^{T_S - 1} e\!\left(\frac{U_0 2^k}{M_S}\right) = \frac{1}{K_S} \sum_{\substack{\chi \bmod M_S \\ \chi(2) = 1}} \overline{\chi(U_0)}\, \tau_{M_S}(\chi),
```

where, setting $h_p = (M_S/p)^{-1} \bmod p$ for each $p \mid M_S$, Chinese remainder factorization of the standard additive character gives

```math
\tau_{M_S}(\chi) = \prod_{p \mid M_S} \overline{\chi_p(h_p)}\, \tau_p(\chi_p).
```

Each CRT unit $\overline{\chi_p(h_p)}$ has modulus $1$, and each local Gauss sum $\tau_p(\chi_p)$ has modulus $\sqrt{p}$ when $\chi_p$ is nonprincipal and $1$ when $\chi_p$ is principal; hence $|\tau_{M_S}(\chi)| \le \sqrt{M_S}$ for every $\chi \bmod M_S$ (including imprimitive characters). There are $K_S$ characters with $\chi(2) = 1$, so the triangle inequality gives $|\sum| \le \sqrt{M_S}$.

(b) Since $p_1 < p_2 \le p_r$ and $m \ge 1$, $L_W = (m+1)p_1 - m p_r = p_1 - m(p_r - p_1) < p_1 < \sqrt{p_1 p_2} \le \sqrt{M_S}$.

(c) Keep $R_n$ and all $u_{n,p}$ for $p \in P_n \setminus P_n^{(> M_0)}$ unchanged; set $\tilde{u}_{n,p} = 1$ for every $p \in P_n^{(> M_0)} \setminus \{p_n^*\}$. Let $z_n = R_n + \Phi_{n, M_0} + \sum_{p \in P_n^{(> M_0)} \setminus \{p_n^*\}} 1/p \pmod{1}$. As $u$ varies over $\{1, 2, \dots, p_n^* - 1\}$, the points $z_n + u/p_n^* \pmod{1}$ form a $1/p_n^*$-spaced grid on $\mathbb{R}/\mathbb{Z}$ with a single omitted point $z_n$ (leaving a maximum gap of $2/p_n^*$), so some $u^* \in \{1, \dots, p_n^* - 1\}$ satisfies $\|z_n + u^*/p_n^* - \theta\| \le 1/p_n^*$. Setting $\tilde{u}_{n, p_n^*} = u^*$ leaves every prime $p \in P_n$ with a nonzero residue mod $p$, preserving the exact reduced denominator $Q_n$. Since $p_n^* \ge \frac{n}{2(M_0+1)}$ for all large $n$ (Theorem 1.2 + PNT), $|e(\tilde{x}_n) - e(\theta)| \le 2\pi/p_n^* = O_{M_0}(1/n)$, giving $|S_N(1)| \ge 1 - O_{M_0}(\frac{\log N}{N})$. $\square$

*Finite measurement* (53-bit points from certified expansions; bears on no limit):

| $N$ | $|S_N(1; \ln 2)|$ | $|S_N(1; \alpha_{\rm top})|$ | $|S_N(1; \beta_{\rm low})|$ |
| --- | --- | --- | --- |
| $1024$ | $0.0337$ | $0.0052$ | $0.0432$ |
| $2048$ | $0.0262$ | $0.0137$ | $0.0316$ |
| $4096$ | $0.0248$ | $0.0077$ | $0.0171$ |

**$D^+(\ln 2; 2) \le 0.9999$ and $D^+(\alpha_{\rm top}; 2) < 1$ remain Open.**

---

## 2. Sub-track E2: Algebraic irrationals ($\sqrt{2}, \sqrt{3}, \phi$) via net carry complexity

Let $\alpha > 0$ be a real quadratic irrational with primitive minimal polynomial $A \alpha^2 + B \alpha + C = 0$ ($A, B, C \in \mathbb{Z}$, $A > 0$, $\gcd(A, B, C) = 1$, discriminant $\Delta = B^2 - 4AC > 0$ nonsquare, and $\sigma = \operatorname{sign}(2A\alpha + B) \in \{+1, -1\}$). Fix an integer radix $b \ge 2$ and write $\alpha = d_0 + \sum_{m \ge 1} d_m b^{-m}$ ($d_0 = \lfloor \alpha \rfloor$, $d_m \in \{0, \dots, b-1\}$), with $N$-digit prefix $x_N = \lfloor b^N \alpha \rfloor = \sum_{m=0}^N d_m b^{N-m}$ and orbit point $\theta_N = \{b^N \alpha\} = b^N \alpha - x_N \in (0, 1)$.

By *P23-B3* Theorem 5.2 (`GF-32`, Lean: `carry_gauge_telescoping`, `carry_kernel_eq_zero_of_tendsto`), every integer sequence $a' = (a'_m)_{m \ge 0}$ with $\sum_{m \ge 0} a'_m b^{-m} = \alpha$ (absolutely convergent) satisfies the **carry-gauge identity**

```math
a'_0 = d_0 - \delta_1, \qquad a'_m = d_m + b \delta_m - \delta_{m+1} \quad (m \ge 1),
```

for a **unique** integer carry sequence $\delta$ with $\delta_m = o(b^m)$, namely $\delta_m = \sum_{j \ge 0} (a'_{m+j} - d_{m+j}) b^{-1-j}$.

### 2.1 Exact carry-gauge quadratic residual identity and binary borrow dichotomy

**Theorem 2.1 (Paper proof; finite certificate).** Let $a' = (a'_m)_{m \ge 0}$ be any radix-equivalent representation of $\alpha$ with canonical carry $\delta$, prefix $x'_N = \sum_{m=0}^N a'_m b^{N-m}$, and raw tail $T_N(a') = \sum_{j \ge 1} a'_{N+j} b^{-j}$. Define the integer norm-form defect and completed-square prefix

```math
E'_N(\alpha; b) = -\bigl(A (x'_N)^2 + B b^N x'_N + C b^{2N}\bigr) \in \mathbb{Z} \setminus \{0\}, \qquad
z'_N = 2 A x'_N + B b^N.
```

Then for every $N \ge 0$:
1. *(Exact telescoping & tail identification.)* $x'_N = x_N - \delta_{N+1}$, $T_N(a') = \delta_{N+1} + \theta_N$, so $\delta_{N+1} = \lfloor T_N(a') \rfloor$ and $\theta_N = \{T_N(a')\}$.
2. *(Exact quadratic residual & completed-square identity.)*

```math
E'_N(\alpha; b) = (\theta_N + \delta_{N+1})\bigl(\sigma b^N \sqrt{\Delta} - A(\theta_N + \delta_{N+1})\bigr), \qquad
\Delta b^{2N} - (z'_N)^2 = 4 A E'_N(\alpha; b).
```

3. *(Binary borrow dichotomy on $\delta_{N+1} \in \{0, -1\}$.)* For $\alpha = \sqrt{2}$ in base $2$ ($A = 1, B = 0, C = -2, \Delta = 8, \sigma = +1$) and every $N \ge 2$:
   - If $\delta_{N+1} = 0$ ($x'_N = x_N = \lfloor 2^N \sqrt{2} \rfloor$), then $1 \le E'_N < 2^{N+1}\sqrt{2} < 2^{N+2}$, so $(x'_N)^2 = 2^{2N+1} - E'_N$ has **every binary bit in positions $[N+2, 2N]$ equal to `1`** (a forced borrow cascade of length $N - 1$).
   - If $\delta_{N+1} = -1$ ($x'_N = x_N + 1 = \lceil 2^N \sqrt{2} \rceil$), then $-2^{N+2} < E'_N \le -1$, so $(x'_N)^2 = 2^{2N+1} + |E'_N|$ has **every binary bit in positions $[N+2, 2N]$ equal to `0`** (zero borrow).

*Proof.* (1) By *P23-B3* Lemma 5.1, $\sum_{m=1}^N (b\delta_m - \delta_{m+1}) b^{N-m} = \delta_1 b^N - \delta_{N+1}$, so $x'_N = (d_0 - \delta_1) b^N + \sum_{m=1}^N d_m b^{N-m} + \delta_1 b^N - \delta_{N+1} = x_N - \delta_{N+1}$. Setting $m = N + 1$ in $\delta_m = \sum_{j \ge 0} (a'_{m+j} - d_{m+j}) b^{-1-j}$ gives $\delta_{N+1} = T_N(a') - \theta_N$. Since $\delta_{N+1} \in \mathbb{Z}$ and $\theta_N \in (0, 1)$, $\delta_{N+1} = \lfloor T_N(a') \rfloor$ and $\theta_N = \{T_N(a')\}$.

(2) Substitute $x'_N = b^N \alpha - (\theta_N + \delta_{N+1})$ into $A (x'_N)^2 + B b^N x'_N + C b^{2N}$ and use $A\alpha^2 + B\alpha + C = 0$ and $2A\alpha + B = \sigma\sqrt{\Delta}$:

```math
A (x'_N)^2 + B b^N x'_N + C b^{2N}
  = -(\theta_N + \delta_{N+1})\bigl(b^N (2A\alpha + B) - A(\theta_N + \delta_{N+1})\bigr) = -E'_N(\alpha; b).
```

Completing the square gives $(z'_N)^2 = 4 A^2 (x'_N)^2 + 4 A B b^N x'_N + B^2 b^{2N} = \Delta b^{2N} - 4 A E'_N(\alpha; b)$. Irrationality of $\alpha$ forces $E'_N(\alpha; b) \ne 0$.

(3) For $\sqrt{2}$, $(x'_N)^2 = 2^{2N+1} - E'_N$. At $\delta_{N+1} = 0$, $0 < \theta_N < 1$ gives $1 \le E'_N < 2^{N+1}\sqrt{2} < 2^{N+2}$, so $2^{2N+1} - 2^{N+2} < (x'_N)^2 \le 2^{2N+1} - 1$; since $2^{2N+1} - 2^{N+2} = \sum_{j=N+2}^{2N} 2^j$, all bits in $[N+2, 2N]$ are `1`. At $\delta_{N+1} = -1$, $\theta_N - 1 \in (-1, 0)$ gives $1 \le |E'_N| < 2^{N+1}\sqrt{2} + 1 < 2^{N+2}$ (for $N \ge 2$), so $2^{2N+1} < (x'_N)^2 < 2^{2N+1} + 2^{N+2}$, making all bits in $[N+2, 2N]$ equal to `0`. $\square$

### 2.2 Elementary convolution-borrow lower bounds on $s_b$ and the squaring carry identity

Bailey–Borwein–Crandall–Pomerance (2004, Theorem 7.1; *External input*) proved that every real algebraic irrational of degree $d \ge 2$ has $\gg N^{1/d}$ ones among its first $N$ binary digits; Adamczewski–Bugeaud (2007; *External input*) proved superlinear subword complexity $p(n)/n \to \infty$. From Theorem 2.1(2)–(3) we obtain a self-contained elementary proof of explicit all-$N$ constants for $\sqrt{2}, \sqrt{3}, \phi$ and general $\sqrt{D}$ in arbitrary base $b \ge 2$, together with an exact identity for the total squaring carry.

**Theorem 2.2 (Paper proof; finite certificate).**

1. *(Exact squaring carry identity.)* Write the entire nonnegative integer $x_N = \sum_{i=0}^K \tilde{d}_i b^i$ in its **ordinary** base-$b$ expansion ($\tilde{d}_i \in \{0, \dots, b-1\}$, so $w_b^+(x_N) = \sum_{i=0}^K \tilde{d}_i$; note that the shorthand integer part $d_0 = \lfloor \alpha \rfloor$ may itself require several base-$b$ digits, e.g. $b = 2, \alpha = \sqrt{5}, N = 0$ gives $d_0 = 2$ while $w_2^+(x_0) = 1$). Let $\Gamma_N \ge 0$ be the sum of all column carries generated when normalizing the nonnegative convolution $(\tilde{d} * \tilde{d})_k = \sum_{i+j=k} \tilde{d}_i \tilde{d}_j$ into the ordinary base-$b$ expansion of $x_N^2$. Then

```math
(b - 1)\, \Gamma_N = \bigl(w_b^+(x_N)\bigr)^2 - w_b^+(x_N^2).
```

2. *(General base-$b$ bound for $\sqrt{D}$.)* For any nonsquare integer $D \ge 2$, any radix $b \ge 2$, and $x_N = \lfloor b^N \sqrt{D} \rfloor$, put $v_b(D) = \max\{j \ge 0 : b^j \mid D\}$ (including for composite $b$) and $c_{b,D} = \lfloor \log_b(2\sqrt{D}) \rfloor + 1$. For every $N > c_{b,D} - v_b(D)$,

```math
w_b^+(x_N^2) \ge (b - 1)\bigl(N + v_b(D) - c_{b,D}\bigr), \qquad
w_b^+(x_N) \ge \sqrt{(b - 1)\bigl(N + v_b(D) - c_{b,D}\bigr)}.
```

3. *(Explicit base-2 constants for $\sqrt{2}, \sqrt{3}, \phi$.)* Using $s_2(x^2) \le s_2(x)(s_2(x)+1)/2$, we have unconditionally:
   - $s_2(\lfloor 2^N \sqrt{2} \rfloor) \ge \frac{-1 + \sqrt{8N - 7}}{2}$ for all $N \ge 2$;
   - $s_2(\lfloor 2^N \sqrt{3} \rfloor) \ge \frac{-1 + \sqrt{8N - 15}}{2}$ for all $N \ge 3$;
   - $s_2(\lfloor 2^N \phi \rfloor) \ge \frac{1 + \sqrt{8N - 31}}{2}$ for all $N \ge 5$.

*Proof.* (1) At each column $k$ of the base-$b$ normalization of $c_k = (\tilde{d} * \tilde{d})_k$, $c_k + \gamma_{k-1} = \tilde{d}_k(x_N^2) + b \gamma_k$. Summing over all columns through carry exhaustion (with boundary carries $0$) yields $\sum_k c_k - w_b^+(x_N^2) = (b - 1) \sum_k \gamma_k = (b - 1)\Gamma_N$. Since $\sum_k c_k = (\sum_i \tilde{d}_i)^2 = w_b^+(x_N)^2$, the identity follows.

(2) By Theorem 2.1(2) at $\delta = 0$, $x_N^2 = D b^{2N} - E_N$ with $1 \le E_N < 2\sqrt{D} b^N < b^{N + c_{b,D}}$. Since $D b^{2N}$ is divisible by $b^{2N + v_b(D)}$, subtracting $E_N$ forces every base-$b$ digit of $x_N^2$ in positions $N + c_{b,D}, \dots, 2N + v_b(D) - 1$ to equal $b - 1$, giving $w_b^+(x_N^2) \ge (b - 1)(N + v_b(D) - c_{b,D})$. Since $\Gamma_N \ge 0$, (1) yields $w_b^+(x_N)^2 \ge w_b^+(x_N^2)$.

(3) For any $x = \sum_{r=1}^k 2^{e_r} \ge 0$, $x^2 = \sum_r 2^{2 e_r} + \sum_{r < s} 2^{e_r + e_s + 1}$ is a sum of $k + \binom{k}{2} = \frac{k(k+1)}{2}$ positive powers of $2$, so $s_2(x^2) \le \frac{k(k+1)}{2}$. Applying (2) at $b = 2$ gives $s_2(x_N^2) \ge N - 1$ for $D = 2$ ($v_2(2) = 1, c_{2,2} = 2$) and $s_2(x_N^2) \ge N - 2$ for $D = 3$ ($v_2(3) = 0, c_{2,3} = 2$). For $\phi = \frac{1 + \sqrt{5}}{2}$, since $\phi \in (\frac{3}{2}, 2)$, $x_N = \lfloor 2^N \phi \rfloor = 2^N + 2^{N-1} + r_N$ with $0 \le r_N < 2^{N-1}$ for every $N \ge 1$. Hence $z_N = 2 x_N - 2^N = 2^{N+1} + 2 r_N$ satisfies $s_2(z_N) = 1 + s_2(r_N) = s_2(x_N) - 1$ identically! By Theorem 2.1(2), $z_N^2 = 5 \cdot 4^N - 4 E_N(\phi)$ with $1 \le 4 E_N(\phi) < 4\sqrt{5} \cdot 2^N < 2^{N+4}$, so every bit of $z_N^2$ in $[N+4, 2N-1]$ is `1`, giving $s_2(z_N^2) \ge N - 4$ and $\frac{s_2(z_N)(s_2(z_N)+1)}{2} \ge N - 4$, hence $s_2(x_N) = 1 + s_2(z_N) \ge \frac{1 + \sqrt{8N - 31}}{2}$. (Note that the constants for $\sqrt{3}$ and $\phi$ are explicit rather than optimal: the high bit at $2N+1$ in $3 \cdot 4^N - E_N$ also survives, giving $s_2(x_N^2) \ge N - 1$, and similarly the high bit at $2N+2$ in $5 \cdot 4^N - 4 E_N(\phi)$ survives, giving $s_2(z_N^2) \ge N - 3$.) $\square$

### 2.3 Carry-gauge gap lower bound and the signed-digit neutralization barrier

Recall from *P23-B3* Theorems 5.4–5.5 (`GF-32`) that the minimal net support $\sigma_B(\alpha; N)$ (counting fractional positions $1 \le m \le N$ modulo integers, with $B = \lfloor b/2 \rfloor$), the fixed-point minimum $\sigma_N(\alpha) = \min_{c \in F_b} \sigma_B(\alpha - c; N)$ ($F_b = \{j/(b-1) : 0 \le j \le b-2\}$), and the digit-transition count $\chi_N(\alpha)$ satisfy $\frac{1}{3} \chi_{N-2}(\alpha) \le \sigma_B(\alpha; N) \le \chi_N(\alpha) + 1$, and $D^+(\alpha; b) < 1 \iff \liminf \sigma_N(\alpha)/N > 0$. Why does the elementary convolution-borrow bound of Theorem 2.2 give $\Omega(\sqrt{N})$ for ordinary `1`-bits $s_2(x_N)$, yet fail to yield $\Omega(\sqrt{N})$ for minimal net support $\sigma_N(\alpha)$ or digit transitions $\chi_N(\alpha)$?

**Theorem 2.3 (Paper proof; Ridout 1957 external for superlogarithmic step; finite certificate).**

**(a) Carry-gauge gap recurrence.** Let $\alpha$ be a real quadratic irrational ($A\alpha^2 + B\alpha + C = 0$, $A > 0$, $\Delta = B^2 - 4AC > 0$), $b \ge 2$, $B_0 = \lfloor b/2 \rfloor$, and let $a' = (a'_m)_{m \ge 0}$ be any signed-digit representation with $\alpha - \sum_{m \ge 0} a'_m b^{-m} \in \mathbb{Z}$ (allowing an arbitrary integer representative $a'_0 \in \mathbb{Z}$), $|a'_m| \le B_0$ for $m \ge 1$, and **fractional** nonzero positions $1 \le m_1 < m_2 < \dots$. Then the first fractional position satisfies the representation-independent bound

```math
m_1 \le M_1(\alpha, b) := 1 + \left\lfloor \log_b\!\left(\frac{B_0}{(b - 1)\|\alpha\|}\right) \right\rfloor,
```

and for every $j \ge 1$,

```math
m_{j+1} \le 2 m_j + c_{\alpha, b}, \qquad
c_{\alpha, b} = \left\lfloor \log_b\!\left(\frac{B_0 b}{b - 1}\bigl(\sqrt{\Delta} + A\bigr)\right) \right\rfloor.
```

(In base $2$ with $B_0 = 1$: $c_{\alpha, 2} = 2, 3, 2$ for $\sqrt{2}, \sqrt{3}, \phi$ respectively, for every $j \ge 1$, and $M_1(\alpha, 2) = 2$ for all three.) Consequently, unconditionally and elementarily, for every $N \ge 1$,

```math
\sigma_{B_0}(\alpha; N) \ge \log_2\!\left(\frac{N + 1 + c_{\alpha,b}}{M_1(\alpha, b) + c_{\alpha,b}}\right), \qquad
\chi_N(\alpha) \ge \log_2 N - O_{\alpha, b}(1),
```

and applying the same estimate to the finitely many quadratic translates $\alpha - c$ ($c \in F_b$) gives $\sigma_N(\alpha) \ge \log_2 N - O_{\alpha, b}(1)$. Combining the same prefix-tail inequality with Ridout's theorem (1957, *External input*: $|b^{m_j}\alpha - x'_{m_j}| \ge c(\alpha, b, \varepsilon) b^{-\varepsilon m_j}$ uniformly over integer prefixes $x'_{m_j} \in \mathbb{Z}$ for all $\varepsilon > 0$) yields $m_{j+1} \le (1 + \varepsilon) m_j + O_{\alpha, b, \varepsilon}(1)$ for every $\varepsilon > 0$, and hence $\sigma_{B_0}(\alpha; N) / \log N \to \infty$, $\sigma_N(\alpha) / \log N \to \infty$, and $\chi_N(\alpha) / \log N \to \infty$.

**(b) Rigorous barrier (signed-digit neutralization of convolution-borrow).** Unlike the nonnegative Hamming weight $s_2(2^{2N+1} - E_N) \ge N - 1$, the signed-digit (NAF) weight satisfies

```math
w_2^\pm(2^{2N+1} - E_N) \le 1 + w_2^\pm(E_N)
```

for every integer $E_N$, collapsing the entire $(N-1)$-bit borrow cascade to a single signed term $+2^{2N+1}$. Furthermore, by Theorem 2.1(3), shifting the carry gauge $\delta_{N+1}$ from $0$ to $-1$ removes the borrow cascade altogether. Explicitly, the integers $u_N = 2^N - 1$ ($N \ge 4$) satisfy $s_2(u_N) = s_2(u_N^2) = N$ while $w_2^\pm(u_N) = 2$ and $w_2^\pm(u_N^2) = 3$. Hence convolution-popcount bounds on $x_N^2$ cannot separate $\sigma_N(\sqrt{2}) \gg N^\delta$ from $\sigma_N = O(\log N)$.

*Proof.* (a) Write $k_0 = \alpha - \sum_{m \ge 0} a'_m b^{-m} \in \mathbb{Z}$. Since $a'_m = 0$ for $1 \le m < m_1$, $\|\alpha\| \le |\alpha - (k_0 + a'_0)| = |\sum_{r \ge m_1} a'_r b^{-r}| \le \frac{B_0}{b-1} b^{1 - m_1}$, which gives $b^{m_1 - 1} \le \frac{B_0}{(b-1)\|\alpha\|}$ and hence $m_1 \le M_1(\alpha, b)$ uniformly over all admissible $a'$. Next, for any $j \ge 1$, put $x'_{m_j} = (k_0 + a'_0) b^{m_j} + \sum_{r=1}^j a'_{m_r} b^{m_j - m_r} \in \mathbb{Z}$. Because $a'_m = 0$ for all $m_j < m < m_{j+1}$, the residual $T_{m_j} = b^{m_j}\alpha - x'_{m_j} = \sum_{r \ge m_{j+1}} a'_r b^{m_j - r}$ satisfies $|T_{m_j}| \le \frac{B_0}{b-1} b^{m_j - m_{j+1} + 1} \le \frac{B_0}{b-1} \le 1$. By Theorem 2.1(2) (which depends only on $x'_{m_j} \in \mathbb{Z}$), $1 \le |E'_{m_j}(\alpha; b)| = |T_{m_j}| \cdot |\sigma b^{m_j}\sqrt{\Delta} - A T_{m_j}| \le \frac{B_0 b}{b-1} b^{m_j - m_{j+1}} (b^{m_j}\sqrt{\Delta} + A) \le \frac{B_0 b}{b-1}(\sqrt{\Delta} + A) b^{2 m_j - m_{j+1}}$, so $b^{m_{j+1} - 2 m_j} \le \frac{B_0 b}{b-1}(\sqrt{\Delta} + A)$, giving $m_{j+1} \le 2 m_j + c_{\alpha, b}$. Inductively $m_k + c_{\alpha, b} \le 2^{k-1}(m_1 + c_{\alpha, b}) \le 2^{k-1}(M_1(\alpha, b) + c_{\alpha, b})$ for all $k \ge 1$. If $K = \#\{j \ge 1 : m_j \le N\}$, then $m_{K+1} \ge N + 1$ (valid both when $K \ge 1$ and when $K = 0$, since $m_1 \ge N + 1$ if $K = 0$), so $N + 1 + c_{\alpha, b} \le 2^K (M_1(\alpha, b) + c_{\alpha, b})$, yielding the displayed lower bound on $\sigma_{B_0}(\alpha; N)$ for every $N \ge 1$ (e.g., at $N = 1$ for $\sqrt{2}$ in base $2$, $\log_2(\frac{1+1+2}{2+2}) = 0 = \sigma_1(\sqrt{2}; 1)$). *P23-B3* Theorem 5.5(c) ($\chi_N \ge \sigma_{B_0} - 1$) transfers this to $\chi_N$, and minimizing over the finitely many quadratic translates $\alpha - c$ ($c \in F_b$) gives the same bound for $\sigma_N(\alpha)$. Under Ridout's theorem, for fixed $\alpha, b, \varepsilon > 0$ we have $b^{m_j - m_{j+1} + 1} \ge \frac{b-1}{B_0} |T_{m_j}| \ge c'(\alpha, b, \varepsilon) b^{-\varepsilon m_j}$ uniformly over $x'_{m_j} \in \mathbb{Z}$, so $m_{j+1} \le (1 + \varepsilon) m_j + C(\alpha, b, \varepsilon)$ for all $j \ge 1$; iterating gives $\sigma_{B_0}(\alpha; N) \ge (1 - o(1)) \frac{\log N}{\log(1 + \varepsilon)}$ for every $\varepsilon > 0$ (and likewise for $\sigma_N$ and $\chi_N$). (b) Subadditivity of $w_2^\pm$ gives $w_2^\pm(2^{2N+1} - E_N) \le w_2^\pm(2^{2N+1}) + w_2^\pm(E_N) = 1 + w_2^\pm(E_N)$, and $(2^N - 1)^2 = 2^{2N} - 2^{N+1} + 1$ has binary expansion $1^{N-1} 0^N 1$ ($s_2 = N$) and is already in NAF with weight $3$ for all $N \ge 4$. $\square$

Proving $\sigma_N(\sqrt{2}) \gg N^\delta$ (or $\chi_N(\sqrt{2}) \gg N^\delta$) for any $\delta > 0$ remains **Open** (matching Bugeaud's open problem on digit changes of algebraic irrationals; *External input* context).

### 2.4 Exponential-carry deficit barrier for binomial, Catalan, and Pell series

Consider the explicit integer-coefficient radix series for $\sqrt{2}, \sqrt{3}, \phi$ arising from $(1 \mp 4x)^{-1/2} = \sum_{k \ge 0} (\pm 1)^k \binom{2k}{k} x^k$ and $(1 \mp 4x)^{1/2} = 1 \mp 2 \sum_{k \ge 1} (\pm 1)^{k-1} C_{k-1} x^k$ (with Catalan numbers $C_n = \frac{1}{n+1}\binom{2n}{n}$):

```math
\sqrt{2} = \sum_{k \ge 0} \binom{2k}{k} 2^{-3k}
         = \sum_{k \ge 0} (-1)^k 3 \binom{2k}{k} 2^{-(5k+1)},
\qquad
5\sqrt{2} = 7 \sum_{k \ge 0} \binom{2k}{k} 200^{-k},
```

```math
\sqrt{3} = 2 - \sum_{k \ge 1} C_{k-1} 2^{-(4k-2)},
\qquad
\phi = \frac{3}{2} + \sum_{k \ge 1} (-1)^{k-1} C_{k-1} 2^{-(4k-1)}.
```

More generally, every Pell solution $p_r^2 - 2 q_r^2 = \epsilon \in \{+1, -1\}$ yields a Pell-accelerated binomial series

```math
q_r \sqrt{2} = p_r \left(1 + \frac{\epsilon}{2 q_r^2}\right)^{-1/2}
             = p_r \sum_{k \ge 0} (-\epsilon)^k \binom{2k}{k} (8 q_r^2)^{-k}
```

(for $(p, q) = (7, 5)$, $\epsilon = -1$ and $-\epsilon = +1$, giving $5\sqrt{2} = 7 \sum \binom{2k}{k} 200^{-k}$; for $(3, 2)$, $\epsilon = +1$ and $-\epsilon = -1$, giving $2\sqrt{2} = 3 \sum (-1)^k \binom{2k}{k} 32^{-k}$).

For an integer radix $b \ge 2$ and a nonzero integer $a$, write $v_b(a) = \max\{j \ge 0 : b^j \mid a\}$ and $u_b(a) = |a| / b^{v_b(a)}$ for the part remaining after stripping complete powers of $b$, and define the **radix-$b$ displaced digit width**

```math
W_{U, b}(N) = \sum_{\substack{1 \le m \le N \\ a(m) \ne 0}} \bigl(\lfloor \log_b u_b(a(m)) \rfloor + 1\bigr).
```

(For $b = 2$, $u_2(a) = \operatorname{odd}(|a|)$ and $W_{U, 2}(N)$ is the binary displaced bit-width.)

**Theorem 2.4 (Exponential-carry deficit barrier — Paper proof; finite certificate).** Let $\alpha = F_b(a) = \sum_{m \ge 0} a(m) b^{-m}$ be an integer series supported on a progression $m = s k + r_0$ ($s \ge 1$) with $|a(sk + r_0)| \asymp \lambda^k k^{-\gamma}$ ($1 < \lambda < b^s$, $\gamma \ge 0$), and put $\rho = (\log_b \lambda)/s \in (0, 1)$. Assume further that the nonzero coefficients $a(sk + r_0)$ satisfy either:
- **(i) eventual constant sign**, or
- **(ii) eventual alternating signs** with successive absolute weighted terms $t_k := |a(sk + r_0)| b^{-sk}$ obeying $t_{k+1}/t_k \to \lambda / b^s < 1$ (in particular $4 / b^s < 1$ for all five binomial/Catalan/Pell series above).

(Without a non-cancellation condition such as (i) or (ii), exact cancellation can occur: for example, adding $a(2j+1) = 2^j$, $a(2j+2) = -2^{j+1}$ to the canonical base-2 digits of $\sqrt{2}$ leaves the sum unchanged while making the added tail vanish at every even cut.)

1. *(Exponential canonical carry.)* By Theorem 2.1(1), $\delta_{n+1} = \lfloor T_n(a) \rfloor$ satisfies $|\delta_{n+1}| \asymp b^{\rho n} n^{-\gamma}$ for every large $n$, so the mean carry magnitude $\frac{1}{N} \sum_{n < N} |\delta_{n+1}|$ grows exponentially like $b^{\rho N} N^{-\gamma - 1}$ while $\theta_n = \{T_n(a)\} \in (0, 1)$.
2. *(Sharp linear raw-truncation window.)* Truncating $T_n(a) = \sum_{j=1}^L a(n+j) b^{-j} + R_{n,L}(a)$ gives $|R_{n,L}(a)| \asymp b^{\rho n - (1-\rho)L} (n+L)^{-\gamma}$. Bounding the **raw absolute truncation error** below any fixed tolerance $\varepsilon > 0$ ($|R_{n,L}(a)| < \varepsilon$, e.g. $\varepsilon = 1/2$) is equivalent to a linear lookahead window

```math
L(n) \ge \frac{\rho}{1 - \rho}\, n - \frac{\gamma}{1 - \rho} \log_b n - O_\varepsilon(1).
```

   *(Qualification: certifying a canonical digit $d_{n+1}$ directly from raw truncation requires an enclosure wholly inside a digit cell — even $|R_{n,L}| < 1/2$ can straddle a cell boundary — whereas arithmetic information about the tail modulo $1$ could in principle certify a digit by another method without shrinking $|R_{n,L}|$.)*

3. *(Quadratic radix-$b$ displaced width & Kummer survival.)* For all four dyadic series above ($b = 2$), Kummer's theorem gives $v_2(\binom{2k}{k}) = s_2(k) \le \log_2 k + 1$ and $v_2(C_{k-1}) = s_2(k-1) - v_2(k) \le \log_2 k + 1$, so stripping all powers of $2$ preserves the quadratic binary displaced width:

```math
W_{U, 2}(N) = \frac{\rho}{2 s} N^2 - O(N \log N).
```

   For the Pell series $q_r \sqrt{2} = p_r \sum_{k \ge 0} (-\epsilon)^k \binom{2k}{k} (8 q_r^2)^{-k}$ in radix $b = 8 q_r^2$ ($s = 1$, $\rho = \log_b 4 > 0$), stripping complete powers of $b$ satisfies $v_b(p_r \binom{2k}{k}) \le v_2(p_r \binom{2k}{k}) / v_2(b) \le s_2(k)/3 + O(1) = O(\log k)$, so the **radix-$b$ displaced width** satisfies $W_{U, b}(N) = \frac{\log_b 4}{2} N^2 - O(N \log N)$ (e.g. $\frac{\log_{200} 4}{2} \approx 0.1308$ at $b = 200$). By contrast, measuring the same coefficients in **binary** odd-part bit-width gives $\lfloor \log_2 \operatorname{odd}(p_r \binom{2k}{k}) \rfloor + 1 = 2k - O(\log k)$, so $W_{U, 2}(N) / N^2 \to 1$.

   Since $\sigma_N(\alpha) \le N$, the ratio $W_{U, b}(N) / \sigma_N(\alpha)$ grows **at least linearly**: $W_{U, b}(N) / \sigma_N(\alpha) \ge \frac{\rho}{2s} N - O(\log N)$ (with no matching upper bound supplied). Each named transfer theorem fails at a specific hypothesis on these series:
   - `GF-01` requires zero-density support $S(X) = o(X)$ and linear mass $A(X) = O(X)$; here $S(X) \sim X/s$ has positive density and $A(X) \asymp b^{\rho X} X^{-\gamma}$ grows exponentially.
   - `GF-02` requires sublinear displaced width $W_{U, b}(N) = o(N)$; here $W_{U, b}(N) \asymp N^2$.
   - `GF-13` requires polynomial or logarithmic mass ($A(X) \le C(X+1)^\kappa$ with $S(X) = o(X/\log X)$, or $A(X) \le C X (\log(X+2))^\gamma$ with $S(X) = o(X/\log\log X)$); both mass growth and sparsity fail.
   - `GF-17` requires polynomial mass $A(X) \le C X^\kappa$ or sublinear displaced width $W_{U, b}(N) = o(N)$; here mass is exponential and $W_{U, b}(N) \asymp N^2$.

   Moreover, quadratic signed width $W_\pm(N) \asymp N^2$ and exponential carry $|\delta_m| \asymp b^{\rho m}$ ($\rho \in (0, 1)$) are compatible with **both** $K_b$ membership and base-$b$ normality: *P23-B3* Proposition 5.7 constructs an element $\Lambda_b \in K_b$ via $\tilde{a}(m) = c(m) + \Delta(m+1) - b\Delta(m)$ with $c = \mathbf{1}_{\{2^s\}}$ and $\Delta(m) = R_{k(m)}/(b-1)$; replacing the seed $c$ by the canonical base-$b$ digit sequence $d(x_{\rm norm})$ of any base-$b$ normal number $x_{\rm norm}$ and setting $k(m) = (b-1)\lfloor \rho m / (2(b-1)) \rfloor$ yields $F_b(\tilde{a}) = x_{\rm norm}$ (by *P23-B3* Lemma 5.1, since $\sum_m b^{2k(m) - m} < \infty$), canonical carry $|\delta_m| = \Delta(m) \asymp b^{\rho m}$, and at every non-jump index (density $1 - \frac{\rho}{2(b-1)} > \frac{1}{2}$) signed weight $w_b^\pm(\tilde{a}(m)) = w_b^\pm(d_m - R_{k(m)}) \ge k(m) - 2$ (by *P23-B3* Lemma 5.6 and subadditivity, since $w_b^\pm(d_m) \le 2$ for $b \ge 2$), hence $W_\pm(N) \asymp N^2$.

| Series | Radix $b$ | Step $s$ | $\rho = \frac{\log_b 4}{s}$ | Raw-truncation window $L(n)$ | Radix-$b$ width $W_{U,b}(N) / N^2$ | Finite check ($N = 300$) |
| --- | --- | --- | --- | --- | --- | --- |
| $\sqrt{2} = \sum \binom{2k}{k} 2^{-3k}$ | $2$ | $3$ | $2/3$ | $\ge 2n - \frac{3}{2}\log_2 n - O(1)$ | $1/9 \approx 0.1111$ | $0.1054$ |
| $\sqrt{2} = \sum (-1)^k 3 \binom{2k}{k} 2^{-(5k+1)}$ | $2$ | $5$ | $2/5$ | $\ge \frac{2}{3}n - \frac{5}{6}\log_2 n - O(1)$ | $1/25 = 0.0400$ | $0.0368$ |
| $\sqrt{3} = 2 - \sum C_{k-1} 2^{-(4k-2)}$ | $2$ | $4$ | $1/2$ | $\ge n - 3\log_2 n - O(1)$ | $1/16 = 0.0625$ | $0.0537$ |
| $\phi = \frac{3}{2} + \sum (-1)^{k-1} C_{k-1} 2^{-(4k-1)}$ | $2$ | $4$ | $1/2$ | $\ge n - 3\log_2 n - O(1)$ | $1/16 = 0.0625$ | $0.0537$ |
| $5\sqrt{2} = 7 \sum \binom{2k}{k} 200^{-k}$ | $200$ | $1$ | $\log_{200} 4 \approx 0.2616$ | $\ge 0.354 n - O(\log n)$ | $\frac{\log_{200} 4}{2} \approx 0.1308$ (binary $W_{U,2}/N^2 \to 1$) | $0.1310$ (binary $0.9872$) |

*Proof.* (1)–(2) The first omitted term in $R_{n,L}(a) = \sum_{j > L} a(n+j) b^{-j}$ has index $k_0 = \lfloor (n + L - r_0)/s \rfloor + 1$, so $m_0 = s k_0 + r_0 \in [n + L + 1, n + L + s]$ and $b^{r_0 - n} R_{n,L}(a) = \sum_{k \ge k_0} \operatorname{sign}(a(sk+r_0)) t_k$. Under (i), all terms for large $k_0$ share one sign and $t_k \asymp (\lambda/b^s)^k k^{-\gamma}$ with $\lambda/b^s < 1$, so $t_{k_0} \le b^{r_0 - n} |R_{n,L}(a)| \ll t_{k_0}$. Under (ii), for large $k_0$ the magnitudes $t_k$ decrease strictly with $t_{k+1}/t_k \to \lambda/b^s < 1$, so the alternating-series bracket gives $t_{k_0} - t_{k_0+1} \le b^{r_0 - n} |R_{n,L}(a)| \le t_{k_0}$, whence $b^{r_0 - n} |R_{n,L}(a)| \asymp t_{k_0}$ with explicit lower factor $1 - \lambda/b^s - o(1) > 0$. Since $s k_0 + r_0 = n + L + O(1)$, $t_{k_0} b^{n - r_0} \asymp \lambda^{(n+L)/s} b^{-L} (n+L)^{-\gamma} = b^{\rho n - (1-\rho)L} (n+L)^{-\gamma}$. Setting $L = 0$ gives (1), and requiring $|R_{n,L}(a)| < \varepsilon$ gives $(1-\rho)L \ge \rho n - \gamma \log_b n - O_\varepsilon(1)$, proving (2). (3) Summing $\log_b u_b(a(sk+r_0)) = \rho s k - O(\log k)$ over $1 \le k \le \lfloor N/s \rfloor$ gives $\frac{\rho s}{2} (N/s)^2 - O(N \log N) = \frac{\rho}{2s} N^2 - O(N \log N)$. For Pell convergents $p_r/q_r$ of $\sqrt{2}$, $|\sqrt{2} - p_r/q_r| \sim (2\sqrt{2} q_r^2)^{-1}$ controls a **real distance** of order $q_r^{-2}$ (precision $\approx 2 \log_2 q_r + O(1)$ bits against period $\operatorname{ord}_{\operatorname{odd}(q_r)}(2)$, e.g., at $r = 14$, $q_{14} = 80{,}782$, real precision $34.1$ bits against period $18{,}564$, illustrating the `CC-50` window–denominator barrier at $\mu = 2$; note that deducing identical individual binary prefix bits between $\sqrt{2}$ and $p_r/q_r$ additionally requires a binary endpoint check verifying that no dyadic rational separates them at that scale). $\square$

---

## 3. Sub-track E3: Classical Lambert & $E$/$E_+$ obstruction map

This section maps the exact quantitative transition in the dyadic Lambert family $E(2^k)$, $E_{\rm odd}(2^k)$, and $E_+(2^k)$ as $k$ decreases from $k \ge 3$ ($b \ge 8$, where zero-carry digit-mass and NAF-weight methods unconditionally establish nonnormality) down to $k = 2$ ($b = 4$) and $k = 1$ ($b = 2$, the benchmark targets `BC-37`–`BC-39`).

### 3.1 Certified popcount & NAF means and binary/NAF carry-balance inequalities

Because $\operatorname{odd}(v_p(n) + 1) = 1$ whenever $v_p(n) \le 1$, the odd part $U_{\rm odd}(n) = \prod_{p > 2} \operatorname{odd}(v_p(n) + 1)$ of $\tau_{\rm odd}(n)$ depends only on the odd squarefull part of $n$, while $\operatorname{odd}(\tau(n)) = \operatorname{odd}(v_2(n) + 1) U_{\rm odd}(n)$ and (for $v_2(n) \ne 1$) $\operatorname{odd}(|a_+(n)|) = \operatorname{odd}(|1 - v_2(n)|) U_{\rm odd}(n)$ (with $a_+(n) = 0$ when $v_2(n) = 1$). Write $U_{\rm odd} = \prod_{p > 2} \operatorname{odd}(B_p + 1)$, where $B_p$ are independent geometric random variables with $\Pr(B_p = e) = (1 - p^{-1}) p^{-e}$ ($e \ge 0$).

**Theorem 3.1 (Paper proof + finite certificate).**

**(a) Unconditional existence and certified outward-rounded enclosures.** For every function $f : \mathbb{Z}_{\ge 0} \to \mathbb{R}_{\ge 0}$ satisfying $f(0) = 0$, $f(2u) = f(u)$ for all $u \ge 1$ (so $f(u) = f(\operatorname{odd}(u))$ for $u \ge 1$), and $0 \le f(u) \le u$ for all $u \ge 1$ — in particular the binary popcount $s_2$ and NAF weight $w_2^\pm$ — the limiting means $\mu_f(\tau) = \lim_{X \to \infty} \frac{1}{X} \sum_{n \le X} f(\tau(n))$ (and analogously for $\tau_{\rm odd}$ and $|a_+|$) exist unconditionally and equal

```math
\mu_f(\tau_{\rm odd}) = \mathbb{E}[f(U_{\rm odd})], \qquad
\mu_f(\tau) = \sum_{e \ge 0} 2^{-(e+1)} \mathbb{E}\bigl[f(\operatorname{odd}(e+1) U_{\rm odd})\bigr],
```

```math
\mu_f(|a_+|) = \frac{1}{2} \mathbb{E}[f(U_{\rm odd})] + \sum_{e \ge 2} 2^{-(e+1)} \mathbb{E}\bigl[f(\operatorname{odd}(e-1) U_{\rm odd})\bigr].
```

Using exact rational arithmetic over primes $3 \le p \le 600$ ($u \le 512$, $e < 24$), submultiplicativity $f(uv) \le f(u) f(v)$ for $f \in \{s_2, w_2^\pm\}$, and rigorous tail bounds for $p > 600$ (`scripts/phase24_classical.py`), we certify the outward-rounded rational enclosures (including outward rounding after division by $3$):

| Constant | Certified rational enclosure | Divided by $k = 3$ | Threshold |
| --- | --- | --- | --- |
| $\mu_{\rm pop}(\tau_{\rm odd})$ | $[1.159430,\, 1.166471]$ | $[0.386476,\, 0.388824]$ | $< 1/2$ (**pass**) |
| $\mu_{\rm pop}(\tau)$ | $[1.337765,\, 1.346123]$ | $[0.445921,\, 0.448708]$ | $< 1/2$ (**pass**) |
| $\mu_{\rm pop}(|a_+|)$ | $[0.914156,\, 0.919767]$ | $[0.304718,\, 0.306589]$ | (signed: $s_2$ not subadditive) |
| $\mu_{\rm NAF}(\tau)$ | $[1.315644,\, 1.323936]$ | $[0.438548,\, 0.441312]$ | $< 1/3$ at $k \ge 4$ |
| $\mu_{\rm NAF}(a_+)$ | $[0.907252,\, 0.912845]$ | $[0.302417,\, 0.304282]$ | $< A_{16} = 0.30902767\ldots < 1/3$ (**pass**) |

**(b) Binary carry-balance upper bound for nonnegative $E(2^k)$ and $E_{\rm odd}(2^k)$.** For $c \in \{\tau, \tau_{\rm odd}\}$, $k \ge 1$, and $M \ge 1$, set $F = F_{2^k}(c)$, $S_M = \sum_{n=1}^M c(n) 2^{k(M-n)}$, and let $C_{\rm bin}(k, M) \ge 0$ be the exact total number of binary carries in summing the $M$ nonnegative integers $c(n) 2^{k(M-n)}$. Then the partial sum satisfies the exact finite identity $s_2(S_M) + C_{\rm bin}(k, M) = \sum_{n=1}^M s_2(c(n))$, and writing $\lfloor 2^{kM} F \rfloor = S_M + t_M$ ($0 \le t_M = O(\sqrt{M})$) yields the upper bound

```math
s_2\bigl(\lfloor 2^{kM} F \rfloor\bigr) \le s_2(S_M) + s_2(t_M) \le \sum_{n=1}^M s_2(c(n)) - C_{\rm bin}(k, M) + O(\log M).
```

Setting $\bar{c}_{k, M} = C_{\rm bin}(k, M)/(kM) \ge 0$, removing the fixed integer part $\lfloor F \rfloor$ ($O(1)$ bits), and using that adjacent multiples of $k$ differ by at most $k$ bits gives

```math
f_{1, kM}\bigl(F_{2^k}(c); 2\bigr) + \bar{c}_{k, M} \le \frac{1}{kM} \sum_{n=1}^M s_2(c(n)) + O\!\left(\frac{\log M}{M}\right), \qquad
\limsup_{N \to \infty} f_{1, N}\bigl(F_{2^k}(c); 2\bigr) + \liminf_{M \to \infty} \bar{c}_{k, M} \le \frac{\mu_{\rm pop}(c)}{k}.
```

(A two-sided equality is not claimed here: adding $t_M = O(\sqrt{M})$ to $S_M$ can trigger a carry chain destroying arbitrarily many ones — as in $(2^j - 1) + 1 = 2^j$ — without a separate carry-length estimate.) Since $\bar{c}_{k, M} \ge 0$, every $k \ge 3$ satisfies $\limsup_N f_{1, N}(E(2^k); 2) \le \frac{\mu_{\rm pop}(\tau)}{k} \le 0.448708 < \frac{1}{2}$ and $\limsup_N f_{1, N}(E_{\rm odd}(2^k); 2) \le \frac{\mu_{\rm pop}(\tau_{\rm odd})}{k} \le 0.388824 < \frac{1}{2}$. In particular, **$E(2^k)$ and $E_{\rm odd}(2^k)$ are simply nonnormal in base $2$ and (by grouping bits) in base $2^k$, with $D^-(E(2^k); 2) \ge \frac{1}{2} - \frac{\mu_{\rm pop}(\tau)}{k} \ge 0.05129$, for every $k \ge 3$.**

**(c) Exact NAF carry-balance inequality for signed $E_+(2^k)$.** For every $k \ge 1$ and $N_0 \ge 1$, set $H = \lceil \frac{2}{k} \log_2(N_0 + 2) \rceil + 4$ and $M = N_0 + H$, and let $S_M^+ = \sum_{n=1}^M a_+(n) 2^{k(M-n)}$. Then

```math
\sigma_1\bigl(E_+(2^k); k N_0\bigr) \le w_2^\pm(S_M^+) \le \sum_{n=1}^M w_2^\pm(a_+(n)), \qquad
\limsup_{N \to \infty} \frac{\sigma_1(E_+(2^k); N)}{N} \le \frac{\mu_{\rm NAF}(a_+)}{k}.
```

*Proof.* (a) For each $c \in \{\tau_{\rm odd}, \tau, |a_+|\}$, write the 2-adic odd-part multiplier separately as $o_2^{(c)}(e) = 1$ for $c = \tau_{\rm odd}$, $\operatorname{odd}(e+1)$ for $c = \tau$, and $\mathbf{1}_{e \ne 1}\operatorname{odd}(|1 - e|)$ for $c = |a_+|$, and set $U_c(n) = o_2^{(c)}(v_2(n)) U_{\rm odd}(n)$ (so $f(|c(n)|) = f(U_c(n))$ for every $n \ge 1$, since $f(0) = 0$ and $f(2u) = f(u)$). Fix parameters $P \ge 3$ and $K \ge 2$, and define the **periodic** event $B_{P,K} = \{v_p(n) < K \text{ for all } p \le P\}$ and the finite-prime truncated observables

```math
U_c^{(P,K)}(n) = o_2^{(c)}(v_2(n)) \Bigl(\prod_{2 < p \le P} \operatorname{odd}(v_p(n) + 1)\Bigr) \mathbf{1}_{B_{P,K}}(n), \qquad
g_{P,K}(n) = f\bigl(U_c^{(P,K)}(n)\bigr) \mathbf{1}_{B_{P,K}}(n).
```

Both $U_c^{(P,K)}$ and $g_{P,K}$ are periodic modulo $\prod_{p \le P} p^K$, so **finite CRT** gives their exact limiting means $\mathbb{E}[U_c^{(P,K)}]$ and $\mathbb{E}[f(o_2^{(c)}(B_2) U_{\rm odd}^{(P)}) \mathbf{1}_{B_p < K \,\forall p \le P}]$ under independent geometric $B_p \sim \operatorname{Geom}(1 - p^{-1})$ (note that the squarefull-free event $A_{P,K} = B_{P,K} \cap \{v_p(n) \le 1\ \forall p > P\}$ is generally aperiodic, so CRT is applied to $g_{P,K}$ and $U_c^{(P,K)}$, not to $\mathbf{1}_{A_{P,K}}$). Pointwise for every $n \ge 1$:
- if $n \notin B_{P,K}$, then $g_{P,K}(n) = U_c^{(P,K)}(n) = 0$, so $|f(|c(n)|) - g_{P,K}(n)| = f(U_c(n)) \le U_c(n) \le 2(U_c(n) - U_c^{(P,K)}(n))$;
- if $n \in B_{P,K}$ and $U_{\rm odd}^{(> P)}(n) := \prod_{p > P} \operatorname{odd}(v_p(n) + 1) = 1$ (which holds on all of $A_{P,K}$), then $U_c(n) = U_c^{(P,K)}(n)$ and $|f(|c(n)|) - g_{P,K}(n)| = 0$;
- if $n \in B_{P,K}$ and $U_{\rm odd}^{(> P)}(n) \ge 3$, then $U_c(n) \ge 3 U_c^{(P,K)}(n)$, so $|f(|c(n)|) - g_{P,K}(n)| \le U_c(n) + U_c^{(P,K)}(n) \le 2(U_c(n) - U_c^{(P,K)}(n))$.

Writing $U_c = 1 * h_c$ by Dirichlet convolution, $h_c(p) = 0$ for every odd prime $p$ and $|h_c(p^e)| \le e + 1$ for all $p, e$, so $\sum_{d \ge 1} |h_c(d)| d^{-\sigma} < \infty$ for every $\sigma > \frac{1}{2}$; hence $\frac{1}{X} \sum_{n \le X} U_c(n) = \mathbb{E}[U_c] + O_\varepsilon(X^{-1/2 + \varepsilon})$ unconditionally for each of the three choices of $c$, with $\mathbb{E}[U_c] = \mathbb{E}[o_2^{(c)}(B_2)] \prod_{p > 2} L_p < \infty$ (where $L_p = 1 + (1-p^{-1})\sum_{e \ge 2}(\operatorname{odd}(e+1) - 1) p^{-e}$; compare *P22-E* Proposition 1.4). Averaging the pointwise bound gives

```math
\limsup_{X \to \infty} \left|\frac{1}{X} \sum_{n \le X} f(|c(n)|) - \mathbb{E}\bigl[f(o_2^{(c)}(B_2) U_{\rm odd}^{(P)}) \mathbf{1}_{B_p < K \,\forall p \le P}\bigr]\right|
  \le 2\Bigl(\mathbb{E}[U_c] - \mathbb{E}\bigl[U_c^{(P,K)}\bigr]\Bigr).
```

Taking the iterated limit $K \to \infty$ first (monotone in $K$ for fixed $P$) and then $P \to \infty$ — or equivalently applying dominated convergence directly for the joint limit $(P, K) \to (\infty, \infty)$ using the integrable dominator $U_c$ (since almost surely only finitely many odd primes have $B_p \ge 2$ and every $B_p < \infty$, so $U_c^{(P, K)} \to U_c$ almost surely with $0 \le U_c^{(P, K)} \le U_c$) — yields $\mathbb{E}[U_c^{(P,K)}] \to \mathbb{E}[U_c]$ and $\mathbb{E}[f(o_2^{(c)}(B_2) U_{\rm odd}^{(P)}) \mathbf{1}_{B_p < K \,\forall p \le P}] \to \mathbb{E}[f(o_2^{(c)}(B_2) U_{\rm odd})]$, proving the three exact mean formulas.

For the certified enclosures at $P = 600$, for each retained prime $p \le 600$ the omitted first moment from $e \ge K$ is bounded by $\sum_{e \ge K} (e+1)(1-p^{-1})p^{-e} = p^{-K}(K + \frac{p}{p-1})$, and the two omitted 2-adic tails ($e \ge K_2 = 24$) are bounded by $(K_2 + 2) 2^{-K_2}$ (for $\tau$) and $K_2 2^{-K_2}$ (for $|a_+|$). For the infinite prime tail $p > P = 600$:
- Convexity of $x^{-2}$ on intervals of length $2$ centered at odd integers gives $\Pr(A_P^c) \le \sum_{p > 600} p^{-2} \le \sum_{m \ge 301} (2m-1)^{-2} < \frac{1}{2} \int_{600}^\infty x^{-2}\, dx = \frac{1}{2P}$.
- Each local first moment satisfies $L_p \le 1 + (1 - p^{-1})\sum_{e \ge 2} e p^{-e} = 1 + \frac{2p-1}{p^2(p-1)} < 1 + \frac{2}{p(p-1)}$. Summing the telescoping identity $\frac{2}{(m-2)m} = \frac{1}{m-2} - \frac{1}{m}$ over odd $m \ge 601$ and omitting the composite $m = 603$ gives

```math
\sum_{p > 600} \frac{2}{p(p-1)}
  \le \sum_{\substack{m \ge 601\text{ odd} \\ m \ne 603}} \frac{2}{(m-2)m}
  = \frac{1}{599} - \frac{2}{601 \cdot 603} < \frac{1}{600} = \frac{1}{P}.
```
- Therefore $\prod_{p > P} L_p \le \exp(1/P) \le 1 + 2/P$ (using $e^t \le 1 + 2t$ on $[0, 1]$), while $\prod_{p > P} (1 - p^{-2}) \ge 1 - \frac{1}{2P}$; subtracting yields $\mathbb{E}[U_{\rm odd} \mathbf{1}_{A_P^c}] \le \mathbb{E}[U_{\rm odd}^{(\le P)}] \cdot \frac{5}{2P}$.

For both $f \in \{s_2, w_2^\pm\}$, multiplying the base-2 or NAF representations of $o_2$ and $u$ term-by-term and normalizing shows $f(o_2 u) \le f(o_2) f(u) \le f(o_2) u$, controlling the truncated tail and yielding the certified outward-rounded rational intervals in `scripts/phase24_classical.py`.

(b) Applying Theorem 2.2(1) at $b = 2$ to the nonnegative shifted summands $c(n) 2^{k(M-n)}$ gives the exact finite identity $s_2(S_M) + C_{\rm bin}(k, M) = \sum_{n=1}^M s_2(c(n))$. Write $\lfloor 2^{kM} F \rfloor = S_M + t_M$, where $0 \le t_M = \lfloor \sum_{n > M} c(n) 2^{k(M-n)} \rfloor \le \sum_{j \ge 1} 2\sqrt{M + j}\, 2^{-kj} = O(\sqrt{M})$, so $s_2(t_M) = O(\log M)$. Subadditivity $s_2(S_M + t_M) \le s_2(S_M) + s_2(t_M)$ gives $s_2(\lfloor 2^{kM} F \rfloor) \le \sum_{n=1}^M s_2(c(n)) - C_{\rm bin}(k, M) + O(\log M)$. Removing the fixed integer part $\lfloor F \rfloor$ costs $O(1)$ bits, and for arbitrary $N$ letting $M = \lfloor N/k \rfloor$ changes the prefix by at most $k$ bits, yielding $\limsup_N f_{1, N}(F; 2) \le \lim_M \frac{1}{kM} \sum_{n=1}^M s_2(c(n)) - \liminf_M \bar{c}_{k, M} = \frac{\mu_{\rm pop}(c)}{k} - \liminf_M \bar{c}_{k, M}$. Simple normality in base $2^k$ implies simple normality in base $2$ by grouping bits (the base-2 digit-1 frequency is $\frac{1}{k}$ times the average binary popcount of the base-$2^k$ digits), and $|f_{1, N}(x; 2) - \frac{1}{2}| \le D_N(x; 2)$ gives $D^-(E(2^k); 2) \ge \frac{1}{2} - \frac{\mu_{\rm pop}(\tau)}{k} \ge 0.05129$ for every $k \ge 3$.

(c) Write $S_M^+$ in NAF: $S_M^+ = \sum_{j \ge 0} \epsilon_j 2^j$ ($\epsilon_j \in \{-1, 0, 1\}$, no two adjacent nonzero, weight $w_2^\pm(S_M^+)$). Put $N = k N_0$ and $M = N_0 + H$ with $H = \lceil \frac{2}{k} \log_2(N_0 + 2) \rceil + 4$. For every $N_0 \ge 1$ and $k \ge 1$:
- $H < \frac{2}{k} \log_2(N_0 + 2) + 5 \le 2 \log_2(N_0 + 2) + 5 \le 2(N_0 + 1) + 5 = 2 N_0 + 7$, and $2^{kH} \ge 16 (N_0 + 2)^2$;
- using $|a_+(n)| \le \tau(n) \le 2\sqrt{n} \le 2n$, in units of the cut bit $2^{-N}$ the omitted series tail satisfies

```math
\left|2^N \sum_{n > M} a_+(n) 2^{-kn}\right|
  \le 2^{-kH} \sum_{j \ge 1} 2(M + j) 2^{-j}
  = 2(M + 2) 2^{-kH}
  \le \frac{2(3 N_0 + 9)}{16 (N_0 + 2)^2} < \frac{1}{4},
```

  since $3 N_0 + 9 < 2(N_0 + 2)^2$ for every $N_0 \ge 1$;
- the finite low NAF sum ($0 \le j < kH$) in units of $2^{-N}$ is strictly smaller than its infinite geometric majorant $\sum_{i \ge 0} 2^{-1-2i} = \frac{2}{3}$.

Hence the combined residual $r = 2^N E_+(2^k) - \sum_{j \ge kH} \epsilon_j 2^{j - kH}$ lies strictly inside $(-\frac{11}{12}, \frac{11}{12}) \subset (-1, 1)$, so $r$ admits a signed binary tail $\sum_{t \ge 1} \eta_t 2^{-t}$ ($\eta_t \in \{-1, 0, 1\}$). Retaining the high NAF digits $\epsilon_j$ ($j \ge kH$) on fractional positions $[1, N]$, discarding integer positions modulo $1$, and appending this signed binary tail exhibits an admissible signed-digit representation $a' \sim d(E_+(2^k))$ with $|a'| \le 1$ and prefix support at most $w_2^\pm(S_M^+)$ on $[1, N]$, even when the residual crosses a canonical prefix boundary. By subadditivity of $w_2^\pm$, $\sigma_1(E_+(2^k); k N_0) \le w_2^\pm(S_M^+) \le \sum_{n=1}^M w_2^\pm(a_+(n))$. For arbitrary $N \ge 1$, rounding $N$ up to $k N_0$ with $N_0 = \lceil N/k \rceil$ and using monotonicity $\sigma_1(E_+(2^k); N) \le \sigma_1(E_+(2^k); k N_0)$ yields $\limsup_{N \to \infty} \sigma_1(E_+(2^k); N)/N \le \mu_{\rm NAF}(a_+)/k$ (as the $H = O(\log N_0)$ extra terms contribute $O((\log N_0)^2/N_0) \to 0$). $\square$

### 3.2 Minimized 4-state NAF automaton and unconditional nonnormality of $E_+(2^k)$ ($k \ge 3$)

To convert Theorem 3.1(c) into an unconditional nonnormality theorem for $E_+(2^k)$, we compute the exact free-boundary minimal signed-digit weight of length-$L$ binary words using the 3-state transducer of *P23-B3* Theorem 5.5.

For $w = w_1 \cdots w_L \in \{0, 1\}^L$, define the **free-boundary minimal signed-digit weight**

```math
\sigma_{\rm free}(w) = \min_{\substack{\delta_0, \dots, \delta_L \in \{-1, 0, 1\} \\ |w_i + 2\delta_{i-1} - \delta_i| \le 1}} \#\{1 \le i \le L : w_i + 2\delta_{i-1} - \delta_i \ne 0\}.
```

**Theorem 3.2 (Paper proof + finite certificate).**

**(a) Exact 4-state minimization and closed formula.** Tracking the normalized min-plus DP vector $v - \min(v) \in \mathbb{Z}_{\ge 0}^3$ from initial state $(0, 0, 0)$ closes under both bit transitions at **exactly $7$ reachable vectors**, which lump by identical transition-and-cost behavior into a minimal **4-state deterministic transducer** $\{A, B, C, D\}$:

| State | Lumped DP vectors | On bit `0`: (next, cost) | On bit `1`: (next, cost) | Stationary weight $\pi$ |
| --- | --- | --- | --- | --- |
| $A$ (start) | $\{(0,0,0), (0,0,1)\}$ | $(C,\, 0)$ | $(B,\, 0)$ | $1/6$ |
| $B$ | $\{(0,1,0), (0,1,1)\}$ | $(A,\, 1)$ | $(B,\, 0)$ | $1/3$ |
| $C$ | $\{(1,0,0), (1,0,1)\}$ | $(C,\, 0)$ | $(D,\, 0)$ | $1/3$ |
| $D$ | $\{(1,1,0)\}$ | $(C,\, 1)$ | $(B,\, 1)$ | $1/6$ |

For every integer $L \ge 1$, the uniform average $A_L = \frac{1}{L \cdot 2^L} \sum_{w \in \{0, 1\}^L} \sigma_{\rm free}(w)$ is given by the exact closed formula

```math
A_L = \frac{1}{3} - \frac{7 - (-1/2)^{L-1}}{18 L}.
```

**(b) Normal-number NAF floor and quantitative discrepancy bound.** Put $s_N = \sigma_1(x; N)/N$. For every real $x$ and every $L \ge 1$,

```math
\liminf_{N \to \infty} s_N \ge A_L \bigl(1 - 2^L D^+(x; 2)\bigr), \qquad
\limsup_{N \to \infty} s_N \ge A_L \bigl(1 - 2^L D^-(x; 2)\bigr).
```

In particular:
1. Every base-2 normal number has $D_N(x; 2) \to 0$ (hence $D^+(x; 2) = 0$), so the **first** inequality and $L \to \infty$ yield the universal floor $\liminf_{N \to \infty} \sigma_1(x; N)/N \ge \frac{1}{3}$.
2. Any real $x$ with $\limsup_{N \to \infty} \sigma_1(x; N)/N \le \alpha < A_L$ satisfies, by the **second** inequality,

```math
D^-(x; 2) \ge \frac{A_L - \alpha}{2^L A_L} > 0,
```

   so $x$ is **nonnormal in base $2$ and in every base $2^k$ ($k \ge 1$)**.

**(c) Application to $E_+(2^k)$ ($k \ge 3$).** Taking $L = 16$ gives $A_{16} = \frac{324039}{1048576} = 0.30902767\ldots$, while Theorem 3.1(a),(c) certifies $\limsup_{N \to \infty} \sigma_1(E_+(2^k); N)/N \le \mu_{\rm NAF}(a_+)/k \le \mu_{\rm NAF}(a_+)/3 \le 0.304282 < A_{16}$. Therefore, for every integer $k \ge 3$, **$E_+(2^k)$ is nonnormal in base $2$ and in base $2^k$, with explicit lower extreme discrepancy**

```math
D^-(E_+(2^k); 2) \ge \frac{A_{16} - \mu_{\rm NAF}(a_+)/k}{2^{16} A_{16}} \ge 2.34 \times 10^{-7} > 0.
```

Simple nonnormality of $E_+(8)$ in base $2$ remains **open**.

*Proof.* (a) Direct closure of the determinized 3-state transitions $\delta \xrightarrow{b} \delta'$ ($a = b + 2\delta - \delta' \in \{-1, 0, 1\}$) from $(0,0,0)$ yields exactly the $7$ normalized vectors and the 4-state lumping in the table (certified exhaustively by transition-table closure in `scripts/phase24_classical.py`, which proves the quotient for all $L \ge 1$; the script separately runs finite cross-checks of $A_L$ for $1 \le L \le 20$ and brute-force word enumeration for $L \le 10$). The four classes are minimal for deterministic word cost: immediate step costs on `(0, 1)` are `(0,0)` for $A, C$, `(1,0)` for $B$, and `(1,1)` for $D$, while the suffix `11` costs `0` from $A$ and `1` from $C$. Under i.i.d. uniform bits, let $p_t = (a_t, b_t, c_t, d_t)$ be the distribution after $t$ steps from $p_0 = (1, 0, 0, 0)$. The transitions give $p_1 = (0, \frac{1}{2}, \frac{1}{2}, 0)$, and inductively for all $t \ge 1$: $a_t = d_t$, $b_t = c_t = \frac{1}{2} - a_t$, with $a_{t+1} = \frac{1}{2} b_t = \frac{1}{4} - \frac{1}{2} a_t$. Solving with $a_1 = 0$ yields $a_t = \frac{1}{6}(1 - (-\frac{1}{2})^{t-1})$ for $t \ge 1$ (stationary weights $(\frac{1}{6}, \frac{1}{3}, \frac{1}{3}, \frac{1}{6})$). The expected cost at step $t + 1$ is $\frac{1}{2} b_t + d_t = \frac{1}{4} + \frac{1}{2} a_t = \frac{1}{3} - \frac{1}{12}(-\frac{1}{2})^{t-1}$ for $t \ge 1$ (and $0$ at $t = 0$). Summing from $t = 0$ to $L - 1$ gives

```math
\mathbb{E}[\sigma_{\rm free}(W_L)] = \frac{L - 1}{3} - \frac{1}{18}\left(1 - \left(-\frac{1}{2}\right)^{L-1}\right) = \frac{L}{3} - \frac{7 - (-1/2)^{L-1}}{18}.
```

Dividing by $L$ gives $A_L$.

(b) For any optimal path $\delta_0, \dots, \delta_N$ attaining $\sigma_1(x; N)$, restricting the path to any wholly contained contiguous length-$L$ word $w = d_{m+1} \cdots d_{m+L}$ costs at least $\sigma_{\rm free}(w)$. Summing over all starts counts each paid position at most $L$ times (and including the final $L - 1$ starts costs at most $L/N$ in the normalized bound), giving $s_N \ge \frac{1}{L} \sum_{w \in \{0,1\}^L} \sigma_{\rm free}(w) f_N(w) - \frac{L}{N}$, where $f_N(w)$ is the empirical frequency of $w$. Since each cylinder $I_w$ is a half-open interval of length $2^{-L}$, $f_N(w) \ge 2^{-L} - D_N(x; 2)$, so

```math
s_N \ge A_L - \left(\frac{1}{L} \sum_{w \in \{0,1\}^L} \sigma_{\rm free}(w)\right) D_N(x; 2) - \frac{L}{N} = A_L\bigl(1 - 2^L D_N(x; 2)\bigr) - \frac{L}{N}.
```

Taking $\liminf_{N \to \infty}$ on both sides (using $\liminf(-D_N) = -D^+$) yields the first inequality $\liminf s_N \ge A_L(1 - 2^L D^+)$. Taking a subsequence $(N_j)$ along which $D_{N_j}(x; 2) \to D^-(x; 2)$ yields $\limsup s_N \ge \liminf_j s_{N_j} \ge A_L(1 - 2^L D^-(x; 2))$, which is the second inequality. (Note that $\liminf s_N \ge A_L(1 - 2^L D^-)$ is false in general, as shown by alternating long zero blocks with repetitions of binary de Bruijn cycles of growing order.) If $x$ is base-2 normal, $D^+(x; 2) = 0$ and the first inequality with $L \to \infty$ gives $\liminf s_N \ge \frac{1}{3}$. If $\limsup s_N \le \alpha < A_L$, the second inequality gives $D^-(x; 2) \ge (A_L - \alpha)/(2^L A_L) > 0$; equivalence of normality in base $2$ and base $2^k$ (Maxfield 1953, *External input*) transfers full nonnormality to every base $2^k$.

(c) Immediate from (b) and Theorem 3.1(a),(c), using the exact outward-rounded upper endpoint $\mu_{\rm NAF}(a_+)/3 \le 0.304282 < A_{16}$ (exact rational lower bound $(A_{16} - \mu_{\rm hi}/3)/(2^{16} A_{16}) = 2.3434\ldots \times 10^{-7} \ge 2.34 \times 10^{-7}$). $\square$

### 3.3 Exact finite-term reduction of $C_+(h; X)$ eliminating Hypothesis (H2)

In *P23-E* Theorem 2.2(2) and Theorem 3.1(3), the two-point signed divisor correlation $C_+(h; X) = \frac{1}{X} \sum_{n \le X} a_+(n) a_+(n+h) \sim \rho(h) \frac{6}{\pi^2} \sigma_{-1}(h) \log^2 X$ and the off-diagonal tail constant $\mathrm{Off}_X(a_+) \sim \kappa_+ \log^2 X$ were conditional on an infinite family of congruence hypotheses **(H2)** modulo $2^K$ ($K \to \infty$). We now eliminate **(H2)** completely via exact 3-term and 4-term finite identities combined with Topacogullari's affine additive divisor theorem and *P23-E* Lemma 3.2.

**Theorem 3.3 (Paper proof; finite certificate; asymptotic corollary uses Topacogullari 2017 Theorem 1.2 as External input).** For every positive integer $X$ and every shift $h \ge 1$:

1. *(Odd $h$.)*

```math
\sum_{n=1}^X a_+(n) a_+(n+h)
  = \sum_{n=1}^X \tau(n) \tau(n+h)
    - 2 \sum_{1 \le m \le \lfloor X/2 \rfloor} \tau(m) \tau(2m + h)
    - 2 \sum_{(h+1)/2 \le m \le \lfloor (X+h)/2 \rfloor} \tau(2m - h) \tau(m).
```

2. *(Even $h = 2 h'$, all $X \ge 1$.)*

```math
\sum_{n=1}^X a_+(n) a_+(n + 2h')
  = \sum_{n=1}^X \tau(n) \tau(n + 2h')
    - 2 \sum_{m=1}^{\lfloor X/2 \rfloor} \tau(m) \tau(2m + 2h')
    - 2 \sum_{m=1}^{\lfloor X/2 \rfloor} \tau(2m) \tau(m + h')
    + 4 \sum_{m=1}^{\lfloor X/2 \rfloor} \tau(m) \tau(m + h').
```

3. *(Algebraic 2-adic collapse & unconditional reduction.)* For every fixed $h \ge 1$, the affine forms in each sum have nonzero determinant, and substituting the sharp-cutoff affine binary additive divisor asymptotic for $\sum_{m \le Y} \tau(a_1 m + b_1)\tau(a_2 m + b_2)$ with slopes $(a_1, a_2) \in \{(1,1), (1,2), (2,1)\}$ (Ingham 1927 / Deshouillers–Iwaniec 1982 / Motohashi 1994 for $(1,1)$; Topacogullari 2017, *On a certain additive divisor problem*, *Acta Arith.* 181, Theorem 1.2 on p. 145 and formula (3.20) in §3.5 on pp. 170–171, corresponding to (3.19) in arXiv:1512.05770v2, summed over dyadic ranges, for general fixed affine forms; *External input*) algebraically recovers the exact 2-adic factor $\frac{1}{4}(2 - 3 \cdot 2^{-k})$ ($k = v_2(h)$) and $\rho(h) = \frac{2^{k+1} - 3}{3(2^{k+1} - 1)}$, eliminating **(H2)** from *P23-E* Theorem 2.2(2). Combining these fixed-shift asymptotics with the uniform two-point bound of *P23-E* Lemma 3.2 and the summable uniform majorant and $o(1)$ tail remainder in *P23-E* §3 (lines 311–317, Tannery's theorem) justifies exchanging the limit $X \to \infty$ with the infinite off-diagonal sum, eliminating **(H2)** from *P23-E* Theorem 3.1(3) as well.

*Proof.* Substitute $a_+(n) = \tau(n) - 2 \mathbf{1}_{2 \mid n} \tau(n/2)$ (*P22-E* Proposition 1.1; Lean `erdosBorweinPlusCoeff_eq`) into $a_+(n) a_+(n+h)$:

```math
a_+(n) a_+(n+h) = \tau(n)\tau(n+h) - 2 \mathbf{1}_{2 \mid n} \tau(n/2)\tau(n+h) - 2 \mathbf{1}_{2 \mid (n+h)} \tau(n)\tau((n+h)/2) + 4 \mathbf{1}_{2 \mid n,\, 2 \mid (n+h)} \tau(n/2)\tau((n+h)/2).
```

- When $h$ is odd, $n$ and $n+h$ have opposite parity, so the fourth term vanishes identically; setting $n = 2m$ in the second sum and $n + h = 2m$ in the third gives (1) (valid even when $X < h$, with empty sums equal to $0$).
- When $h = 2h'$ is even, $2 \mid n \iff 2 \mid (n+h)$, so all three correction terms are supported on even $n$; setting $n = 2m$ ($1 \le m \le \lfloor X/2 \rfloor$, valid for both even and odd $X$) gives (2).

For (3), for fixed $h$ every affine pair $(m, 2m+h)$, $(2m-h, m)$, $(m, 2m+2h')$, $(2m, m+h')$, $(m, m+h')$ has nonzero determinant and satisfies the size conditions of Topacogullari (2017, *Acta Arith.* 181, Theorem 1.2, p. 145) as $X \to \infty$. Summing its dyadic ranges yields the sharp-cutoff asymptotic with leading $\log^2 X$ coefficient $C_{0,0}$ given by formula (3.20) on pp. 170–171 (= (3.19) in arXiv:1512.05770v2): writing $u_i = \gcd(r_i, f_i)$, $s_i = r_i/u_i$, $h_0 = \Delta/(u_1 u_2)$, $\psi_0(t) = \prod_{p \mid t}(1 - 1/p)$, and $\gamma_0(t) = \sum_{\gcd(d, t) = 1} c_d(h_0)/d^2$, we have $C_{0,0} = \sum_{d_1 \mid u_1,\, d_2 \mid u_2} \psi_0(s_1 d_1)\psi_0(s_2 d_2)\gamma_0(s_1 d_1 s_2 d_2)$. Every odd prime $p$ acts bijectively under $m \mapsto 2m$ on $\mathbb{Z}_p$ with $|h_0|$ differing from $h$ only by a power of $2$, so all terms share the identical odd-prime singular series $P_{\rm odd}(h)$. At $p = 2$, putting $T_k := \frac{3}{4}\sum_{j=0}^k 2^{-j} = \frac{1}{4}(6 - 3\cdot 2^{-k})$: for odd $h$ ($k = 0$) each mixed pair has primitive slope-2 form ($s_i = 2$, $u_1 = u_2 = 1$), contributing $\psi_0(2) = 1/2$ on a half-length range $X/2$; for even $h = 2h'$ ($k \ge 1$) the slope-2 form is nonprimitive ($u_i = 2, s_i = 1$), so summing over $d_i \in \{1, 2\}$ yields local factor $T_{k-1} + 1/2 = \frac{1}{4}(8 - 6\cdot 2^{-k})$ on a half-length range $X/2$, while the final unrestricted pair contributes $T_{k-1}$. Multiplying each term's local factor by its range factor ($1$ for $n \le X$, $\frac{1}{2}$ for $m \le \lfloor X/2 \rfloor$) and coefficient gives:
- For odd $h$ ($k = 0$): $\frac{3}{4} - 2 \cdot \frac{1}{2} \cdot (\frac{1}{4} \cdot 2) - 2 \cdot \frac{1}{2} \cdot (\frac{1}{4} \cdot 2) = \frac{3}{4} - \frac{1}{2} - \frac{1}{2} = -\frac{1}{4} = \frac{1}{4}(2 - 3 \cdot 2^0)$.
- For even $h = 2h'$ ($k = v_2(h) \ge 1$, $v_2(h') = k - 1$): using $\mathbb{E}_2[(1+v)(1+v')] = 6 - 3 \cdot 2^{-k}$ (*P23-E* Prop. 2.1) and $\mathbb{E}_2[(1+v)(2+v')] = (6 - 3 \cdot 2^{-(k-1)}) + 2 = 8 - 6 \cdot 2^{-k}$, the weighted sum is

```math
\frac{1}{4}(6 - 3 \cdot 2^{-k}) - 4 \cdot \frac{1}{8}(8 - 6 \cdot 2^{-k}) + 4 \cdot \frac{1}{2} \cdot \frac{1}{4}(6 - 3 \cdot 2^{-(k-1)})
  = \left(\frac{3}{2} - 4 + 3\right) + \left(-\frac{3}{4} + 3 - 3\right) 2^{-k}
  = \frac{1}{4}(2 - 3 \cdot 2^{-k}),
```

matching *P23-E* Proposition 2.1 identically and establishing *P23-E* Theorem 2.2(2) without (H2). Finally, for $\mathrm{Off}_X(a_+)$ in *P23-E* Theorem 3.1(3), the fixed-shift theorem alone does not justify interchanging $X \to \infty$ with the infinite sum over $k, h \ge 1$; however, since $|a_+| \le \tau$, *P23-E* Lemma 3.2 supplies the uniform bound $\sum_{n \le X} \tau(n)\tau(n+h) \le 4\sigma_{-1}(h) X(1 + \frac{1}{2}\log(2X))^2 + 8X$ for all $1 \le h \le X$, giving the summable uniform majorant $C\, 2^{-2k-h} \sigma_{-1}(h)$ on $k + h \le X$ and $o(1)$ tail remainder on $k + h > X$ (*P23-E* §3, lines 311–317). Applying Tannery's theorem with the now-unconditional fixed-shift asymptotics yields $\mathrm{Off}_X(a_+) = (\kappa_+ + o(1))\log^2 X$ without (H2). $\square$

### 3.4 Quantitative obstruction map: $E(8)$ vs $E(4), E(2), E_+(4), E_+(2)$

Combining Theorems 3.1–3.3 with *P22-E* / *P23-E* maps the exact quantitative transition across the dyadic Lambert family. In the table below, the upper-bound and sufficient carry-deficit columns are certified outward-rounded bounds (`Finite certificate`) — note that a carry-cancellation lower bound exceeding the stated threshold is a **sufficient** test via Theorem 3.1(b)–(c) (necessity is not proved) — while observed digit/NAF frequencies at $M = 6000$ (with a 40-base-digit guard, leaving 5,960 certified retained base-4 digits for $k = 2$) are `Finite measurement` only.

| Constant | Status | Certified zero-carry bound | Sufficient carry-cancellation deficit | Observed ($M = 6000$, *finite*) | Proposed missing estimate |
| --- | --- | --- | --- | --- | --- |
| $E(8), E(16), \dots$ ($k \ge 3$) | **Simply nonnormal** (Thm. 3.1) | $f_1 \le \frac{\mu_{\rm pop}(\tau)}{k} \le 0.448708 < \frac{1}{2}$ | $0$ (cleared unconditionally) | $f_1 = 0.4147$ ($k=3$), $0.3310$ ($k=4$) | None for simple nonnormality; exact $D_\infty$ open |
| $E_{\rm odd}(8), \dots$ ($k \ge 3$) | **Simply nonnormal** (Thm. 3.1) | $f_1 \le \frac{\mu_{\rm pop}(\tau_{\rm odd})}{k} \le 0.388824 < \frac{1}{2}$ | $0$ (cleared unconditionally) | $f_1 = 0.3812$ ($k=3$), $0.2897$ ($k=4$) | None for simple nonnormality |
| $E_+(8), E_+(16), \dots$ ($k \ge 3$) | **Nonnormal, $D^- > 0$** (Thm. 3.2) | $\sigma_1/N \le \frac{\mu_{\rm NAF}(a_+)}{k} \le 0.304282 < A_{16}$ | $0$ (cleared unconditionally) | $\text{naf}/N = 0.2514$, $f_1 = 0.3342$ ($k=3$) | Simple nonnormality of $E_+(8)$ in base 2 open (signed $s_2$ not subadditive) |
| $E(4)$ ($k = 2$) | **Open** | $f_1 \le 0.673062$ (vs $0.5$) | $\liminf \bar{c}_2 > 0.1731$ (sufficient popcount test) | $f_1 = 0.4971$, $\bar{c}_2 = 0.1713$, $\text{naf}/N = 0.3614$; base-4 digits $(0.18473, 0.31376, 0.32265, 0.17886)$ | **Bit-pair XOR / base-4 arrival bias:** single-source arrivals ($\operatorname{odd}(\tau)=1$) place one `1`-bit per base-4 digit (`01` or `10`), and observed finite data stays near $f_1 \approx 1/2$ with $\bar{c}_2 < 0.1731$ (necessity of $\bar{c}_2 > 0.1731$ and impossibility of a binary popcount test are **not proved**). A direct route is a 2-column joint arrival law proving $\mathbb{E}[(-1)^{d_{2j}+d_{2j+1}}] < 0$ |
| $E_+(4)$ ($k = 2$) | **Open** | $\sigma_1/N \le 0.456423$ (vs $1/3$) | $\liminf \bar{c}_2^{\rm NAF} > 0.1231$ (sufficient signed test) | $\text{naf}/N = 0.2906$, $\bar{c}_2^{\rm NAF} = 0.1630$, $f_1 = 0.4003$; base-4 digit `0` $= 0.38775$ | **Signed-arrival cancellation lower bound:** unconditional $\liminf \bar{c}_2^{\rm NAF} > 0.1231$ from opposite-sign ($n$ odd vs $4 \mid n$) collisions in base-4 columns |
| $E(2)$ ($k = 1$, `BC-37`) | **Open** *(external base-2 disjunctivity preserved on `BC-37`)* | $f_1 \le 1.346123$ (vs $0.5$) | $\liminf \bar{c}_1 > 0.8462$ (sufficient popcount test) | $f_1 = 0.5008$, $\bar{c}_1 = 0.8358$ | $\ge 16$-column joint law and $\ge 7$-point shifted correlations of $(V, U)$ (`CC-49`, `GF-28`, `GF-35`) |
| $E_+(2)$ ($k = 1$, `BC-39`) | **Open** | $\sigma_1/N \le 0.912845$ (vs $1/3$) | $\liminf \bar{c}_1^{\rm NAF} > 0.579512$ (sufficient signed test) | $\text{naf}/N = 0.3374$, $f_1 = 0.4928$ | $\ge 14$-column signed joint law of $(v_2, \operatorname{odd})$ of $a_+$ beyond $r = 2$ (where Thm. 3.3 now handles $r = 2$); NAF density sits near $1/3$ |

---

## 4. Lean 4 blueprint (finite algebraic cores)

Statements only; not compiled here. Every statement is finite or elementary and is checked across thousands of instances by [`scripts/phase24_classical.py`](../../scripts/phase24_classical.py). Builds go through `hail` (`AGENTS.md`).

```lean
-- E1.1 Same-band CRT collapse (Thm. 1.1(a)): H_S ≡ M_S / p (mod p) for all p ∈ S.
theorem prod_div_sum_modEq_div (S : Finset ℕ) (p : ℕ) (hp : p ∈ S) (hcop : ∀ q ∈ S, q ≠ p → p.Coprime q) :
    (∑ q ∈ S, (∏ r ∈ S, r) / q) ≡ (∏ r ∈ S, r) / p [MOD p]

-- E1.2 Top-band Fermat cancellation (Thm. 1.3): for odd prime p and n ≥ 2p,
--      p ∣ (2^(n - p) - 2^(n + 1 - 2p)).
theorem topBand_fermat_cancel {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hn : 2 * p ≤ n) :
    p ∣ 2 ^ (n - p) - 2 ^ (n + 1 - 2 * p)

-- E2.1 Exact completed-square prefix residual identity (Thm. 2.1(2)).
theorem quad_prefix_completed_square (A B C b x' : ℤ) (N : ℕ) :
    (B ^ 2 - 4 * A * C) * b ^ (2 * N) - (2 * A * x' + B * b ^ N) ^ 2 =
      4 * A * (-(A * x' ^ 2 + B * b ^ N * x' + C * b ^ (2 * N)))

-- E2.2 Exact binary popcount identity for phi's completed-square prefix (Thm. 2.2(3)).
theorem phi_completed_prefix_popcount (N r : ℕ) (hN : 1 ≤ N) (hr : r < 2 ^ (N - 1)) :
    (2 * (2 ^ N + 2 ^ (N - 1) + r) - 2 ^ N).popCount + 1 = (2 ^ N + 2 ^ (N - 1) + r).popCount

-- E3.1 Exact binary addition carry-balance identity (Thm. 3.1(b)).
theorem popcount_add_carries_eq (x y : ℕ) :
    (x + y).popCount + (x.popCount + y.popCount - (x + y).popCount) = x.popCount + y.popCount

-- E3.2 Exact pointwise 3-term/4-term a_+ shifted divisor identity (Thm. 3.3).
theorem erdosBorweinPlusCoeff_mul_shift_odd {n h : ℕ} (hn : 0 < n) (hh : Odd h) :
    erdosBorweinPlusCoeff n * erdosBorweinPlusCoeff (n + h) =
      (n.divisors.card : ℤ) * ((n + h).divisors.card : ℤ)
      - (if 2 ∣ n then 2 * ((n / 2).divisors.card : ℤ) * ((n + h).divisors.card : ℤ) else 0)
      - (if 2 ∣ (n + h) then 2 * (n.divisors.card : ℤ) * (((n + h) / 2).divisors.card : ℤ) else 0)
```

---

## 5. Verification record

```sh
python -B scripts/phase24_classical.py
```

Standard library only; exits `0` with **108,334 assertions** in ~2.5 s:

- **E1:** `[exact]` same-band CRT collapse & $Q_m$ lift (`2,651` multi-prime bands, $N \le 500$); `[exact]` global band decomposition & explicit $\sqrt{N}$-smooth defect ($4 \le N \le 220$); `[exact]` consecutive-shift and multi-step band evolution ($300$ steps, prime-square exits $p \in \{3, 5, 7, 11, 13, 17\}$, Wieferich vanishing at $1093, 3511$); `[exact]` $A_m < 8^m$ ($m \le 1200$) and exact integer dropped-prime product bound ($2 \le n \le 1200$), plus `[float]` numerical checks of $\sum_{p \in D_n} \log p \le 4 n^{2/3}$ ($n \le 1200$ and analytic constant $n < 20{,}000$); `[exact]` $\Phi_{n,1}$ recurrence ($3 \le n \le 800$, $\Phi_{2,1} = 0$) and `[encl]` certified $|r_n^{\rm top}| < \frac{8}{3n}$ and fixed-point shadowing of $\alpha_{\rm top}$ to $< 2^{-43}$ with propagated tail and rounding bounds ($n \le 200$); `[float]` numerical evaluation of the $r = 2$ complete-period character factorization (`153` pairs, $p \le 67$, $c_1 = c_2 = 1$, `32` primitive-root $g = 2$ pairs); `[exact]` Barrier 1 (`19,487` same-band pairs) and Barrier 2 (`306` exact-$Q_n$ pointwise alignment instances); `[finite]` Weyl-sum comparison for $\ln 2, \alpha_{\rm top}, \beta_{\rm low}$.
- **E2:** `[exact]` quadratic residual, completed-square identity, and binary borrow dichotomy (`567` instances on $\sqrt{2}, \sqrt{3}, \phi$, $N = 2\dots 300$); `[exact]` explicit $s_2$ lower bounds from exact endpoints ($\sqrt{2}: N \ge 2$, $\sqrt{3}: N \ge 3$, $\phi: N \ge 5$, to $1000$), ordinary-digit check at $N = 0$ ($\sqrt{5}$), and exact base-$b$ squaring carry identity (`36` cases); `[exact]` carry-gauge gap recurrence on all fractional NAF positions ($m_j \ge 1$) and repaired all-$N$ support bound ($N \le 2000$), plus neutralization witnesses $u_N = 2^N - 1$ ($4 \le N \le 200$); `[exact]` Kummer's $v_2(\binom{2k}{k}) = s_2(k)$ ($k \le 400$), exact series & gauge identities for all $5$ binomial/Catalan/Pell series (including a genuine base-200 gauge check and both radix-200 and binary displaced widths $W_{U,200}(300), W_{U,2}(300)$), and Pell convergent sign $(-\epsilon)^k$ & period checks ($r \le 16$).
- **E3:** `[encl]` certified outward-rounded exact rational enclosures for $\mu_{\rm pop}(\tau_{\rm odd}), \mu_{\rm pop}(\tau), \mu_{\rm pop}(|a_+|), \mu_{\rm NAF}(\tau), \mu_{\rm NAF}(a_+)$ ($P = 600, U_{\rm cap} = 512, K_2 = 24$), explicit prime-tail telescoping check at $P = 600$, all-prefix signed carry-buffer check ($1 \le N_0 \le 100, 1 \le k \le 6$), and exact `Fraction` assertions for every published interval and sufficient carry threshold; `[exact]` full 7-vector BFS closure, 4-state lumping table & minimality certification (proving $A_L$ for all $L \ge 1$, with finite cross-checks $1 \le L \le 20$ DP and $L \le 10$ brute-force); `[encl]` certified $D^-(E_+(8); 2) \ge 2.34 \times 10^{-7} > 0$; `[exact]` 3-term/4-term reductions of $\sum a_+(n) a_+(n+h)$ (`128` pairs, $1 \le h \le 32$, odd and even $X \le 2^{16}$) and 2-adic algebraic collapse ($k \le 20$); `[exact]` independent column-by-column carry count verifying Kummer's balance identity ($M = 6000$) and `[finite]` obstruction-map & base-4 digit measurements (5,960 certified retained base-4 digits at $M = 6000$ with 40-base-digit guard).

---

## 6. Open questions

1. **Top-band prime series $\alpha_{\rm top}$:** Prove $D^+(\alpha_{\rm top}; 2) < 1$ (equivalently $\limsup |\frac{1}{N} \sum_{n < N} e(\Phi_{n,1})| < 1$), or construct a dynamic BBP-compatible complement barrier showing even a dynamic perturbation of $\beta_{\rm low}$ can cancel $\alpha_{\rm top}$.
2. **Signed-digit complexity of $\sqrt{2}$:** Establish $\sigma_N(\sqrt{2}) \gg N^\delta$ (or $\chi_N(\sqrt{2}) \gg N^\delta$) for any $\delta > 0$, overcoming the signed-digit neutralization barrier of Theorem 2.3(b).
3. **$E(4)$ via bit-pair XOR correlation:** Prove $\limsup_M \frac{1}{M} \sum_{j < M} (-1)^{d_{2j} + d_{2j+1}} < 0$ for $E(4)$ (base-4 digits `01`/`10` dominating `00`/`11`), which would establish simple nonnormality of $E(4)$ in base $4$ without requiring a binary popcount bias.
4. **$E_+(4)$ via signed-arrival cancellation:** Prove an unconditional lower bound $\liminf_M \bar{c}_{2, M}^{\rm NAF}(E_+(4)) > 0.1231$, which combined with Theorem 3.2 would prove $E_+(4)$ is nonnormal in base $2$ and base $4$.
5. **Simple nonnormality of $E_+(8)$:** Theorem 3.2 proves $E_+(8)$ is nonnormal with $D^-(E_+(8); 2) > 0$; does $E_+(8)$ also satisfy $\limsup f_1(E_+(8); 2) < 1/2$ (observed $0.3342$ at $M = 6000$)?

## References

- B. Adamczewski and Y. Bugeaud, On the complexity of algebraic numbers I. Expansions in integer bases, *Ann. of Math.* **165** (2007), 547–565.
- D. H. Bailey, J. M. Borwein, R. E. Crandall, and C. Pomerance, On the binary expansions of algebraic numbers, *J. Théor. Nombres Bordeaux* **16** (2004), 487–518.
- Y. Bugeaud, *Distribution Modulo One and Diophantine Approximation*, Cambridge Tracts in Math. **193**, Cambridge Univ. Press, 2012.
- J.-M. Deshouillers and H. Iwaniec, An additive divisor problem, *J. London Math. Soc.* (2) **26** (1982), 1–14.
- D. Hanson, On the product of the primes, *Canad. Math. Bull.* **15** (1972), 33–37.
- A. E. Ingham, Some asymptotic formulae in the theory of numbers, *J. London Math. Soc.* **2** (1927), 202–208.
- J. E. Maxfield, Normal $k$-tuples, *Pacific J. Math.* **3** (1953), 189–196.
- Y. Motohashi, The binary additive divisor problem, *Ann. Sci. Éc. Norm. Supér.* (4) **27** (1994), 529–572.
- D. Ridout, Rational approximations to algebraic numbers, *Mathematika* **4** (1957), 125–131.
- J. B. Rosser and L. Schoenfeld, Approximate formulas for some functions of prime numbers, *Illinois J. Math.* **6** (1962), 64–94.
- B. Topacogullari, On a certain additive divisor problem (2017), Theorem 1.2 and §3.5, arXiv:1512.05770.
- Phase 22 [classical-targets-and-recon.md](../phase22/classical-targets-and-recon.md) (`GF-28`); Phase 23 [classical-correlations-and-log2.md](../phase23/classical-correlations-and-log2.md) (`GF-35`), [binary-partition-and-carry-complexity.md](../phase23/binary-partition-and-carry-complexity.md) (`GF-32`), [dense-characters-and-nonfundamental-forms.md](../phase23/dense-characters-and-nonfundamental-forms.md) (`GF-31`).
