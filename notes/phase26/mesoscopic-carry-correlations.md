# Mesoscopic Carry Correlations and Classical Lambert Constants

Phase 26, Track C (`C1`–`C5`). Companion verification script: `scripts/phase26_mesoscopic_carries.py`.

**Reproduction & verification summary.** Running `python -B scripts/phase26_mesoscopic_carries.py` (Python standard library only, CPython 3.13 on Windows; takes ~5–6 s) executes **`24,497 [exact] + 2,828 [encl] = 27,325` zero-float theorem checks** (plus **`3 [finite]`** prefix measurements, counted separately) and exits with code `0`. Every `[exact]` and `[encl]` check uses exact integers, `fractions.Fraction`, or directed-rounded fixed-point integer arithmetic at scale $2^{-100}$; **no floating-point literals or `float`/transcendental calls appear anywhere in the script (not even in failure-message formatting)**. Every decimal interval or endpoint quoted in this note is the outward rounding (floor for lower endpoints, ceiling for upper endpoints) of a certified `Fraction` bound and is explicitly asserted in `scripts/phase26_mesoscopic_carries.py`.

**Scope, evidence discipline, and benchmark stability.** Evidence labels strictly follow `docs/research-objectives.md`: `Paper proof`, `Finite certificate`, `External input`, `Conditional`, `Finite measurement`, and `Open`. Finite prefix statistics (`[finite]`) are finite measurements only and are never treated as evidence for asymptotic statements. No registry file (`docs/registry/`) and no benchmark file (`docs/benchmarks/classical-constants.toml`, fixed roster `BC-01`–`BC-50`, or `docs/benchmarks/arithmetic-families.toml`) is modified here; in particular, although Theorem C5.3 proves unconditional base-2 disjunctivity of $E_{\mathrm{odd}}(2)$ (`BC-38`) and $E_+(2)$ (`BC-39`) alongside $E(2)$ (`BC-37`), any benchmark status update awaits independent verification and registry registration. Cross-model review is not independent human peer review.

---

## Results at a Glance

| ID | Statement | Evidence | External inputs | Standing Objectives |
| :--- | :--- | :--- | :--- | :--- |
| **C1.1** | **Two-column adjacent-pair criterion for $E(4)$ & exact 1-column converse.** An exact 1-line inequality on all 64 triples $(a_1, a_2, a_3) \in \mathbb{Z}/2 \times \mathbb{Z}/4 \times \mathbb{Z}/8$ upgrades `GF-41` Thm 2.4 from 3 columns to **2 adjacent columns**: under $Q^{(1/2) \otimes 2}$ alone, $\mathbb{E}[\Psi_{2,\mathrm{adj}}] \in [0.356817, 0.356889]$, yielding $\limsup f_1(E(4); 2) \le 0.486661 < \frac{1}{2}$ ($D^- \ge 0.013339$). Conversely, an explicit closed-form shift-invariant star-orbit mixture matches the exact 1-column residue law $p_J$ and all-order stationarity yet achieves $\mathbb{E}[R_3/8] \ge 0.380742 > 0.370231$, proving column interaction order **$k = 2$ is sharp** for $E(4)$. | Paper proof; Finite certificate (conditional part for $E(4)$ under $H_2^{\mathrm{adj}}$) | None for exact inequality, converse, and certificate; conditional $H_2^{\mathrm{adj}}$ for $E(4)$ | 2, 3, 4 |
| **C1.2** | **Exact factorial-moment order hierarchy for $E(4)$ at $W = 3$ (solves `GF-41` OQ6).** For the general 7-variable marked counts $(N_1; N_{2,1}, N_{2,3}; N_{3,1}, N_{3,3}, N_{3,5}, N_{3,7})$: order $r = 3$ fails ($\ge 0.378089 > 0.370231$, certified by a $35 \times 35$ exact rational perturbation basis, matching all 120 order-$\le 3$ marked moments including all 6 derived column-count second moments $= 1/4$), while our global **2-column Shifted Split-Bonferroni** polynomial of degree $r = 7$ succeeds ($\le 0.369593 < 0.370228$), giving **$4 \le r_{\min}^{\mathrm{marked}}(E(4); W = 3) \le 7$** using 2-column moments only. Under i.i.d. marks $\nu$ on $(N_1, N_2, N_3)$: $r = 2$ fails ($\ge 0.400955$, explicit 8-atom law of denominator 24) and $r = 3$ succeeds globally ($\le 0.369859$, certified by Young's inequality + 1,800 exact box points), giving **$r_{\min}^{\mathrm{iid}}(E(4); W = 3) = 3$ exact**. | Paper proof; Finite certificate (zero-float) | None | 3, 4 |
| **C1.3 & C2** | **Exact Fourier/trigonometric thresholds for $E(4)$ & $E(2)$.** On $\mathbb{Z}/8\mathbb{Z}$, dropping any single harmonic $h^* \in \{1, 2, 3, 4\}$ raises the worst-case expectation above $0.370231$. On $\mathbb{R}/\mathbb{Z}$, exact Sturm root counting (`roots = (0, 0)`) certifies a degree-$12$ rational majorant $T_{12} \ge \mathbf{1}_{[1/2, 1)}$ with $\mathbb{E}[T_{12}] \in [0.497296, 0.497302] < \frac{1}{2}$, while a $23 \times 23$ pure-integer Neumann-series certificate constructs a degree-$11$ countermeasure with $\mu([1/2, 1)) \ge 0.503909 > \frac{1}{2}$, proving **$M_{\min}(E(4)) = 12$ exact**. For **$E(2)$ at $W = 8$**, stationarity halves `CC-49`'s Bonferroni order from $r = 92$ (at $D = 16$) to **$r = 46$** (excess $\le 0.002220 < 0.0028923$). | Paper proof; Finite certificate (zero-float Sturm + Neumann) | None | 3, 4 |
| **C1.4** | **Unconditional arithmetic moments & dual LP barriers.** Catalogs all unconditionally provable displaced-arrival moments (including a new unconditional lattice-scale 2nd-moment bound with explicit certified **$C_{\mathrm{lat}} = 180$** via dyadic shells + 2-D Selberg sieve), strictly separates all five moment layers, and proves via C1.1–C1.3 exact dual-LP barriers for 1-column residue laws with stationarity, order-3 single-window marked moments, order-2 i.i.d.-mark count moments, and degree-11 circular Fourier moments, alongside three sufficient inputs crossing the $E(4)$ threshold. | Paper proof; Finite certificate; External input (Wirsing, Halász, 2-D Fundamental Lemma / Selberg sieve) | Wirsing (1967), Halász (1968), 2-D Fundamental Lemma / Selberg sieve | 3, 4 |
| **C3.1** | **Unconditional proof of `PUB(C)` in `GF-41` Thm 4.3.** Uniformly for $1 \le d < d' \le \sqrt{L}$ ($L = \log\log x$), $\#\{n \in (x/2, x] : \omega(n+d) - \omega(n) = 2d,\; \omega(n+d') - \omega(n) = 2d'\} \le C |I| / L$. Simple nonnormality of $E^*(4)$ via `GF-41` Thm 4.3 now reduces to **`LLB(c)` alone** (even along a single subsequence of scales). | Paper proof; External input | 3-D Fundamental Lemma of the Combinatorial Sieve | 2, 3, 4 |
| **C3.2** | **Zero-external-input collision lower bound for $E^*(4)$.** CRT prime-planting + Turán–Kubilius + optimal $A = \sqrt{3}$ Chebyshev–Markov + Pigeonhole yields unconditionally $\#\{n \le N : \exists d \in [1, 6\sqrt{L}],\; q(n+d) = q(n)\} \ge N \exp(-C (\log\log N)(\log\log\log N))$. | Paper proof; Finite certificate (algebraic SOS & CRT check) | **None** | 3 |
| **C3.3** | **Polynomial-in-$1/\log N$ collision lower bound for $E^*(4)$.** Admissible $k$-tuple CRT planting $q(m + iB) = 2m - \omega(L_i(t))$ + general linear-forms Maynard (2015, 2016) / Polymath8b (2014) at $k = 50$ yields $\gg N / (\log N)^{50}$ collisions unconditionally (and general linear-forms GGPY 2009 at $k = 3$ yields infinitely many bounded-shift $E_2$-collisions). Structural remark isolates the uniform $(-1)^{\omega(n)+\omega(n+d)}$ parity obstruction blocking `LLB(c)`. | Paper proof; Finite certificate (admissibility, coprimality & independence); External input | General linear-forms Maynard (2015, 2016) / Polymath8b (2014); GGPY (2009) | 3, 4 |
| **C4.1** | **Signed Carry Conservation & Exponential Carry-Growth Lemma.** Exact telescoping carry bound $\sum_{n < N} |q_n| \le \sum_{n \le N} |C_k(n)| + A_N + |q_N| - |q_0|$ and disjoint $t$-gap growth bound $A_N/N \ge (1 - 2^{-(t+1)}) |\mathcal{M}_t(N)|/N - 2^{-(t+1)} \overline{|C_k|} - \frac{2(|q_N| - |q_0|)}{2^{t+1} N}$, linking $A_N$ to binary transitions $\mathrm{tr}_N \ge (A_N - 2)/2$ and $1 - D_N(x; 2) \ge \min(\frac{1}{4}, \frac{A_N - 6}{4N})$. | Paper proof; Finite certificate (certified 1200-bit prefixes of $E_+(8), E_+(16), E_+(32)$) | **None** | 3 |
| **C4.2** | **Explicit $k_0 = 25$ for $D^+(E_+(2^k); 2) < 1$ & sharp large-window barrier for $E_+(8)$.** Combining C4.1 ($t = 2$), a dyadic-block decomposition covering all $m \le M$, 2-D Selberg sieve, monotone pure-integer enclosure of $1/\sigma_2(s)$, and 10-shell Abel summation with verified non-increasing Rankin weights certifies **$k_0 = 25$** ($k_{\mathrm{req}} \le 24.75247$, $1 - D^+ \ge 4.36 \times 10^{-5}$ at $k = 25$), slashing `GF-42` Thm B1.4's $k_0 > 3.05 \times 10^{10}$ by **$> 1.2 \times 10^9\times$**. Conditionally, any 2-point lattice pair constant $C < 1.02341$ proves $D^+(E_+(8); 2) < 1$. Conversely, the periodic zero-sum arrival sequence $C(12m) = -1, C(12m+1) = +2$ ($x = 0 \in K_2$) proves large-$G$ window statistics alone cannot decide $D^+(E_+(8); 2) < 1$. | Paper proof; Finite certificate (zero-float); External input (2-D Selberg sieve) | 2-D Selberg upper-bound sieve (`Opera de Cribro` Thm 7.1) | 2, 3, 4 |
| **C4.3** | **Exact carry-coupled base-$2^L$ simple-normality floor & base-256 simple nonnormality of $E_+(8)$.** Proves analytically for every $L \ge 1$ (over all non-dyadic $x$) that $m_1^{(2^L)} = \frac{1}{3} - \frac{2 + (-1/2)^{L-1}}{9L}$ (via a 2-state carry Markov chain on $c_n \in \{0, 1\}$, $\psi \equiv 0$, with exact irrational Eulerian-cycle attaining numbers for every $L \ge 2$). Yields with **zero external inputs**: **$E_+(8)$ is simply nonnormal in base $256$** ($32\times$ stronger than `GF-42`'s base $8192$, and **$L = 8$ is sharp** vs $L \le 7$ for NAF weight alone); **$E_+(2^k)$ ($k \ge 4$, starting at $E_+(16)$) is simply nonnormal in base $4$ and base $8$** (even DP-free, via a 2-line base-4 proof!); **$L_-(4), L_+(8)$ (mod $7, 9, 13, 19, 37$), $E_+^*(8), E_{\mathrm{alt},+}^*(8)$ in base $16$**; **$E_{+,\mathrm{odd}}(16)$ in base $64$**; plus sharpened $E_+(4)$ deficit $[0.120699, 0.120775]$ (with multiscale block scaling isolated in a subsequent remark). | Paper proof; Finite certificate (zero-float) | **None** | 2, 3, 4 |
| **C5.1** | **Complete order-$m$ Dirichlet character Lambert trichotomy & new alternating cubic class.** Classifies all primitive characters $\chi$ of order $m$: $m = 1$ (nonnormal $k \ge 3$); $m$ even (Dirichlet density $1/m$ zeros, $\in K_b$ for all $b \ge 2, k \ge 1$ via `GF-13`); $m = 3$ (bounded NAF mean, including **new alternating cubic $L_{-,+}(4)$** for $M \in \{31, 43, 109, 127\}$ with $\rho_- < \frac{1}{4}$ $\implies$ unconditional binary order-2 nonnormality AND base-4 & base-8 simple nonnormality at $k = 2$, zero external inputs; unitary $L_{-,+}^*(4)$ base-16; and universal $k = 1$ cubic barrier $> 0.487$ / $> 0.452 > \frac{1}{3}$); and **new odd $m \ge 5$ cyclotomic-unit divergence barrier** ($\overline{w_\pm}(\Lambda(1 * \chi)) \to +\infty$ for every odd $m \ge 5$ and every nonzero $\Lambda : \mathbb{Z}[\zeta_m] \to \mathbb{Z}$, handling all conjugate-pair null directions and degenerate $S$-unit subsums explicitly, verified in $\mathbb{Z}[\zeta_5]$ on all 1,115 squarefree $n \le 2000$ coprime to $11$, the $\Lambda = c - d$ counterexample, and unit inverses for $m = 5, 7, 9$). | Paper proof; Finite certificate; External input (for $m$ even and odd $m \ge 5$) | None for $m \in \{1, 3\}$; Dirichlet's theorem + Wirsing / Selberg–Delange (`GF-13`) for $m$ even; Evertse (1984, Thm 1) + Halász (1968) + Dirichlet's theorem for odd $m \ge 5$ | 2, 3, 4 |
| **C5.2** | **New full-density quadratic-twisted family $\tau_3 * \chi_D$.** For every quadratic character $\chi_D$, $(\tau_3 * \chi_D)(p) = 3 + \chi_D(p) \in \{2, 4\}$ and $(\tau_3 * \chi_D)(p^e) \ge 1$ everywhere (exact closed form $\lfloor(e+2)/2\rfloor\lfloor(e+3)/2\rfloor$ when $\chi_D(p) = -1$). Certified $C_{\mathrm{pop}}$ gives unconditional simple nonnormality (zero external inputs) for **$k \ge 3$ at $D = 5$** ($C_{\mathrm{pop}}/3 \le 0.475190 < \frac{1}{2}$) and **$k \ge 4$ at $D \in \{-3, -4, 8\}$**. Certified $C_{U, D}$ together with the $V_D(p) \in \{1, 2\}$ 2-D Fundamental Lemma + Halász extension gives unconditional **$0 < D^- \le D^+ < 1$ and $F_D(2^k) \notin K_2$ for every $k > C_{U, D}$** (**$k \ge 3$ for $D = 5$; $k \ge 4$ for $D \in \{-3, 8\}$; $k \ge 5$ for $D = -4$**), and **$D^-(F_D(2^k); 2^k) \ge \max(0, 1 - 2\sqrt{C_{U, D}/k}) \to 1$** at rate $O(\frac{\log k}{k})$. | Paper proof; Finite certificate | None for simple nonnormality; 2-D Fundamental Lemma, Dirichlet's theorem, Halász (1968) for $D^+ < 1$ and $D^-(2^k) \to 1$ | 2, 3 |
| **C5.3** | **Unconditional base-2 disjunctivity of $E(2^k)$, $E_{\mathrm{odd}}(2^k)$, and $E_+(2^k)$ for every $k \ge 1$ (resolves `GF-42` OQ4).** Elementary CRT + Odd-Target Guard-Bit Lemma + Markov proof yields $\#\{0 \le n < N : d_{n+1}\cdots d_{n+\ell}(F; 2) = w\} \ge N \exp(-(37/k)(\log\log N)^3)$ (wholly contained inside $[0, N)$) for every binary word $w$, every $k \ge 1$, and $F \in \{E(2^k), E_{\mathrm{odd}}(2^k), E_+(2^k)\}$. Establishes **unconditional disjunctive nonnormality** of all three families for all $k \ge 3$ (combining with $D^- > 0$ from `GF-36` and `GF-40`/`GF-44`), proves base-2 disjunctivity of **$E_{\mathrm{odd}}(2)$ (`BC-38`)** and **$E_+(2)$ (`BC-39`)** alongside $E(2)$ (`BC-37`) with zero external inputs, and gives paper constant $37/k$ (compared with Captain Sude's external Lean-verified $70{,}000$ for $E(2)$). | Paper proof; Finite certificate (zero-float) | **None** | 2, 3 |

---

## 0. Definitions, Constants, and Moment Taxonomy

We follow the exact notation of `GF-41` (`notes/phase25/e4-carry-correlations.md`), `GF-42` (`notes/phase25/generalized-lambert-and-eplus.md`), and `GF-44` (`notes/phase25/naf-geometric-transfer.md`).

- **Classical Lambert series.** For $b = 2$ and $k \ge 1$:
  ```math
  E(2^k) = \sum_{n \ge 1} \frac{1}{2^{kn} - 1} = \sum_{m \ge 1} \tau(m) 2^{-km}, \qquad
  E_{\mathrm{odd}}(2^k) = \sum_{n \ge 1} \frac{1}{2^{k(2n-1)} - 1} = \sum_{m \ge 1} \tau_{\mathrm{odd}}(m) 2^{-km},
  ```
  ```math
  E^*(2^k) = \sum_{m \ge 1} 2^{\omega(m)} 2^{-km} = \sum_{m \ge 1} 2^{-(km - \omega(m))}, \qquad
  E_+(2^k) = \sum_{n \ge 1} \frac{1}{2^{kn} + 1} = \sum_{m \ge 1} a_+(m) 2^{-km},
  ```
  where $a_+(2^e u) = (1 - e)\tau(u)$ for odd $u$ ($a_+(m) = 0 \iff m \equiv 2 \pmod 4$), $\tau(m) = 2^{v(m)} o(m)$ with $o(m) = \prod_{p^e \parallel m} \mathrm{odd}(e + 1)$ odd, and $|a_+(m)| = 2^{V_+(m)} U_+(m)$ for $m \not\equiv 2 \pmod 4$ with $U_+(m)$ odd.
- **Displaced column arrivals and residue windows.** For $E(2^k)$, the mark arrival at binary column $j \ge 1$ is
  ```math
  J_j := \sum_{\substack{m \ge 1 \\ km - v(m) = j}} o(m), \qquad
  R_W(j) := \left(\sum_{i = 1}^{W} J_{j + i} 2^{W - i}\right) \bmod 2^W,
  ```
  with arrival count $N_j := \#\{m \ge 1 : km - v(m) = j\}$ and marked counts $N_{j, r}^{(m)} := \#\{n \ge 1 : kn - v(n) = j,\, o(n) \equiv r \pmod m\}$. For $E(4)$ ($k = 2$) at $W = 3$, the 7 marked count variables entering $R_3(j) = (4 J_{j+1} + 2 J_{j+2} + J_{j+3}) \bmod 8$ are
  ```math
  \mathbf{N}(j) := \bigl(N_{j+1};\; N_{j+2, 1}^{(4)},\, N_{j+2, 3}^{(4)};\; N_{j+3, 1}^{(8)},\, N_{j+3, 3}^{(8)},\, N_{j+3, 5}^{(8)},\, N_{j+3, 7}^{(8)}\bigr) \in \mathbb{Z}_{\ge 0}^7.
  ```
- **Five strictly separated moment/expectation layers.** Throughout Sections 1–2 we strictly separate:
  1. *Coefficient moments*: averages of $f(\tau(n))$ or $f(o(n))$ over $n \le M$ (e.g. $\mu = \lim \frac{1}{M} \sum_{n \le M} o(n) \in [2.076318, 2.076347]$ self-contained here, and $[2.07632553, 2.07632693]$ in `GF-41` Thm 2.6; $C_{\mathrm{true}} = \lim \frac{1}{M} \sum_{n \le M} s_2(\tau(n)) \in [1.339103, 1.339116]$).
  2. *Unconditionally proved displaced-arrival moments*: averages of functions of $(J_j, N_j, \mathbf{N}(j))$ over columns $1 \le j \le N$ proved without unproved hypotheses (Theorem C1.4).
  3. *Carried binary digit statistics*: $f_{1, N}(x; 2) = \frac{1}{N} \sum_{j=1}^N d_j(x; 2)$, $D_N(x; 2)$, and true carries $c_j = \lfloor \sum_{i > j} r_i 2^{j-i} \rfloor$ (`GF-41` §1).
  4. *Comparison-model expectations* (heuristic/conditional benchmark ONLY): expectations under i.i.d. compound-Poisson columns $J_j \sim \mathrm{CP}(1/k, \nu)$, denoted $Q_W^{(1/k)}$ on $\mathbb{Z}/2^W\mathbb{Z}$ and $Q^{(1/k)}$ on $\mathbb{R}/\mathbb{Z}$, where $\nu$ is the exact limiting law of $o(n)$ (`GF-41` §0).
  5. *Dual LP/SDP bounds*: exact worst-case extrema over ALL probability laws matching a prescribed moment or Fourier constraint set.
- **NAF weight and discrepancy.** For $m \in \mathbb{Z}$, $w_\pm(m) := \min\{\sum_i |s_i| : m = \sum_i s_i 2^i,\, s_i \in \{-1, 0, 1\}\}$ is the non-adjacent form (NAF) weight; for $x \in \mathbb{R}$, $\sigma_1(x; N) := \min\{\sum_{n=1}^N |s_n| : x = \sum_{n \ge 1} s_n 2^{-n},\, s_n \in \{-1, 0, 1\}\}$ and $\overline{w}_\pm(x) := \limsup_{N \to \infty} \sigma_1(x; N)/N$. The extreme discrepancy is $D_N(x; b) := \sup_{0 \le u < v \le 1} |F_N([u, v)) - (v - u)|$, with $D^-(x; b) = \liminf D_N$ and $D^+(x; b) = \limsup D_N$.

---

## 1. Tracks C1 & C2: $E(4)$ and $E(2)$ Mesoscopic Arrival Correlations and Exact Moment/Fourier Thresholds

`GF-41` Theorem 2.2 proves unconditionally for every $k \ge 1$ and $W \ge 1$ the stationarity bound
```math
\limsup_{N \to \infty} f_{1, N}(E(2^k); 2)
  \le \limsup_{N \to \infty} \frac{1}{N} \sum_{j = 0}^{N - 1} \frac{R_W(j)}{2^W} + \frac{\mu}{k \cdot 2^W}.
```
For $E(4)$ ($k = 2$) at $W = 3$, this requires beating the threshold
```math
t_3 := \frac{1}{2} - \frac{\mu}{16} \in [0.370228, 0.370231] \qquad (\text{self-contained } \mu \in [2.076318, 2.076347];\ \text{GF-41 gives } t_3 \approx 0.3702296).
```

### 1.1 Two-column adjacent-pair criterion and exact 1-column converse

`GF-41` Theorem 2.4 proved that the 2-column residue window $R_2 = (2 J_1 + J_2) \bmod 4$ cannot decide $E(4)$ ($B_2 > \frac{1}{2}$), and therefore required the 3-column hypothesis $H_3$. By exploiting LP duality on the $W = 3$ stationarity bound, we eliminate all 3-column correlations completely and show that **2 adjacent columns** are both necessary and sufficient.

**Theorem C1.1 (Two-column adjacent-pair criterion and exact 1-column converse; Paper proof + Finite certificate; Conditional part under $H_2^{\mathrm{adj}}$).**
1. *(Exact 2-column majorant.)* Define $u : \mathbb{Z}/2\mathbb{Z} \times \mathbb{Z}/4\mathbb{Z} \to \mathbb{Q}$ and $v : \mathbb{Z}/4\mathbb{Z} \times \mathbb{Z}/8\mathbb{Z} \to \mathbb{Q}$ by
   ```math
   u(a_1, a_2) := \frac{1}{2}\mathbf{1}[a_1 = 1] + \mathbf{1}[a_1 = 0,\, a_2 \in \{2, 3\}], \qquad
   v(a_2, a_3) := \frac{r_{23}}{8} - \mathbf{1}[a_2 \in \{2, 3\},\, r_{23} \ge 4],
   ```
   where $r_{23} := (2 a_2 + a_3) \bmod 8$. Then for **all $64$ triples** $(a_1, a_2, a_3) \in \mathbb{Z}/2\mathbb{Z} \times \mathbb{Z}/4\mathbb{Z} \times \mathbb{Z}/8\mathbb{Z}$,
   ```math
   \frac{(4 a_1 + 2 a_2 + a_3) \bmod 8}{8} \le u(a_1, a_2) + v(a_2, a_3),
   ```
   with exact equality on $48/64$ triples and slack $+1$ on the remaining $16$ triples ($a_1 = 0, a_2 \in \{2, 3\}, r_{23} < 4$). Equivalently, shifting by $c(a_2) = \frac{1}{2}\mathbf{1}[a_2 \in \{2, 3\}]$,
   ```math
   u(a_1, a_2) + v(a_2, a_3) = \frac{1}{2}\mathbf{1}[a_1 = 1] + w(a_1, a_2) + v'(a_2, a_3),
   ```
   where $w(a_1, a_2) := \frac{1}{2}(-1)^{a_1} \mathbf{1}[a_2 \in \{2, 3\}] \in [-\frac{1}{2}, \frac{1}{2}]$ and $v'(a_2, a_3) := v(a_2, a_3) + \frac{1}{2}\mathbf{1}[a_2 \in \{2, 3\}] \in [0, \frac{7}{8}]$.
2. *(Unconditional 2-column reduction for $E(4)$.)* Putting $\Psi_{2,\mathrm{adj}}(a, b) := u(a \bmod 2, b \bmod 4) + v(a, b)$ on $\mathbb{Z}/4\mathbb{Z} \times \mathbb{Z}/8\mathbb{Z}$, every real arrival sequence satisfies unconditionally
   ```math
   \limsup_{N \to \infty} f_{1, N}(E(4); 2)
     \le \limsup_{N \to \infty} \frac{1}{N} \sum_{j = 1}^{N} \Psi_{2, \mathrm{adj}}\bigl(J_j \bmod 4,\, J_{j+1} \bmod 8\bigr) + \frac{\mu}{16}.
   ```
   Under the **2-column** independent comparison hypothesis $H_2^{\mathrm{adj}}$ ($\limsup \frac{1}{N} \sum_{j \le N} \Psi_{2,\mathrm{adj}}(J_j \bmod 4, J_{j+1} \bmod 8) \le \mathbb{E}_{Q^{(1/2) \otimes 2}}[\Psi_{2,\mathrm{adj}}]$), we obtain the certified enclosure
   ```math
   \mathbb{E}_{Q^{(1/2) \otimes 2}}[\Psi_{2, \mathrm{adj}}] \in [0.356817, 0.356889], \qquad
   \limsup_{N \to \infty} f_{1, N}(E(4); 2) \le 0.486661 < \frac{1}{2}, \qquad
   D^-(E(4); 2) \ge 0.013339 > 0.
   ```
3. *(Exact 1-column + all-order stationarity converse.)* Let $p_J(a) := \Pr_{Q^{(1/2)}}(J \equiv a \pmod 8)$ ($p_J(0) \in [0.609692, 0.609710] > \frac{1}{2}$). The shift-invariant mixture of periodic sequences placing mass $2 p_J(a)$ on the period-$2$ orbit $(0, a, 0, a, \ldots)$ for each $a \in \{1, \ldots, 7\}$ and mass $2 p_J(0) - 1 > 0$ on the constant sequence $(0, 0, 0, \ldots)$ is **stationary of every order**, has exact 1-column marginal $p_J$ on $\mathbb{Z}/8\mathbb{Z}$, and satisfies
   ```math
   \mathbb{E}\!\left[\frac{R_3}{8}\right]
     = \sum_{a = 1}^{7} p_J(a) \cdot \frac{(2a \bmod 8) + (5a \bmod 8)}{8}
     \ge 0.380742 > 0.370231 \ge t_3.
   ```
   Hence 1-column laws plus arbitrary stationarity cannot decide $E(4)$ through $W = 3$; the exact column-interaction threshold is **$k_{\min}(E(4); W = 3) = 2$** (compared with $k \ge 5$ in `CC-49` for $E(2)$).

*Proof.* (1) Write $4 a_1 + 2 a_2 + a_3 \equiv 4 a_1 + r_{23} \pmod 8$.
- If $a_1 = 0$: LHS is $r_{23}/8$. When $a_2 \in \{0, 1\}$, $u = 0$ and $v = r_{23}/8$ (equality). When $a_2 \in \{2, 3\}$, $u = 1$, while $v = r_{23}/8 - 1$ if $r_{23} \ge 4$ (equality) and $v = r_{23}/8$ if $r_{23} < 4$ (slack $+1$).
- If $a_1 = 1$: LHS is $((4 + r_{23}) \bmod 8)/8 = \frac{1}{2} + \frac{r_{23}}{8} - \mathbf{1}[r_{23} \ge 4]$, whereas $u + v = \frac{1}{2} + \frac{r_{23}}{8} - \mathbf{1}[a_2 \in \{2, 3\},\, r_{23} \ge 4] \ge \mathrm{LHS}$, with equality whenever $r_{23} < 4$ or $a_2 \in \{2, 3\}$, and slack $+1$ on the $8$ triples with $a_1 = 1, a_2 \in \{0, 1\}, r_{23} \ge 4$.
In total, exact equality holds on $48/64$ triples and slack $+1$ on the $16$ triples $\{(0, a_2, a_3) : a_2 \in \{2, 3\}, r_{23} < 4\} \cup \{(1, a_2, a_3) : a_2 \in \{0, 1\}, r_{23} \ge 4\}$ (exhaustively verified in `scripts/phase26_mesoscopic_carries.py` Section 1.4).
(2) Applying (1) to $(a_1, a_2, a_3) = (J_{j+1} \bmod 2, J_{j+2} \bmod 4, J_{j+3} \bmod 8)$ and shifting the index of $u(J_{j+1} \bmod 2, J_{j+2} \bmod 4)$ by $1$ introduces only an $O(1/N)$ boundary term, yielding the unconditional Cesàro bound; `scripts/phase26_mesoscopic_carries.py` Section 1 certifies the exact `Fraction` enclosure of $\mathbb{E}_{Q^{(1/2)\otimes 2}}[\Psi_{2,\mathrm{adj}}]$.
(3) In the period-$2$ orbit $(0, a, 0, a, \ldots)$, each symbol $0$ and $a$ occurs with frequency $\frac{1}{2}$, and the two 3-step windows $(0, a, 0)$ and $(a, 0, a)$ occur with equal frequency $\frac{1}{2}$ and values $(2a \bmod 8)/8$ and $(5a \bmod 8)/8$. Weighting by $2 p_J(a)$ gives 1-column marginal $p_J(a)$ on every $a \in \{1, \ldots, 7\}$ and $\sum_{a=1}^7 p_J(a) + (2 p_J(0) - 1) = p_J(0)$ on $0$, with exact expectation $\sum_{a=1}^7 p_J(a) \frac{(2a \bmod 8) + (5a \bmod 8)}{8} \ge 0.380742$. $\square$

*(Remark: Adding the non-adjacent pair $(J_1, J_3)$ lowers the 2-column LP optimum slightly further to $\approx 0.349131$, while the general 3-column stationary LP over 1-column marginals achieves $\approx 0.402934$; the closed-form star-orbit mixture already establishes the converse cleanly with zero numerical inversion.)*

### 1.2 Exact factorial-moment order hierarchy for $E(4)$ at $W = 3$

How many joint factorial moments of the marked column arrival counts $\mathbf{N}(j) \in \mathbb{Z}_{\ge 0}^7$ suffice to prove $\mathbb{E}[R_3/8] < t_3$? Resolving `GF-41` Open Question 6, we establish sharp finite-order upper and lower bounds in both the general 7-variable marked model and the i.i.d.-mark 3-variable count model.

**Theorem C1.2 (Factorial-moment order hierarchy for $E(4)$ at $W = 3$; Paper proof + Finite certificate, zero floats).**
1. *(General 7-variable marked counts: $4 \le r_{\min}^{\mathrm{marked}}(E(4); W = 3) \le 7$.)*
   - *Lower bound ($r = 3$ fails):* There exists a probability distribution on $\mathbb{Z}_{\ge 0}^7$ matching **all $120$ joint falling-factorial moments of order $\le 3$** of independent Poisson random variables with exact intensities $\boldsymbol{\lambda} = (\frac{1}{2}; \frac{\nu_1+\nu_5}{2}, \frac{\nu_3+\nu_7}{2}; \frac{\nu_1}{2}, \frac{\nu_3}{2}, \frac{\nu_5}{2}, \frac{\nu_7}{2})$, yet satisfying $\mathbb{E}[R_3/8] \ge 0.378089 > 0.370231 \ge t_3$.
   - *Upper bound ($r = 7$ succeeds globally using **2-column** moments only):* There exists an explicit degree-$7$ polynomial $P_7(\mathbf{N}) = P_7^{(1)}(N_1) + P_7^{(w)}(N_1, N_{2,1}, N_{2,3}) + P_7^{(v')}(N_{2,1}, N_{2,3}, N_{3,1}, N_{3,3}, N_{3,5}, N_{3,7})$ (involving **no** 3-column cross-moments) satisfying $P_7(\mathbf{x}) \ge R_3(\mathbf{x})/8$ identically for **all** $\mathbf{x} \in \mathbb{Z}_{\ge 0}^7$ and
     ```math
     \mathbb{E}_{\mathrm{Pois}(\boldsymbol{\lambda})}[P_7(\mathbf{N})] \le 0.369593 < 0.370228 \le t_3.
     ```
2. *(i.i.d.-mark 3-variable counts: $r_{\min}^{\mathrm{iid}}(E(4); W = 3) = 3$ exact.)* Let $f_{\mathrm{iid}}(n_1, n_2, n_3) := \mathbb{E}[R_3/8 \mid N_1 = n_1, N_2 = n_2, N_3 = n_3]$ when arrival marks are i.i.d. $\nu$.
   - *Lower bound ($r = 2$ fails):* The explicit 8-atom rational probability distribution on $\mathbb{Z}_{\ge 0}^3$,
     ```math
     \begin{aligned}
     \Pr(0,0,0) &= \tfrac{6}{24},\quad \Pr(0,1,0) = \tfrac{4}{24},\quad \Pr(0,1,1) = \tfrac{3}{24},\quad \Pr(0,1,3) = \tfrac{1}{24}, \\
     \Pr(1,0,0) &= \tfrac{2}{24},\quad \Pr(1,0,1) = \tfrac{6}{24},\quad \Pr(1,3,0) = \tfrac{1}{24},\quad \Pr(3,1,0) = \tfrac{1}{24},
     \end{aligned}
     ```
     matches all $10$ falling-factorial moments $(1/2)^{a+b+c}$ ($a + b + c \le 2$) of $\mathrm{Pois}(1/2)^3$ identically and satisfies $\mathbb{E}[f_{\mathrm{iid}}(N_1, N_2, N_3)] \ge 0.400955 > 0.370231 \ge t_3$.
   - *Upper bound ($r = 3$ succeeds globally):* There exists an explicit rational degree-$3$ polynomial $P_3(n_1, n_2, n_3)$ (denominator $10^5$, given in `scripts/phase26_mesoscopic_carries.py` Section 2.4) satisfying $P_3(n_1, n_2, n_3) \ge f_{\mathrm{iid}}(n_1, n_2, n_3)$ for **every** $(n_1, n_2, n_3) \in \mathbb{Z}_{\ge 0}^3$ and
     ```math
     \mathbb{E}_{\mathrm{Pois}(1/2)^3}[P_3(N_1, N_2, N_3)] \le 0.369859 < 0.370228 \le t_3.
     ```

*Proof.*
- *(1, lower bound):* Keep $(N_{3,3}, N_{3,5}, N_{3,7})$ independent with the closed-form 1D order-$3$ Poisson-matched laws $p_3 = \lambda^3/6$, $p_2 = (\lambda^2 - \lambda^3)/2$, $p_1 = \lambda - \lambda^2 + \lambda^3/2$, $p_0 = 1 - \lambda + \lambda^2/2 - \lambda^3/6$ on $\{0, 1, 2, 3\}$ (strictly positive for every $\lambda \in (0, 1)$). On the remaining 4 variables $(N_1, N_{2,1}, N_{2,3}, N_{3,1})$, choose the explicit 35-point support `pts4_35` in `scripts/phase26_mesoscopic_carries.py` Section 2.1. The $35 \times 35$ falling-factorial moment matrix $B$ is inverted exactly over $\mathbb{Q}$ (`frac_mat_inv`), giving $\|B^{-1}\|_\infty < 20$. For every true $\boldsymbol{\lambda}$ in the certified Section 1 enclosure, every coordinate of $B^{-1} \mathbf{b}(\boldsymbol{\lambda})$ is certified strictly positive and yields $\mathbb{E}[R_3/8] \ge 0.378089$. By independence of the remaining three coordinates, all $120$ 7-variable moments of order $\le 3$ match $\mathrm{Pois}(\boldsymbol{\lambda})$ identically.
- *(1, upper bound — Shifted Split-Bonferroni):* For any bounded function $g : \mathbb{Z}_{\ge 0}^d \to (-\infty, U_g]$ and total count $S(\mathbf{x}) = \sum_{i=1}^d x_i$, write
  ```math
  g(\mathbf{x}) \le U_g - \sum_{|\mathbf{k}| \le r - 1} \bigl(U_g - g(\mathbf{k})\bigr)\, \mathbf{1}[\mathbf{x} = \mathbf{k}].
  ```
  For every integer $t \ge 0$ and every **odd** integer $K \ge 1$, the binomial identity $\sum_{j=0}^K (-1)^j \binom{t}{j} = \mathbf{1}[t = 0] - \binom{t - 1}{K}\mathbf{1}[t \ge 1] \le \mathbf{1}[t = 0]$ holds globally. Setting $K(s) := r - s$ if $r - s$ is odd and $r - s - 1$ if $r - s$ is even (always odd and $\ge 1$ for $0 \le s \le r - 1$), the degree-$\le r$ polynomial
  ```math
  P_r^{(g)}(\mathbf{x}) := U_g - \sum_{|\mathbf{k}| \le r - 1} \bigl(U_g - g(\mathbf{k})\bigr) \left(\prod_{i=1}^d \binom{x_i}{k_i}\right) \sum_{j = 0}^{K(|\mathbf{k}|)} (-1)^j \binom{S(\mathbf{x}) - |\mathbf{k}|}{j}
  ```
  satisfies $P_r^{(g)}(\mathbf{x}) \ge g(\mathbf{x})$ globally on $\mathbb{Z}_{\ge 0}^d$: if $x_i < k_i$ for some $i$ the indicator lower bound vanishes; if $\mathbf{x} = \mathbf{k}$ it equals $1$; if $\mathbf{x} \ge \mathbf{k}$ with $t = S(\mathbf{x}) - |\mathbf{k}| \ge 1$ it is $\le 0$. Under independent $\mathrm{Pois}(\lambda_1, \ldots, \lambda_d)$ with $\Lambda = \sum_i \lambda_i$,
  ```math
  \mathbb{E}[P_r^{(g)}] = U_g - \sum_{s = 0}^{r - 1} \bigl(U_g - \mathbb{E}[g \mid S = s]\bigr) \frac{\Lambda^s}{s!} \sum_{j = 0}^{K(s)} \frac{(-\Lambda)^j}{j!}.
  ```
  Applying this at $r = 7$ to the three shifted 2-column pieces of Theorem C1.1(1)—namely $\frac{1}{2}\mathbf{1}[a_1 = 1]$ ($U = \frac{1}{2}, \Lambda = \frac{1}{2}$), $w(a_1, a_2)$ ($U = \frac{1}{2}, \Lambda = 1$), and $v'(a_2, a_3)$ ($U = \frac{7}{8}, \Lambda = 1$)—yields the certified global bound $\mathbb{E}[P_7] \le 0.369593 < 0.370228$.
- *(2, lower and upper bounds):* The 8-atom verification at $r = 2$ is exact finite rational arithmetic. For $r = 3$, expanding $P_3$ in standard monomials $n_1^i n_2^j n_3^k$ reveals all degree-$3$ coefficients $\ge 0$ (with pure cubes $a_1, a_2, a_3 > 0$) and all negative degree-$2$ cross-terms $-b_{ij} n_i n_j$ bounded via Young's inequality $n_i n_j \le \frac{r_{ij}}{2} n_i^2 + \frac{1}{2 r_{ij}} n_j^2$ ($r_{12} = 2, r_{13} = 4, r_{23} = 2$), separating $P_3(n_1, n_2, n_3) \ge f_1(n_1) + f_2(n_2) + f_3(n_3) + c_0$. Exact derivative monotonicity of the three 1D cubics $f_i$ certifies $P_3 \ge \frac{7}{8} \ge f_{\mathrm{iid}}$ everywhere outside $[0, 9] \times [0, 9] \times [0, 17]$, while all $1{,}800$ interior lattice points are verified in exact `Fraction` arithmetic in `scripts/phase26_mesoscopic_carries.py` Section 2.4. $\square$

*(Structural insight: Comparing (1) and (2) proves that mark–column decoupling at order $3$ strictly separates the i.i.d.-mark threshold $r_{\min}^{\mathrm{iid}} = 3$ from the general marked threshold $r_{\min}^{\mathrm{marked}} \ge 4$.)*

### 1.3 Exact Fourier and trigonometric thresholds for $E(4)$ and $E(2)$

**Theorem C1.3 (Exact Fourier thresholds on $\mathbb{Z}/8\mathbb{Z}$ and $\mathbb{R}/\mathbb{Z}$ for $E(4)$, and $W = 8$ Bonferroni reduction for $E(2)$; Paper proof + Finite certificate, zero floats).**
1. *(Exact $\mathbb{Z}/8\mathbb{Z}$ harmonic necessity.)* On $\mathbb{Z}/8\mathbb{Z}$, $\mathbb{E}_{Q_3^{(1/2)}}[R_3/8] \in [0.323087, 0.323132]$, and **every** proper subset $S \subsetneq \{1, 2, 3, 4\}$ of non-trivial harmonics fails to beat $t_3$: dropping $h^* \in \{1, 2, 3, 4\}$ admits an exact probability measure matching all remaining harmonics with $\mathbb{E}[R_3/8] \ge 0.45931$ ($h^* = 1$), $0.44098$ ($h^* = 2$), $0.37470$ ($h^* = 3$), and $0.37176$ ($h^* = 4$), all strictly exceeding $0.370231$.
2. *(Exact trigonometric majorant degree on $\mathbb{R}/\mathbb{Z}$: $M_{\min}(E(4)) = 12$ exact.)* Let $\phi_{E(4)}(h) := \mathbb{E}_{Q^{(1/2)}}[e^{2\pi i h X}] = \exp\bigl(\frac{1}{2} \sum_{j \ge 1} (\mathbb{E}_U[e^{2\pi i h U / 2^j}] - 1)\bigr)$ ($h \in \mathbb{Z}_{\ge 1}$, satisfying $\phi_{E(4)}(2^a h_{\mathrm{odd}}) = \phi_{E(4)}(h_{\mathrm{odd}})$).
   - *Degree $M = 12$ succeeds globally:* The explicit rational trigonometric polynomial $T_{12}(t) = a_0 + \sum_{h=1}^{12} (a_h \cos(2\pi h t) + b_h \sin(2\pi h t))$ with denominator $10{,}000$,
     ```math
     a_0 = \frac{5809}{10000}, \quad
     10^4 \mathbf{a} = (85, 1355, 26, 1080, -14, 798, -31, 538, -38, 304, -29, 123),
     ```
     ```math
     10^4 \mathbf{b} = (-6289, -232, -1968, -371, -1040, -427, -600, -412, -333, -322, -141, -178),
     ```
     satisfies $T_{12}(t) \ge \mathbf{1}_{[1/2, 1)}(t)$ **globally for all $t \in \mathbb{R}/\mathbb{Z}$** and
     ```math
     \mathbb{E}_{Q^{(1/2)}}[T_{12}(X)] \in [0.497296, 0.497302] < \frac{1}{2}.
     ```
   - *Degree $M = 11$ fails:* There exists a discrete probability measure $\mu_{11}$ supported on $23$ rational atoms in $[0, 1)$ matching **all $22$ real Fourier moments** $(\Re\phi_{E(4)}(h), \Im\phi_{E(4)}(h))$ for $1 \le h \le 11$ identically, with $\mu_{11}([1/2, 1)) \ge 0.503909 > \frac{1}{2}$.
   Hence **$M_{\min}(E(4)) = 12$ exact** (compare `CC-49`'s $111 \le M_{\min}(E(2)) \le 116$).
3. *(Track C2: $E(2)$ at $W = 8$ Bonferroni order reduction from $r = 92$ to $r = 46$.)* Under `GF-41` Remark 2.5 ($B_8^{(1)} \le 0.497108$, margin $\frac{1}{2} - B_8^{(1)} \ge 0.0028923$, total Poisson intensity $\Lambda = 8$), the global degree-$r$ Bonferroni upper polynomial $P_r$ on $\mathbb{Z}_{\ge 0}^{255}$ has exact excess over $\mathbb{E}_{Q_8^{(1)}}[R_8/256]$ bounded by
   ```math
   \mathbb{E}_{Q_8^{(1)}}\bigl[P_r - R_8/256\bigr] \le \frac{255}{256}\left[\sum_{s = 0}^{r - 1} \frac{8^s}{s!}\left(e^{-8} - \sum_{j = 0}^{K(s)} \frac{(-8)^j}{j!}\right) + \Pr(\mathrm{Pois}(8) \ge r)\right].
   ```
   At $r = 46$, this exact upper bound is **$\le 0.002220 < 0.0028923$** (whereas $r = 44$ gives $0.017946$), **halving** `CC-49`'s $D = 16$ Bonferroni order $r = 92$ and bringing the required joint factorial-moment order for $E(2)$ down to $r = 46$.

*Proof.*
- *(1)* For each dropped $h^* \in \{1, 2, 3, 4\}$, Section 3.1 of `scripts/phase26_mesoscopic_carries.py` adds a certified kernel vector orthogonal to $\{1, 2, 3, 4\} \setminus \{h^*\}$ while preserving nonnegativity on all $8$ residues.
- *(2, global Sturm positivity at $M = 12$)* Substitute $u = \tan(\pi t)$ so $\cos(2\pi t) = \frac{1 - u^2}{1 + u^2}$ and $\sin(2\pi t) = \frac{2u}{1 + u^2}$. Then $t \in [0, \frac{1}{2}]$ corresponds to $u \in [0, +\infty]$ and $t \in [\frac{1}{2}, 1]$ corresponds to $u = -v$ with $v \in [0, +\infty]$. Consequently $T_{12}(t) > 0$ on $[0, \frac{1}{2}]$ and $T_{12}(t) > 1$ on $[\frac{1}{2}, 1]$ iff the exact degree-$24$ rational polynomials $P_{\mathrm{up}}(u) := (1 + u^2)^{12} T_{12}(t)$ and $P_{\mathrm{lo}}(v) := (1 + v^2)^{12} (T_{12}(-t) - 1)$ are strictly positive at $0$ and $+\infty$ and have **zero real roots in $(0, +\infty)$**. Exact rational Sturm sequences in `scripts/phase26_mesoscopic_carries.py` Section 3.3 certify $P_{\mathrm{up}}(0) > 0$, $P_{\mathrm{up}}(+\infty) > 0$, $\mathrm{roots}_{(0,\infty)}(P_{\mathrm{up}}) = 0$ and $P_{\mathrm{lo}}(0) > 0$, $P_{\mathrm{lo}}(+\infty) > 0$, $\mathrm{roots}_{(0,\infty)}(P_{\mathrm{lo}}) = 0$ with zero discretization error.
- *(2, $M = 11$ countermeasure via Neumann series)* Section 3.2 certifies $(\Re\phi_{E(4)}(h), \Im\phi_{E(4)}(h))$ for odd $h \le 11$ to width $\le 4.0 \times 10^{-6}$ via a tightened $U$-pmf up to $U \le 4095$ (primes $\le 400{,}000$ + 30-wheel tail). On the $23$ rational atoms `t11_rat`, Section 3.4 computes an approximate inverse $R$ in pure 64-bit fixed-point integer arithmetic and verifies $\|R A_{\mathrm{true}} - I\|_\infty \le q \le 10^{-9} \ll 1$, whence Banach's Neumann-series theorem certifies invertibility of the exact $23 \times 23$ trigonometric moment matrix $A_{\mathrm{true}}$ and guarantees that the exact solution $\mathbf{w}_{\mathrm{true}} = A_{\mathrm{true}}^{-1} \mathbf{b}_{\mathrm{true}}$ satisfies $\min_i w_{\mathrm{true}, i} \ge 0.000366 > 0$ and $\sum_{t_i \ge 1/2} w_{\mathrm{true}, i} \ge 0.503909 > \frac{1}{2}$.
- *(3)* Direct pure-`Fraction` evaluation of the alternating-series Bonferroni excess in Section 3.5. $\square$

### 1.4 Unconditional arithmetic moments and dual LP barriers

We now compare what **can** be proved unconditionally for the actual arithmetic displaced arrivals of $E(2^k)$ against the sharp dual thresholds of Theorems C1.1–C1.3.

**Theorem C1.4 (Unconditional arithmetic displaced-arrival moments & dual LP barriers; Paper proof + Finite certificate; External inputs: Wirsing 1967, Halász 1968, 2-D Fundamental Lemma / Selberg sieve).**
For $E(2^k)$ ($k \ge 1$), let $N_j = \#\{m \ge 1 : km - v(m) = j\}$ and $J_j^{(F)} = \sum_{km - v(m) = j} F(o(m))$.
1. *(Unconditionally proved first moments and modular equidistribution.)*
   - For every $F$ on odd integers with $\sum_{s\text{ squarefull}} |F(o(s))|/s < \infty$, $\frac{1}{N} \sum_{j = 1}^N J_j^{(F)} = \frac{1}{k} \mathbb{E}_\nu[F] + o(1)$ (in particular $\frac{1}{N} \sum_{j=1}^N N_j = \frac{1}{k} + O(\frac{\log N}{N})$ and $\frac{1}{N} \sum_{j=1}^N J_j = \frac{\mu}{k} + o(1)$; with $F = \mathbf{1}_{o \equiv r \pmod m}$, every marked arrival density $\frac{1}{N} \sum_{j=1}^N N_{j, r}^{(m)} \to \frac{\nu(r \bmod m)}{k}$).
   - For every modulus $q \ge 2$ and residue $a \bmod q$, $\frac{q}{N} \sum_{j \le N,\, j \equiv a (q)} J_j^{(F)} \to \frac{1}{k} \mathbb{E}_\nu[F]$ (Halász 1968, as in `GF-42` Thm B1.5; for $q = 2$, Wirsing 1967, `GF-41` Thm 3.2).
2. *(Unconditionally proved second moments: mesoscopic and lattice scale.)*
   - *Mesoscopic $G$-window second moment (`GF-42` Thm B1.3 / 2-D Fundamental Lemma):* For every $\varepsilon > 0$ and sufficiently large $G = G(\varepsilon)$, the window count $Z_{j, G} = \sum_{i = 0}^{G - 1} N_{j + i}$ satisfies $\limsup_{N \to \infty} \frac{1}{N} \sum_{j = 1}^N Z_{j, G}^2 \le \frac{G}{k} + (1 + \varepsilon) \frac{G^2}{k^2}$.
   - *New explicit unconditional lattice-scale second-moment upper bound (2-D Selberg sieve):* For every fixed separation $h \ge 0$ (in particular $h = 0$, the single-column factorial second moment $N_j(N_j - 1)$),
     ```math
     \limsup_{N \to \infty} \frac{1}{N} \sum_{j = 1}^{N} N_j (N_j - 1) \le \frac{C_{\mathrm{lat}}}{k^2}, \qquad
     \limsup_{N \to \infty} \frac{1}{N} \sum_{j = 1}^{N} N_j N_{j + h} \le \frac{C_{\mathrm{lat}}}{k^2} \quad (h \ge 1),
     ```
     with the explicit certified absolute constant **$C_{\mathrm{lat}} = 180$** (independent of $k$ and $h$; `scripts/phase26_mesoscopic_carries.py` Section 1.6 and `main()` certify the exact bound $\le 175.42 \cdot \sigma_2(10)^{-1} < 180$).
3. *(Exact dual LP barriers and sufficient inputs for $E(4)$.)* Comparing against the `GF-41` $W = 3$ stationarity threshold $t_3 = \frac{1}{2} - \frac{\mu}{16} \in [0.370228, 0.370231]$:
   - *One-column residue law + all-order stationarity (residue-level barrier):* For residue processes $(J_j \bmod 8)_{j \in \mathbb{Z}}$, matching the exact 1-column residue law $p_J$ of $\mathrm{CP}(1/2, \nu)$ together with arbitrary shift stationarity leaves the worst-case expectation $\ge 0.380742 > 0.370231$ (Theorem C1.1(3); verified in Section 1.5 with exact mass $1$ and exact 1-column marginal $p_J$). *(Note: this star-orbit witness lives on residues in $\mathbb{Z}/8\mathbb{Z}$ and is not lifted to a count process $(N_j, \text{marks})$.)*
   - *Order-3 marked single-window factorial moments (count-level barrier):* For the 7-variable marked arrival counts $\mathbf{N}(j)$ in a single $W = 3$ window, matching **all $120$ exact joint falling-factorial moments of order $\le 3$** of $\mathrm{Pois}(\boldsymbol{\lambda})$—which in particular forces all six derived column-count second factorial moments $\mathbb{E}[N_i(N_i - 1)] = \frac{1}{4}$ and $\mathbb{E}[N_i N_{i'}] = \frac{1}{4}$ ($1 \le i < i' \le 3$, asserted identically in Section 2.1)—still leaves the dual-LP maximum $\ge 0.378089 > 0.370231$ (Theorem C1.2(1)).
   - *Order-2 i.i.d.-mark count moments & degree-11 circular Fourier moments:* Even under i.i.d. marks $\nu$, matching all $10$ falling-factorial moments of $(N_1, N_2, N_3)$ of order $\le 2$ (including all exact second moments $= 1/4$) fails ($\ge 0.400955$, Theorem C1.2(2)); on $\mathbb{R}/\mathbb{Z}$, matching all $22$ real circular Fourier moments for $1 \le h \le 11$ fails ($\mu_{11}([1/2, 1)) \ge 0.503909 > \frac{1}{2}$, Theorem C1.3(2)).
   - *Sufficient arithmetic inputs crossing the $E(4)$ threshold:* Within the `GF-41` $W = 3$ stationarity / circular-Fourier framework, proving $\limsup f_1(E(4); 2) < \frac{1}{2}$ **is achieved by any one** of the following sufficient inputs at lattice resolution $d \asymp \sqrt{\log\log M}$ (these are proved sufficient, not claimed necessary across all possible proof methods):
     - the **2-column adjacent residue law** $(J_j \bmod 4, J_{j+1} \bmod 8)$ ($H_2^{\mathrm{adj}}$, Theorem C1.1(2)), which is implied by 2-column joint marked factorial moments of order $\le 7$ (Theorem C1.2(1));
     - exact **order-3 column-count factorial moments** of $(N_1, N_2, N_3)$ *together with* asymptotic mark–column independence (Theorem C1.2(2));
     - the first **$12$ circular Fourier moments** $\frac{1}{N} \sum_{j < N} e(h \cdot 2^j E(4))$ ($1 \le h \le 12$, Theorem C1.3(2)).

*Proof of (2), lattice-scale bound ($C_{\mathrm{lat}} = 180$).* Fix $k \ge 1$, $h \in \mathbb{Z}_{\ge 0}$, and a fixed prime cutoff $p_1 \ge 5$ (taken arbitrarily large after $N \to \infty$). Put $M := \lfloor N/k \rfloor + \lceil 2 \log_2 N \rceil$ (so every $m$ with $km - v(m) \le N$ lies in $[1, M]$ for large $N$, since $v(m) \le \log_2 m$) and $L := \log\log M$. Both $\sum_{j=1}^N N_j(N_j - 1)$ (at $h = 0$) and $\sum_{j=1}^N N_j N_{j+h}$ (at $h \ge 1$) are bounded by
```math
S(M; k, h) := \sum_{d \in \mathbb{Z} \setminus \{0\}} \#\bigl\{m \in [1, M] : m + d \in [1, M],\; v(m + d) - v(m) = kd - h\bigr\}.
```
We partition the pairs $(m, m + d)$ into four pieces:
1. *Large-shift tail $|d| > D_0 := \lceil (10 L + h)/k \rceil$:* If $d > D_0$, then $v(m + d) \ge kd - h > 10 L$, forcing $\tau(m + d) \ge 2^{v(m+d)} > 2^{10 L}$; for each fixed $n = m + d \le M$, at most $(v(n) + h)/k \le \tau(n) + h$ values of $d > D_0$ can occur. Using $\tau(n)^2 \le \tau_4(n)$ (since $(e+1)^2 \le \binom{e+3}{3}$ for every $e \ge 0$), $\sum_{n \le M,\, \tau(n) > 2^{10L}} (\tau(n) + h) \ll_h 2^{-10 L} \sum_{n \le M} \tau_4(n) \ll_h M (\log M)^{3 - 10\ln 2} = o(M)$. The range $d < -D_0$ is symmetric (forcing $\tau(m) > 2^{10 L}$).
2. *Large prime powers at $p \le p_1$ or large squarefull part $> L^4$ at $p > p_1$:* For $n \ge 1$, write $n = s_{\le p_1}(n) \cdot s_{> p_1}(n) \cdot r_{> p_1}(n)$, where $s_{\le p_1}(n) = \prod_{p \le p_1} p^{v_p(n)}$, $s_{> p_1}(n)$ is the squarefull part of $n / s_{\le p_1}(n)$, and $r_{> p_1}(n)$ is squarefree and coprime to $s_{\le p_1}(n) s_{> p_1}(n)$. The number of $n \le M$ with $p^{v_p(n)} > L^4$ for some $p \le p_1$ is $\le \pi(p_1) M / L^4$; the number with $s_{> p_1}(n) > L^4$ is $\le M \sum_{s > L^4,\, s\text{ sqfull}} 1/s \ll M / L^2$ (since every squarefull integer writes uniquely as $a^2 b^3$ with $b$ squarefree, so $\sum_{s > Y,\, s\text{ sqfull}} 1/s \ll Y^{-1/2}$). Multiplying by $2 D_0 = O(L)$ choices of $d$ bounds all pairs violating $p^{v_p} \le L^4$ ($\forall p \le p_1$) and $s_{> p_1} \le L^4$ by $O_{p_1}(M / L) = o(M)$.
3. *Small-prime tail $U_d(m; z_J) > M^{1/4}$:* Define dyadic cutoffs $z_j := M^{1/w_j}$ with $w_j := 24 \cdot 2^j$ ($0 \le j \le J$, where $J$ is least with $w_J \ge 24 \log L$, so $w_J < 48 \log L$), and put $U_d(m; z) := \prod_{p_1 < p \le z,\, p \nmid d s_1 s_2,\, p \mid m(m+d)} p$ (where $s_1 = s_{> p_1}(m)$ and $s_2 = s_{> p_1}(m+d)$). Whenever $U_d(m; z_J) > M^{1/4}$, at least one of $n \in \{m, m+d\}$ has squarefree radical $u(n; z_J) := \prod_{p \le z_J,\, p \mid n} p > M^{1/8}$. Applying the elementary Rankin bound with $\alpha_J = 1/\log z_J = w_J / \log M$ (expanding $u(n; z_J)^{\alpha_J} = \sum_{r \mid u(n; z_J)} \mu^2(r) \prod_{p \mid r} (p^{\alpha_J} - 1)$ and summing $\lfloor M/r \rfloor \le M/r$ gives $\sum_{n \le M} u(n; z_J)^{\alpha_J} \le M \prod_{p \le z_J}(1 + \frac{p^{\alpha_J}-1}{p}) \ll M$) yields $\#\{n \le M : u(n; z_J) > M^{1/8}\} \ll M e^{-w_J/8} \le M / L^3$. Multiplying by $2 \cdot 2 D_0 = O(L)$ gives $O(M / L^2) = o(M)$.
4. *Remaining pairs on shells $I_0$ ($U_d(m; z_0) \le M^{1/4}$) and $I_j = I_j^{(a)} \cup I_j^{(b)}$ ($1 \le j \le J$, $U_d(m; z_j) \le M^{1/4} < U_d(m; z_{j-1})$):* Fix $1 \le |d| \le D_0$, exact $p \le p_1$ valuations $(e_{1, p}, e_{2, p})$ with $p^{e_{i, p}} \le L^4$, and squarefull parts $s_1, s_2 \le L^4$ (made of primes $> p_1$). The congruence event $\{v_p(m) = e_{1, p},\, v_p(m+d) = e_{2, p}\ (\forall p \le p_1);\; p^{v_p(s_1)} \parallel m,\, p^{v_p(s_2)} \parallel (m+d)\ (\forall p \mid s_1 s_2)\}$ is periodic modulo $Q \le L^{8\pi(p_1) + 16} = M^{o(1)}$ with exact local density $\rho_{\mathrm{loc}}(e_1, e_2, s_1, s_2; d) = \prod_{p \le p_1} \rho_p(e_{1, p}, e_{2, p}; v_p(d)) \cdot \prod_{p \mid s_1 s_2} \rho_p(v_p(s_1), v_p(s_2); v_p(d))$. Crucially, for **every** $d \ne 0$, summing over all $(e_{1, p}, e_{2, p})$ at $p \le p_1$ gives $\le 1$ per prime (partition of $\mathbb{Z}_p$), and summing over all $(s_1, s_2)$ at $p > p_1$ gives at most $\prod_{p > p_1}(1 + \Pr_{\mathbb{Z}_p}(p^2 \mid m \text{ or } p^2 \mid m+d)) \le \prod_{p > p_1}(1 + 2/p^2) = 1 + O(1/p_1)$ **uniformly in $d$**! Furthermore, the shift from $p \le p_1$ and $(s_1, s_2)$ satisfies $|v_{\le p_1}(m+d) - v_{\le p_1}(m)| + |v(s_2) - v(s_1)| \le \pi(p_1) \log_2(4 \log_2 L + 2) + 4 \log_2 L = O_{p_1}(\log L)$, while every prime $p \in (p_1, z_j]$ dividing $d$ (with $p \nmid s_1 s_2$) cancels from $v(m+d) - v(m)$, and $\Delta_{> z_j} := \omega_{> z_j}(m+d) - \omega_{> z_j}(m) \in [-w_j, w_j]$ takes $2 w_j + 1$ values. Thus the total shift satisfies $|\Delta| \le B_j := h + O_{p_1}(\log L) + w_j = O_{p_1}(\log L) = o(\sqrt{L})$.
   - On $I_0$: apply the **2-D Selberg upper-bound sieve** (Friedlander–Iwaniec, *Opera de Cribro*, 2010, Thm 7.1) on $\mathcal{P}_d^{(0)} = \{p \in (p_1, z_0] : p \nmid d s_1 s_2\}$ at level $D = M^{1/2}$ (parameter $s_0 = \frac{\log D}{\log z_0} = w_0/2 = 12 > 10$, multiplier $\le 1/\sigma_2(10) + o(1)$).
   - On $I_j^{(a)}$ ($M^{1/8} < U_d(m; z_j) \le M^{1/4}$): apply the 2-D Selberg sieve at $D = M^{1/2}$ ($s_j = w_j/2 \ge 24 > 10$) with Rankin weight $(u_1 u_2)^{\eta_j} M^{-\eta_j/8}$ ($\eta_j = 1/\log z_j$, contributing $e^{-w_j/8 + 2\mathrm{Ein}(1) + O(1/p_1) + o(1)}$ inside the Cramér Fourier integral as in Theorem C4.2 below).
   - On $I_j^{(b)}$ ($U_d(m; z_j) \le M^{1/8}$ and $V_j := U_d(m; z_{j-1})/U_d(m; z_j) > M^{1/8}$): since every prime in $V_j$ is $\le z_{j-1} = M^{2/w_j}$, $\omega(V_j) \ge w_j/16 > r_j := 2^j = w_j/24$; choosing $r_j$ distinct primes in $(z_j, z_{j-1}]$ gives $W = W_1 W_2 \le z_{j-1}^{r_j} = M^{1/12}$ with $U_d(m; z_j) W \le M^{5/24} < M^{1/4}$, and summing over $W$ yields $\frac{(2\ln 2 + o(1))^{r_j}}{r_j!}$.
   - Across all $0 \le j \le J$, $1 \le |d| \le D_0$, $(e_1, e_2, s_1, s_2)$, and $u_1 u_2 W \le M^{1/4}$, the total Selberg sieve remainder is $O_{p_1}(L^{8\pi(p_1)+21} (\log L) \cdot M^{1/4} (\log M)^2 \cdot M^{1/2} (\log M)^5) = O(M^{3/4+\varepsilon}) = o(M)$.
   - In every shell's Cramér Fourier local bound (with $E_d = \sum_{p \in \mathcal{P}_d^{(j)}} 1/p \sim L$ uniformly for $1 \le |d| \le D_0$), bounding $\exp(-(kd - \Delta)^2/(4 E_d))$ uniformly over $|\Delta| \le B_j$ by $\exp(-(|kd| - B_j)_+^2/(4 E_{\max}))$ decouples the Gaussian from $(e_1, e_2, s_1, s_2)$, allowing $\rho_{\mathrm{loc}}$ to be summed pointwise at each $d$ to $\le 1 + O(1/p_1)$. Summing the shifted Gaussian over $1 \le |d| \le D_0$ yields $\frac{1}{k} + O(B_j / (k \sqrt{L})) = \frac{1}{k} + o(1)$ uniformly across all $0 \le j \le J$. Dividing by $N = kM + O(\log N)$, letting $N \to \infty$ and then $p_1 \to \infty$, gives
     ```math
     \limsup_{N \to \infty} \frac{S(M; k, h)}{N}
       \le \frac{1}{k^2 \sigma_2(10)} \left[49 + \sum_{j = 1}^{\infty} (2 w_j + 1)\left(e^{-w_j/8 + 2\mathrm{Ein}(1)} + \frac{(2 \ln 2)^{2^j}}{(2^j)!}\right)\right]
       \le \frac{180}{k^2},
     ```
     certified in pure `Fraction` arithmetic in `scripts/phase26_mesoscopic_carries.py` Section 1.6 and `main()`. $\square$

---

## 2. Track C3: The $E^*(4)$ Unitary Lambert Boundary ($q(n) = 2n - \omega(n)$)

Recall from `GF-41` Theorem 4.1 that $E^*(4) = \sum_{n \ge 1} 2^{-q(n)}$ ($q(n) = 2n - \omega(n)$) sits at the exact zero-carry boundary: $f_{1, N}(E^*(4); 2) = \frac{1}{2} - \frac{K^*(N)}{N} + O(\frac{\log N}{N})$, so **any positive lower density of collisions** $\mathcal{C} = \{n : \exists n' > n,\, q(n') = q(n)\}$ immediately proves unconditional simple nonnormality of $E^*(4)$ (`GF-41` Thm 4.3). Here we unconditionally prove `PUB(C)` in `GF-41` Theorem 4.3, prove two new unconditional collision lower bounds (one with **zero external inputs**, one polynomial in $1/\log N$), and isolate the exact remaining parity obstruction.

### 2.1 Unconditional proof of `PUB(C)` in `GF-41` Theorem 4.3

**Theorem C3.1 (Unconditional triple-collision pair upper bound `PUB(C)`; Paper proof; External input: upper bound of the 3-D Fundamental Lemma of the Combinatorial Sieve).**
There exists an absolute constant $C > 0$ such that for all sufficiently large $x$, putting $I = (x/2, x]$ and $L = \log\log x$, uniformly for every pair of integers $1 \le d < d' \le \sqrt{L}$,
```math
\#\bigl\{n \in I : \omega(n + d) - \omega(n) = 2d,\; \omega(n + d') - \omega(n) = 2d'\bigr\}
  \le \frac{C |I|}{L}.
```
Consequently, `PUB(C)` in `GF-41` Theorem 4.3 holds unconditionally, and **simple nonnormality of $E^*(4)$ reduces to `LLB(c)` alone** (even along a single unbounded subsequence of scales $x_j \to \infty$ if one seeks $\liminf f_{1, N} < \frac{1}{2}$).

*Proof.* Fix $1 \le d < d' \le \sqrt{L}$ and write $n_0 = n$, $n_1 = n + d$, $n_2 = n + d'$. Let $\mathcal{Q} := \{p \le 5\} \cup \{p \mid d d' (d' - d)\}$. Since $d, d' \le \sqrt{L}$, $M_{\mathcal{Q}} := \prod_{p \in \mathcal{Q}} p \le 30 L^{3/2}$. Condition on the exact congruence class $n \equiv a \pmod{M_{\mathcal{Q}}}$: for every prime $p \in \mathcal{Q}$, $p \mid n_i \iff p \mid (a + d_i)$ is **deterministic** given $a \bmod M_{\mathcal{Q}}$ (no $p^2$ needed because $\omega$ only counts distinct prime factors). Averaging over all $M_{\mathcal{Q}} \le 30 L^{3/2}$ classes $a \bmod M_{\mathcal{Q}}$, it suffices to prove the bound $O(|I| / (M_{\mathcal{Q}} L))$ uniformly in $a \bmod M_{\mathcal{Q}}$ for the equations
```math
\omega_{\notin \mathcal{Q}}(n_1) - \omega_{\notin \mathcal{Q}}(n_0) = h_1, \qquad
\omega_{\notin \mathcal{Q}}(n_2) - \omega_{\notin \mathcal{Q}}(n_0) = h_2
```
with fixed integers $h_1, h_2$ (depending on $d, d', a$).

Define dyadic prime cutoffs $z_j := x^{1/w_j}$ with $w_j := 40 \cdot 2^j$ for $0 \le j \le J$, where $J$ is the least integer with $w_J \ge 24 \log L$ (so $z_J \ge \exp(c_0 \frac{\log x}{\log L})$). For any $z \ge 7$ put
```math
U(n; z) := \prod_{\substack{p \le z,\; p \notin \mathcal{Q} \\ p \mid n_0 n_1 n_2}} p.
```
Notice that for every prime $p \notin \mathcal{Q}$, $p \nmid d d'(d' - d)$, so $p$ divides **at most one** of $n_0, n_1, n_2$. Partition $I_a := \{n \in I : n \equiv a \pmod{M_{\mathcal{Q}}}\}$ into:
1. *$I_{\mathrm{tail}} := \{n \in I_a : U(n; z_J) > x^{1/4}\}$.* Summing over all $a \bmod M_{\mathcal{Q}}$, for any $n \in I$ with $U(n; z_J) > x^{1/4}$, at least one $i \in \{0, 1, 2\}$ satisfies the squarefree-radical bound $u(n_i; z_J) := \prod_{p \le z_J,\, p \mid n_i} p > x^{1/12}$. Put $\alpha_J := \frac{1}{\log z_J} = \frac{w_J}{\log x}$. Because $u(m; z_J)$ is squarefree, expanding $u(m; z_J)^{\alpha_J} = \sum_{r \mid u(m; z_J)} \mu^2(r) \prod_{p \mid r} (p^{\alpha_J} - 1)$ and summing $\lfloor 2x/r \rfloor \le 2x/r$ elementarily (no Hall–Tenenbaum theorem required!) yields
   ```math
   \#\bigl\{n \in I : U(n; z_J) > x^{1/4}\bigr\}
     \le 3 x^{-\alpha_J / 12} \sum_{m \le 2x} u(m; z_J)^{\alpha_J}
     \le 6 x e^{-w_J / 12} \prod_{p \le z_J} \left(1 + \frac{p^{\alpha_J} - 1}{p}\right)
     \ll x e^{-w_J / 12} \le \frac{x}{L^2} = O\!\left(\frac{|I|}{L}\right),
   ```
   since $\sum_{p \le z_J} \frac{p^{\alpha_J} - 1}{p} = \mathrm{Ein}(1) + O(1) = O(1)$ by Mertens' first theorem.
2. *$I_0 := \{n \in I_a : U(n; z_0) \le x^{1/4}\}$ and shells $I_j := \{n \in I_a : U(n; z_j) \le x^{1/4} < U(n; z_{j-1})\}$ ($1 \le j \le J$).*
   - On $I_0$: every $n_i$ has at most $w_0 = 40$ prime factors $> z_0$. Condition on the exact prime sets $u_i = \prod_{p \le z_0,\, p \notin \mathcal{Q},\, p \mid n_i} p$ ($i = 0, 1, 2$), which are pairwise coprime with $u_0 u_1 u_2 = U(n; z_0) \le x^{1/4}$ and $\gcd(u_0 u_1 u_2, M_{\mathcal{Q}}) = 1$. Since $n_i$ has at most $40$ prime factors $> z_0$, the difference $(\omega(u_1) - \omega(u_0), \omega(u_2) - \omega(u_0))$ lies in the box $[h_1 - 40, h_1 + 40] \times [h_2 - 40, h_2 + 40]$ (at most $81^2 = O(1)$ pairs). For each triple $(u_0, u_1, u_2)$, the sifted set $\{n \in I_a : u_i \mid n_i,\, \gcd(\frac{n_0}{u_0}\frac{n_1}{u_1}\frac{n_2}{u_2}, P_{\mathcal{Q}}(z_0)) = 1\}$ is a 3-dimensional sieve problem of progression length $|I| / (M_{\mathcal{Q}} u_0 u_1 u_2) \ge |I| x^{-1/4} / (30 L^{3/2})$ with $g(p) = 3/p \le 3/7 < 1$ on $p \in (5, z_0] \setminus \mathcal{Q}$. Applying the **upper bound of the 3-D Fundamental Lemma of the Combinatorial Sieve** (Halberstam–Richert Thm 2.5 / Iwaniec–Kowalski §6.4; *External input*) at level $D = x^{1/2}$ ($s = \frac{\log D}{\log z_0} = 20$) yields a uniform main-term factor $O(1)$ and total remainder $\ll L^{3/2} \cdot x^{1/4} (\log x)^3 \cdot x^{1/2} (\log x)^3 = O(x^{3/4 + \varepsilon}) = o(|I|/L)$.
   - Summing the main term over $(u_0, u_1, u_2)$ gives $O(|I|/M_{\mathcal{Q}})$ times $\Pr\bigl((S_1, S_2) \in [h_1 - 40, h_1 + 40] \times [h_2 - 40, h_2 + 40]\bigr)$, where $(S_1, S_2) = \sum_{p \in \mathcal{P}_0} (\eta_{p, 1}, \eta_{p, 2})$ is a sum of independent 4-nomial vectors taking values $(0, 0)$ (prob $1 - 3/p$), $(-1, -1)$ (prob $1/p$, when $p \mid n_0$), $(+1, 0)$ (prob $1/p$, when $p \mid n_1$), and $(0, +1)$ (prob $1/p$, when $p \mid n_2$). By 2-D Fourier inversion, for every $(m_1, m_2) \in \mathbb{Z}^2$:
     ```math
     \Pr(S_1 = m_1,\, S_2 = m_2)
       = \frac{1}{(2\pi)^2} \int_{[-\pi, \pi]^2} e^{-i(m_1 t_1 + m_2 t_2)} \prod_{p \in \mathcal{P}_0} \left(1 + \frac{e^{-i(t_1+t_2)} + e^{it_1} + e^{it_2} - 3}{p}\right) dt_1\, dt_2.
     ```
     Using $|1 + z/p| \le \exp(\frac{\Re z}{p} + \frac{C_1}{p^2})$ and the exact identity (certified in `scripts/phase26_mesoscopic_carries.py` Section 4.1)
     ```math
     3 - \cos(t_1 + t_2) - \cos t_1 - \cos t_2
       = 2\left(\sin^2\!\frac{t_1}{2} + \sin^2\!\frac{t_2}{2} + \sin^2\!\frac{t_1 + t_2}{2}\right)
       \ge \frac{2}{\pi^2}(t_1^2 + t_2^2) \qquad \forall (t_1, t_2) \in [-\pi, \pi]^2,
     ```
     with $E_0 := \sum_{p \in \mathcal{P}_0} \frac{1}{p} = L - O(\log\log\log L) \ge \frac{1}{2} L$, the 2-D Gaussian integral yields
     ```math
     \Pr(S_1 = m_1,\, S_2 = m_2)
       \ll \int_{\mathbb{R}^2} \exp\!\left(-\frac{2 E_0}{\pi^2}(t_1^2 + t_2^2)\right) dt_1\, dt_2
       \ll \frac{1}{E_0} \ll \frac{1}{L}.
     ```
     Multiplying by $81^2 = O(1)$ gives $O(|I| / (M_{\mathcal{Q}} L))$ on $I_0$, and summing over $a \bmod M_{\mathcal{Q}}$ gives $O(|I|/L)$.
   - On each dyadic shell $I_j$ ($1 \le j \le J$), split according to $U(n; z_j) > x^{1/8}$ versus $V_j(n) := U(n; z_{j-1}) / U(n; z_j) > x^{1/8}$ (since $U(n; z_{j-1}) = U(n; z_j) V_j(n) > x^{1/4}$):
     - *Subcase $I_j^{(a)}$ ($x^{1/8} < U(n; z_j) \le x^{1/4}$):* Run the 3-D Fundamental Lemma sieve up to $z_j$ with level $D = x^{1/2}$ ($s = w_j / 2 \ge 20$), weighting each $(u_0, u_1, u_2)$ inside the 2-D Fourier integral by the Rankin factor $(u_0 u_1 u_2)^{\alpha_j} x^{-\alpha_j / 8}$ with $\alpha_j = 1/\log z_j$ (so $x^{-\alpha_j / 8} = e^{-w_j / 8}$). Inside the Euler product, for each phase $\phi \in \{t_1, t_2, -t_1 - t_2\}$, $p^{\alpha_j} \cos\phi - 1 \le (p^{\alpha_j} - 1) - (1 - \cos\phi)$ (using $p^{\alpha_j} \ge 1$), preserving the quadratic Gaussian width $E_j \ge \frac{1}{2} L$ while contributing at most $\exp(3 \sum_{p \le z_j} \frac{p^{\alpha_j} - 1}{p}) = O(1)$. Multiplying by the $(2 w_j + 1)^2$ possible values of the $> z_j$ prime counts gives $\ll \frac{|I|}{L} w_j^2 e^{-w_j / 8}$.
     - *Subcase $I_j^{(b)}$ ($U(n; z_j) \le x^{1/8}$ and $V_j(n) > x^{1/8}$):* Since every prime in $V_j(n)$ lies in $(z_j, z_{j-1}]$ with $z_{j-1} = x^{2/w_j}$, $V_j(n) > x^{1/8}$ forces $\omega(V_j(n)) \ge \lceil w_j / 16 \rceil$; choosing a subset of $r_j := \lceil w_j / 48 \rceil$ distinct primes $q_1 < \cdots < q_{r_j}$ in $(z_j, z_{j-1}]$ dividing $n_0 n_1 n_2$ gives a divisor $W = q_1 \cdots q_{r_j} \le z_{j-1}^{r_j} \le x^{1/12}$ (for $w_j \ge 48$, and $r_j = 2$ for $w_j = 80$) with $U(n; z_j) W \le x^{5/24} < x^{1/4}$. Running the 3-D Fundamental Lemma sieve up to $z_j$ on the progression $u_i \mid n_i$ and $W_i \mid n_i$ ($W = W_0 W_1 W_2$, $3^{r_j}$ splits) and summing $\sum_{W} \frac{3^{\omega(W)}}{W} \le \frac{1}{r_j!} \bigl(3 \sum_{z_j < p \le z_{j-1}} \frac{1}{p}\bigr)^{r_j} = \frac{(3 \ln 2 + o(1))^{r_j}}{r_j!} \le \frac{3^{r_j}}{r_j!}$ gives $\ll \frac{|I|}{L} w_j^2 \frac{3^{r_j}}{r_j!}$.
   - Summing $\sum_{j=1}^J w_j^2 \bigl(e^{-w_j / 8} + 3^{r_j}/r_j!\bigr) < \infty$ (exponentially convergent in $w_j = 40 \cdot 2^j$) proves the total count on $I$ is $O(|I|/L)$ uniformly for all $1 \le d < d' \le \sqrt{L}$. $\square$

### 2.2 Unconditional collision lower bounds for $E^*(4)$

Although a positive lower density of collisions remains blocked by the parity problem (Remark below), we prove two new unconditional collision lower bounds for $E^*(4)$: a completely elementary bound with **zero external inputs** and a sharper polynomial-in-$1/\log N$ bound.

**Theorem C3.2 (Zero-external-input collision lower bound for $E^*(4)$; Paper proof + Finite certificate, zero external inputs).**
There exists an explicit constant $C > 0$ such that for all sufficiently large $N$,
```math
\#\bigl\{n \le N : \exists d \in \bigl[1,\, 6\sqrt{\log\log N}\bigr],\; q(n + d) = q(n)\bigr\}
  \ge N \exp\!\bigl(-C (\log\log N)(\log\log\log N)\bigr).
```

*Proof.* Put $L = \log\log N$ and $k := \lceil \frac{26}{5} \sqrt{L} \rceil$ (so $k > 3\sqrt{3}\sqrt{L}$ since $(26/5)^2 = 27.04 > 27 = (3\sqrt{3})^2$). Let $M_k := \operatorname{lcm}(1, \ldots, k) \cdot \prod_{p \le k} p$. Pick pairwise disjoint sets $S_1, \ldots, S_k$ of primes $> k^3$ with $|S_i| = 2i - \omega(i)$ (the first $\sum_{i=1}^k (2i - \omega(i)) \le k(k+1)$ primes strictly exceeding $k^3$; by Chebyshev's elementary prime bound $\pi(2k^3) - \pi(k^3) \gg k^3 / \log k \gg k^2$, every planted prime satisfies $k^3 < p \le 2 k^3$ for large $k$, so $\log p = 3 \log k + O(1) = O(\log k)$), and set $P_i := \prod_{p \in S_i} p$, $Q := \prod_{i=1}^k P_i^2$. By the Chinese Remainder Theorem, pick $m_0 \in [1, M_k Q)$ satisfying $m_0 \equiv 0 \pmod{M_k}$ and $m_0 \equiv P_i - i \pmod{P_i^2}$ for every $1 \le i \le k$. Note $\log(M_k Q) = O(k^2 \log k) = O(L \log L)$.

For every integer $t \ge 0$, set $m = m_0 + M_k Q t$. Since $i \mid M_k$ and every prime dividing $i$ divides $M_k$ to a strictly higher power than $v_p(i)$ (because $M_k$ carries an extra factor $\prod_{p \le k} p$), we have $\gcd(m + i, M_k) = i$ and $P_i \parallel (m + i)$, so $m + i = i P_i L_i(t)$ where $L_i(t) := \frac{m_0 + i}{i P_i} + \frac{M_k Q}{i P_i} t$ is coprime to $i P_i$. Therefore
```math
\omega(m + i) = \omega(i) + |S_i| + \omega(L_i(t)) = 2i + \omega(L_i(t)), \qquad
q(m + i) = 2(m + i) - \omega(m + i) = 2m - \omega(L_i(t))
```
holds **identically** for all $1 \le i \le k$ and all $t \ge 0$.

Let $T := \lfloor (N - k) / (M_k Q) \rfloor \asymp N \exp(-O(L \log L))$. By the elementary Turán–Kubilius inequality applied to each linear form $L_i(t)$ ($1 \le t \le T$; zero external inputs, variance $\le (1 + o(1)) L$), letting $A = \sqrt{3}$ (minimizing $\frac{2 A^3}{A^2 - 1}$ at $3\sqrt{3} < \frac{26}{5}$, certified algebraically by $4 A^6 - 27(A^2 - 1)^2 = (A^2 - 3)^2 (4 A^2 - 3) \ge 0$ in `scripts/phase26_mesoscopic_carries.py` Section 4.2), for each $i$ we have
```math
\#\bigl\{t \le T : |\omega(L_i(t)) - L| > A\sqrt{L}\bigr\} \le \left(\frac{1}{A^2} + o(1)\right) T = \left(\frac{1}{3} + o(1)\right) T.
```
Averaging over $1 \le i \le k$, the mean number of typical indices $Y(t) := \#\{1 \le i \le k : |\omega(L_i(t)) - L| \le \sqrt{3 L}\} \le k$ satisfies $\frac{1}{T} \sum_{t=1}^T Y(t) \ge (\frac{2}{3} - o(1)) k$. Since $\frac{2}{3} k - (2\sqrt{3 L} + 1) \ge (\frac{52}{15} - 2\sqrt{3})\sqrt{L} - 1 \approx 0.002565\sqrt{L} - 1 > 0$ once $L = \log\log N \gtrsim 1.52 \times 10^5$ (note: replacing $\frac{26}{5}$ by $6$ in $k = \lfloor 6\sqrt{L} \rfloor$ keeps $d \le k - 1 < 6\sqrt{L}$ while widening the margin to $(4 - 2\sqrt{3})\sqrt{L} \approx 0.536\sqrt{L}$, lowering the reverse-Markov threshold to $L = O(1)$), reverse Markov guarantees that at least a positive constant proportion $c_0 T$ of integers $t \le T$ satisfy:
```math
\#\bigl\{1 \le i \le k : |\omega(L_i(t)) - L| \le \sqrt{3 L}\bigr\} > 2\sqrt{3 L} + 1.
```
By the **pigeonhole principle**, for every such $t$, two distinct indices $1 \le i < j \le k$ satisfy $\omega(L_i(t)) = \omega(L_j(t))$, whence $q(m + i) = q(m + j)$ with shift $d = j - i \in [1, k - 1] \subseteq [1, 6\sqrt{L}]$. Distinct $t$ yield disjoint blocks $\{m + 1, \ldots, m + k\}$, giving $\gg T \ge N \exp(-C L \log L)$ distinct collision integers $n \le N$. $\square$

**Theorem C3.3 (Polynomial-in-$1/\log N$ collision lower bound for $E^*(4)$; Paper proof + Finite certificate; External inputs: general linear-forms Maynard 2015, 2016 / Polymath8b 2014; general linear-forms GGPY 2009).**
1. *(Admissible $k$-tuple CRT planting.)* For any fixed $k \ge 2$, set $B := \prod_{p \le k} p$, choose pairwise disjoint sets $S_1, \ldots, S_k$ of primes $> \max(k, B)$ with $|S_i| = 2 i B$, put $P_i := \prod_{p \in S_i} p$, $Q := \prod_{i=1}^k P_i^2$, and pick $m_0 \bmod (B Q)$ with $m_0 \equiv 1 \pmod B$ and $m_0 \equiv P_i - i B \pmod{P_i^2}$ ($1 \le i \le k$). Then for $m = m_0 + B Q t$, the $k$ affine linear forms $L_i(t) := a_i t + b_i$ with $a_i := \frac{B Q}{P_i} > 0$ and $b_i := \frac{m_0 + iB}{P_i}$ ($1 \le i \le k$) satisfy $\gcd(a_i, b_i) = 1$, pairwise linear independence $a_i b_j - a_j b_i = \frac{B^2 Q (j - i)}{P_i P_j} \ne 0$ ($i \ne j$), and **admissibility** (zero forbidden residues mod every $p \le k$, zero forbidden residues at every planted $p \mid Q$ since $p \mid a_i \implies b_i \not\equiv 0 \pmod p$, and $\le k < p$ forbidden residues mod every other $p > k$), and obey identically
   ```math
   q(m + i B) = 2m - \omega(L_i(t)) \qquad (1 \le i \le k,\ t \ge 0).
   ```
   *(Admissibility, $\gcd(a_i, b_i) = 1$, and pairwise linear independence verified algebraically in `scripts/phase26_mesoscopic_carries.py` Section 4.3 for $k = 2, 3$ across all primes $p \le 100$.)*
2. *(Polynomial-in-$1/\log N$ collision density.)* Because the slopes $a_i = BQ/P_i$ differ, we invoke the **general admissible linear-forms** formulation of the Maynard–Tao sieve (Maynard, *Ann. Math.* 181 (2015), general linear-forms extension, & *Compos. Math.* 152 (2016), Thm 3.1, combined with Polymath8b, *Res. Math. Sci.* 1:12 (2014), establishing $M_{50} > 4$ at Bombieri–Vinogradov level $\theta = 1/2 - \varepsilon$; *External input*; using Maynard 2015 directly without Polymath8b's variational bound replaces $50$ by $105$ with the same qualitative form $N / (\log N)^{O(1)}$). Applied to the fixed admissible $50$-tuple $\{L_1, \ldots, L_{50}\}$, this produces $\gg T / (\log T)^{50}$ integers $t \le T \asymp_{50} N$ for which at least two of $L_1(t), \ldots, L_{50}(t)$ are simultaneously prime ($\omega(L_i) = \omega(L_j) = 1$), yielding unconditionally
   ```math
   \#\bigl\{n \le N : \exists d \in [1, 50 B_{50}],\; q(n + d) = q(n)\bigr\} \gg \frac{N}{(\log N)^{50}}.
   ```
   Moreover, applying the **general admissible linear-forms** statement of Goldston–Graham–Pintz–Yıldırım (*Proc. LMS* 98(3) (2009), general linear forms at $k = 3$; *External input*) yields infinitely many bounded-shift collisions ($d \in \{6, 12\}$) from simultaneous $E_2$-values $\omega(L_i) = \omega(L_j) = 2$. $\square$

*Remark (Parity obstruction to positive collision density and `LLB(c)`; Structural / heuristic diagnosis).* Because Theorem C3.1 removes `PUB(C)` unconditionally, the sole remaining input for unconditional simple nonnormality of $E^*(4)$ via `GF-41` Theorem 4.3 is `LLB(c)`: a uniform local lower bound $\#\{n \in I : \omega(n+d) - \omega(n) = 2d\} \ge c |I| / \sqrt{L}$ for $1 \le d \le \sqrt{L}$. By exact Fourier inversion on $\mathbb{Z}$, $\Pr(\omega(n+d) - \omega(n) = 2d) = \frac{1}{2\pi} \int_{-\pi}^{\pi} e^{-2 i d \vartheta} \mathbb{E}[e^{i\vartheta(\omega(n+d) - \omega(n))}]\, d\vartheta$, whose integrand at $\vartheta = \pi$ is the two-point Chowla correlation $\mathbb{E}[(-1)^{\omega(n) + \omega(n+d)}]$. As `GF-41` Theorem 4.2(a) shows, every collision requires equal $\omega$-parity; heuristically, any purely parity-blind sieve bound cannot rule out $(-1)^{\omega(n) + \omega(n+d)} \equiv -1$, which would annihilate all collisions. *(Note: recent work of Tao–Teräväinen on almost-all-scales Chowla / local laws for additive functions may plausibly yield `LLB(c)` along a subsequence of scales $x_j \to \infty$—giving $\liminf f_1(E^*(4); 2) < \frac{1}{2}$—but that external literature is NOT verified or used as an input here.)*

---

## 3. Track C4: $E_+(8)$ and $E_+(4)$ — Exponential Carry Growth, Explicit $k_0 = 25$, Exact Base-$2^L$ Floor, and Barriers

### 3.1 Exact Signed Carry Conservation and Exponential Carry-Growth Lemma

To crush `GF-42` Theorem B1.4's unspecified $k_0 > 3.05 \times 10^{10}$ down to a concrete small integer while keeping zero external inputs for the carry transfer, we replace `GF-42`'s Markov tail cutoff ($j_0 = 9$) with an exact signed-carry conservation law.

**Theorem C4.1 (Signed Carry Conservation & Exponential Carry-Growth Lemma; Paper proof + Finite certificate, zero external inputs).**
Let $x = \sum_{n \ge 1} C_k(n) 2^{-n}$ with integers $C_k(n) \in \mathbb{Z}$ and $Y_n := \sum_{j \ge 1} C_k(n + j) 2^{-j}$ converging absolutely. Define the nearest-integer signed carry $q_n := \lfloor Y_n + \frac{1}{2} \rfloor \in \mathbb{Z}$, remainder $\varepsilon_n := Y_n - q_n \in [-\frac{1}{2}, \frac{1}{2})$, induced signed binary digit $a'_n := 2 \varepsilon_{n-1} - \varepsilon_n = C_k(n) + q_n - 2 q_{n-1} \in \{-1, 0, 1\}$, and total signed weight $A_N := \sum_{n=1}^N |a'_n|$. Then:
1. *(Signed carry conservation.)* For every $N \ge 1$,
   ```math
   \sum_{n = 0}^{N - 1} |q_n| \le \sum_{n = 1}^{N} |C_k(n)| + A_N + |q_N| - |q_0|.
   ```
2. *(Exponential carry growth on $t$-isolated odd arrivals.)* For any integer $t \ge 0$, set
   ```math
   \mathcal{M}_t(N) := \bigl\{1 \le n \le N - t : C_k(n) \text{ is odd and } C_k(n + 1) = \cdots = C_k(n + t) = 0\bigr\}.
   ```
   The intervals $\{[n, n + t] : n \in \mathcal{M}_t(N)\}$ are **pairwise disjoint**, and every $n \in \mathcal{M}_t(N)$ satisfies either $\sum_{j=n}^{n+t} |a'_j| \ge 1$ or $\sum_{j=n}^{n+t} |q_j| \ge 2^{t+1} - 1$. Consequently,
   ```math
   \frac{A_N}{N} \ge \left(1 - 2^{-(t+1)}\right) \frac{|\mathcal{M}_t(N)|}{N}
     - 2^{-(t+1)} \cdot \frac{1}{N} \sum_{n = 1}^{N} |C_k(n)| - \frac{2(|q_N| - |q_0|)}{2^{t+1} N}.
   ```
3. *(Binary transition and discrepancy-gap link.)* For every $N \ge 1$ (assuming $x$ is not dyadic rational),
   ```math
   \mathrm{tr}_N(x) := \#\{1 \le n < N : d_n(x; 2) \ne d_{n+1}(x; 2)\} \ge \frac{A_N - 2}{2}, \qquad
   1 - D_N(x; 2) \ge \min\!\left(\frac{1}{4},\; \frac{A_N - 6}{4 N}\right).
   ```

*Proof.*
(1) From $2 q_{n-1} = C_k(n) + q_n - a'_n$, the triangle inequality gives $2 |q_{n-1}| \le |C_k(n)| + |q_n| + |a'_n|$, i.e., $|q_{n-1}| \le |C_k(n)| + |a'_n| + (|q_n| - |q_{n-1}|)$. Summing over $1 \le n \le N$ telescopes $\sum (|q_n| - |q_{n-1}|) = |q_N| - |q_0|$.
(2) Disjointness is immediate: if $n < n' \le n + t$ with $n \in \mathcal{M}_t(N)$, then $C_k(n') = 0$ is even, so $n' \notin \mathcal{M}_t(N)$. Take $n \in \mathcal{M}_t(N)$ and suppose $a'_j = 0$ for all $j \in [n, n + t]$. At $j = n$, $q_n = 2 q_{n-1} - C_k(n)$ is **odd**, so $|q_n| \ge 1$. Inductively for $1 \le r \le t$, since $C_k(n + r) = a'_{n+r} = 0$, we have $q_{n+r} = 2 q_{n+r-1} = 2^r q_n$, hence $\sum_{j=n}^{n+t} |q_j| = (2^{t+1} - 1)|q_n| \ge 2^{t+1} - 1$. Therefore every $n \in \mathcal{M}_t(N)$ satisfies
```math
(2^{t+1} - 1) \le (2^{t+1} - 1)\sum_{j=n}^{n+t} |a'_j| + \sum_{j=n}^{n+t} |q_j|.
```
Summing over the disjoint intervals $n \in \mathcal{M}_t(N)$ gives $(2^{t+1} - 1) |\mathcal{M}_t(N)| \le (2^{t+1} - 1) A_N + \sum_{j=1}^N |q_j|$. Since $\sum_{j=1}^N |q_j| = \sum_{j=0}^{N-1} |q_j| + |q_N| - |q_0|$, substituting (1) gives $\sum_{j=1}^N |q_j| \le \sum_{n=1}^N |C_k(n)| + A_N + 2(|q_N| - |q_0|)$, whence $(2^{t+1} - 1) |\mathcal{M}_t(N)| \le 2^{t+1} A_N + \sum_{n=1}^N |C_k(n)| + 2(|q_N| - |q_0|)$. Dividing by $2^{t+1} N$ yields the exact stated inequality.
(3) Whenever $a'_n \ne 0$, $|2 \varepsilon_{n-1} - \varepsilon_n| = 1$ with $|\varepsilon_n| \le \frac{1}{2}$ forces $|\varepsilon_{n-1}| \ge \frac{1}{4}$. Since $2^{n-1} x \equiv \varepsilon_{n-1} \pmod 1$, we have $\{2^{n-1} x\} \in [\frac{1}{4}, \frac{3}{4}]$. If $\{2^{n-1} x\} \in [\frac{1}{4}, \frac{3}{4})$, then $(d_n, d_{n+1}) \in \{01, 10\}$ is a transition at $n$; if $\{2^{n-1} x\} = \frac{3}{4}$ (which cannot happen for irrational $x$, and even for non-dyadic $x$ forces $d_{n+1} = 1, d_{n+2} = 0$ because expansions do not end in $1^\infty$), it produces a transition at $n + 1$. Thus each $n \in [1, N - 2]$ with $a'_n \ne 0$ places a transition in $\{n, n + 1\}$, so each transition is hit at most twice, giving $2 \mathrm{tr}_N(x) \ge A_N - 2$. Since binary transitions alternate between $(0, 1)$ and $(1, 0)$, $\#\{1 \le n < N : (d_n, d_{n+1}) = (0, 1)\} \ge \frac{\mathrm{tr}_N(x) - 1}{2} \ge \frac{A_N - 4}{4}$, and `GF-42` Lemma B1.2(3) gives $1 - D_N(x; 2) \ge \min(\frac{1}{4}, \frac{A_N - 6}{4N})$. *(Verified identically with the exact $2(|q_N| - |q_0|)$ boundary term on certified $1200$-bit prefixes of $E_+(8), E_+(16), E_+(32)$ for $t = 0, 1, 2, 3$ in `scripts/phase26_mesoscopic_carries.py` Section 5.1.)* $\square$

### 3.2 Explicit $k_0 = 25$ for $D^+(E_+(2^k); 2) < 1$ and the sharp large-window barrier for $E_+(8)$

**Theorem C4.2 (Explicit $k_0 = 25$ for $D^+(E_+(2^k); 2) < 1$ and $E_+(2^k) \notin K_2$, conditional $E_+(8)$ threshold, and sharp large-window barrier; Paper proof + Finite certificate; External input: 2-D Selberg upper-bound sieve).**
1. *(Unconditional explicit $k_0 = 25$.)* For **every integer $k \ge 25$**,
   ```math
   0 < D^-(E_+(2^k); 2) \le D^+(E_+(2^k); 2) < 1, \qquad E_+(2^k) \notin K_2.
   ```
   Specifically, at $k = 25$ we certify $1 - D^+(E_+(2^{25}); 2) \ge 4.36 \times 10^{-5} > 0$, slashing `GF-42` Theorem B1.4's $k_0 > 3.05 \times 10^{10}$ by **more than $1.2 \times 10^9\times$**.
2. *(Conditional $E_+(8)$ criterion.)* If the 2-point lattice collision density of $V_+$ satisfies $\sum_{d \ne 0} \#\{m \le M : m, m+d \not\equiv 2 (4),\, V_+(m+d) - V_+(m) = 3d - j\} \le C \cdot \frac{9}{16} \cdot \frac{M}{3} + o(M)$ for $j \in \{0, 1, 2\}$ with **$C < 1.02341$**, then Theorem C4.1 ($t = 2$) implies $D^+(E_+(8); 2) < 1$ and $E_+(8) \notin K_2$.
3. *(Sharp Large-Window Signed-Cancellation Barrier for $E_+(8)$; Objective 4.)* The periodic signed arrival sequence $C(12m) = -1$, $C(12m + 1) = +1 + 1 = +2$ (two $+1$ arrivals), and $C(n) = 0$ otherwise has positive/negative arrival rates $\lambda_+ = \frac{1}{6}$, $\lambda_- = \frac{1}{12}$ (matching $E_+(8)$'s exact arrival rates $\frac{1}{2}/3 = \frac{1}{6}$ and $\frac{1}{4}/3 = \frac{1}{12}$), unit odd parts $U = \pm 1$, positive net arrival count $\lambda_+ - \lambda_- = \frac{1}{12}$ per column, and **zero variance** on every large window of length $12L$, yet satisfies $\sum_{n \ge 1} C(n) 2^{-n} = 0 \in K_2$ ($D^+ = 1$). Consequently, no large-$G$ window count or second-moment statistic (of `GF-42` Thm B1.3 type) can prove $D^+(E_+(8); 2) < 1$; short-range ($j \le 2$) lattice pair-correlation control below the sieve parity barrier $C = 2$ is strictly necessary.

*Proof.*
(1) Fix $t = 2$, $u = 12$, $\alpha = \frac{9}{20} = 0.45$, and $B = 4$. We take limits in the strict order: fix an arbitrary tolerance $\varepsilon \in (0, 10^{-4})$, choose fixed integers $K = K(\varepsilon) \ge 1$ with $2^{-K} < \varepsilon$, a fixed prime cutoff $p_1 = p_1(\varepsilon) \ge \max(5, \lceil 400/\varepsilon \rceil)$ with $\sum_{p > p_1} p^{-2} < \varepsilon$, a fixed smooth-part threshold $S_0 = S_0(p_1, \varepsilon) \ge 1$ such that $\Pr(s_{\le p_1}(m) > S_0) < \varepsilon$ (possible because $\sum_{s\text{ } p_1\text{-smooth}} \frac{1}{s} \prod_{p \le p_1}(1 - \frac{1}{p}) = 1$), and a fixed $\delta = \delta(\varepsilon) \in (0, 10^{-4})$; then let $N \to \infty$ (with $M = \lfloor N/k \rfloor \to \infty$), and only at the end let $\varepsilon \to 0$ (so $\delta \to 0$, $p_1 \to \infty$, $K \to \infty$).

- *Dyadic-block good-source set $\mathcal{G}_+$ covering $(M/2^K, M]$:* Partition $(M / 2^K, M]$ into $K$ disjoint dyadic blocks $I_\ell := (M_\ell / 2, M_\ell]$ with $M_\ell := M / 2^\ell$ ($0 \le \ell < K$), and set block-specific prime cutoffs $z_\ell := M_\ell^{1/u} = M_\ell^{1/12}$. Define $\mathcal{G}_+^{(\ell)} \subseteq I_\ell$ as the set of integers $m \in I_\ell$ satisfying: (i) $m \not\equiv 2 \pmod 4$; (ii) $p^2 \nmid m$ for every prime $p > p_1$; (iii) $s_{\le p_1}(m) := \prod_{p \le p_1} p^{v_p(m)} \le S_0$; (iv) $u_\ell(m) := \prod_{p_1 < p \le z_\ell,\, p \mid m} p \le M_\ell^\alpha$; and (v) $W_\ell(m) := \omega_{> z_\ell}(m) \le B = 4$. Set $\mathcal{G}_+ := \bigsqcup_{\ell = 0}^{K - 1} \mathcal{G}_+^{(\ell)}$. For every $m \in \mathcal{G}_+^{(\ell)}$, we have $m > M_\ell / 2$ and $s_{\le p_1}(m) u_\ell(m) \le S_0 M_\ell^\alpha$, so $m / (s_{\le p_1}(m) u_\ell(m)) > \frac{1}{2 S_0} M_\ell^{1 - \alpha} > 1$ for all large $M$ (since $M_\ell \ge M/2^K \to \infty$ while $S_0$ is fixed); hence **$1 \le W_\ell(m) \le 4$ holds automatically on every dyadic block $\ell$**!

- *Scale-invariant elementary upper bounds on bad sources across all $m \le M$:* The bottom tail $m \le M/2^K$ with $m \not\equiv 2 \pmod 4$ has count $\le \frac{3}{4} \cdot 2^{-K} M + 1 < \frac{3}{4} \varepsilon M + 1$. Inside each block $I_\ell = (M_\ell/2, M_\ell]$ ($0 \le \ell < K$), conditions (ii) and (iii) exclude at most $\frac{3}{4}(2\varepsilon + o(1)) |I_\ell|$ integers $m \in I_\ell$ with $m \not\equiv 2 \pmod 4$. For (iv), split $\{m \in I_\ell : m \not\equiv 2 (4),\, u_\ell(m) > M_\ell^\alpha\}$ at $M_\ell^{11/12}$:
  - When $M_\ell^\alpha < u_\ell(m) \le M_\ell^{11/12}$, every divisor $d \mid u_\ell(m)$ satisfies $d \le M_\ell^{11/12}$; writing $u_\ell(m)^\theta = \sum_{d \mid u_\ell(m),\, d \le M_\ell^{11/12}} g(d)$ with $g(d) = \mu^2(d) \prod_{p \mid d}(p^\theta - 1) \ge 0$ ($\theta = c / \log z_\ell$, $c = \frac{21}{10}$), every $d$ is odd ($\gcd(d, 4) = 1$) and $g(d) \le d^\theta \le e^{12 c} = O(1)$, so summing $\#\{m \in I_\ell : m \not\equiv 2(4),\, d \mid m\} = \frac{3}{4}\frac{|I_\ell|}{d} + O(1)$ gives $\le \frac{3}{4} |I_\ell| \cdot \exp(-\alpha u c + \mathrm{Ein}(c) + o(1)) + O(M_\ell^{11/12})$ (using Stieltjes integration against Mertens' $\sum_{p \le t} \frac{\log p}{p} = \log t + O(1)$ to bound $\sum_{p \le z_\ell} \frac{p^\theta - 1}{p} = \mathrm{Ein}(c) + O_c(\frac{1}{\log z_\ell})$).
  - When $u_\ell(m) > M_\ell^{11/12}$, bounding by all $m \le M_\ell$ (where $\lfloor M_\ell/d \rfloor \le M_\ell/d$ has zero $+1$ error) with $c' = 3$ gives $\le M_\ell \exp(-11 c' + \mathrm{Ein}(c') + o(1)) = \frac{3}{4} |I_\ell| \cdot \bigl(\frac{8}{3} \exp(-33 + \mathrm{Ein}(3)) + o(1)\bigr)$, where Section 5.2 certifies the extra tail $\frac{8}{3} \exp(-33 + \mathrm{Ein}(3)) < 5 \times 10^{-11}$ and the combined sum $p_{\mathrm{sm}} \le 0.000659$.
  For (v), every $m \in I_\ell$ with $W_\ell(m) \ge 5$ is divisible by some odd product $Q = q_1 \cdots q_5 \le M_\ell$ of five primes $> z_\ell$. Splitting at $M_\ell^{1-\delta}$: products $Q \le M_\ell^{1-\delta}$ yield $\frac{3}{4} |I_\ell| \sum_{Q \le M_\ell^{1-\delta}} 1/Q + O(M_\ell^{1-\delta}) \le \frac{3}{4} |I_\ell| (p_W + o(1))$, while products $Q \in (M_\ell^{1-\delta}, M_\ell]$ (bounded on $[1, M_\ell]$ via $\lfloor M_\ell/Q \rfloor \le M_\ell/Q$) contribute at most $M_\ell \sum_{M_\ell^{1-\delta} < Q \le M_\ell} 1/Q = O(\delta) |I_\ell|$ by Mertens' theorem on the thin shell $1 - \delta < \sum_{i=1}^5 t_i \le 1$. Here
  ```math
  p_W := \frac{1}{5!} \int_{\substack{t_1, \ldots, t_5 \ge 1/12 \\ t_1 + \cdots + t_5 \le 1}} \frac{dt_1 \cdots dt_5}{t_1 \cdots t_5}
    \le 0.047083,
  ```
  certified in pure integer arithmetic via an exact upper Riemann convolution on $N_g = 240$ bins using $\int_{i/N}^{(i+1)/N} \frac{dt}{t} = \ln\frac{i+1}{i} \le \frac{2}{2i+1} + \frac{2}{3(2i+1)((2i+1)^2 - 1)}$. Summing over all $K$ blocks ($\sum_{\ell=0}^{K-1} |I_\ell| \le M$) and adding the bottom tail $m \le M/2^K$, the total count of bad sources $\mathrm{Bad}_+ := \{m \in [1, M] : m \not\equiv 2 \pmod 4\} \setminus \mathcal{G}_+$ satisfies
  ```math
  |\mathrm{Bad}_+| \le \frac{3}{4}\bigl(p_{\mathrm{sm}} + p_W + 3\varepsilon + O(\delta) + o(1)\bigr) M.
  ```

- *Disjointness trick (eliminating the factor $(t + 1)$ on bad sources):* Put $n(m) := km - V_+(m)$ and $\mathcal{G}_+^{\mathrm{iso}} := \{m \in \mathcal{G}_+ : \text{no } m' \in \mathcal{G}_+ \setminus \{m\} \text{ lands in } [n(m), n(m) + 2]\}$. The intervals $\{[n(m), n(m) + 2] : m \in \mathcal{G}_+^{\mathrm{iso}}\}$ are **pairwise disjoint**: if $n(m_1) \le n(m_2) \le n(m_1) + 2$, then $m_2$ kills $m_1 \notin \mathcal{G}_+^{\mathrm{iso}}$. Consequently, every bad source $m' \in \mathrm{Bad}_+$ (plus the $O(\log M)$ sources with $m' > M$ landing in $[1, N]$) hits **at most one** interval of $\mathcal{G}_+^{\mathrm{iso}}$. Since $|\mathcal{G}_+| = \frac{3}{4} M - |\mathrm{Bad}_+| + O(1)$,
  ```math
  |\mathcal{M}_2(N)| \ge |\mathcal{G}_+| - |\mathrm{Bad}_+| - \mathrm{Col}(\mathcal{G}_+, 2) - O(\log M)
    \ge \frac{3}{4}\bigl(1 - 2(p_{\mathrm{sm}} + p_W) - 6\varepsilon - O(\delta) - o(1)\bigr) M - \mathrm{Col}(\mathcal{G}_+, 2).
  ```

- *Cross-block and within-block collisions ($\mathrm{Col}(\mathcal{G}_+, 2)$):*
  - *Cross-block collisions:* If $m \in \mathcal{G}_+^{(\ell)}$ and $m' \in \mathcal{G}_+^{(\ell')}$ with $\ell \ne \ell'$ satisfy $|n(m') - n(m)| \le 2$, then $m$ and $m'$ straddle one of the $K - 1$ block boundaries $M_{\ell_0} = M / 2^{\ell_0}$. Since $V_+(n) \le \log_2 M$ for all $n \le M$, we have $k |m' - m| \le \log_2 M + 2$, forcing $m$ within $(\log_2 M + 2)/k$ of some $M_{\ell_0}$. Thus at most $2(K - 1)(\frac{\log_2 M + 2}{k} + 1) = O_K(\log M) = o(M)$ sources participate in cross-block collisions.
  - *Within-block tail $|d| > D_0 := \lceil (10 L_\ell + 2)/k \rceil$ ($L_\ell = \log\log M_\ell$):* If $m, m + d \in \mathcal{G}_+^{(\ell)}$ satisfy $V_+(m+d) - V_+(m) = kd - j$ ($j \in \{0, 1, 2\}$) with $d > D_0$, then $\tau(m+d) \ge 2^{V_+(m+d)} > 2^{10 L_\ell}$, so $\tau(n)^2 \le \tau_4(n)$ bounds all $|d| > D_0$ pairs on $I_\ell$ by $O(M_\ell (\log M_\ell)^{3 - 10\ln 2}) = o(M_\ell)$.
  - *Within-block main range $1 \le |d| \le D_0$ — fixed-$S_0$ conditioning, 10-shell 2-D Selberg sieve, Abel summation, and Cramér local limit:* Fix $\ell \in \{0, \ldots, K - 1\}$, $j \in \{0, 1, 2\}$ ($t + 1 = 3$ choices), $\Delta_W = W_\ell(m+d) - W_\ell(m) \in \{-3, -2, -1, 0, 1, 2, 3\}$ ($2B - 1 = 7$ choices, since $1 \le W_\ell \le 4$), and a compatible pair of $p_1$-smooth integers $(s_1, s_2)$ with $s_1, s_2 \le S_0$ and $s_1, s_2 \not\equiv 2 \pmod 4$ (a **finite fixed set** of at most $S_0^2$ pairs!). The exact condition $s_{\le p_1}(m) = s_1, s_{\le p_1}(m+d) = s_2$ is a union of residue classes modulo the **fixed** modulus $Q_0 := P(s_1, s_2) = \prod_{p \le p_1} p^{\max(v_p(s_1), v_p(s_2)) + 1} = O_{p_1, \varepsilon}(1)$ with exact density $\rho_{p_1}(s_1, s_2; d)$ depending **only** on $d \bmod Q_0$, and fixes the exact bounded shift $\Delta := j + (V_{+, \le p_1}(s_2) - V_{+, \le p_1}(s_1)) + \Delta_W$ ($|\Delta| \le B_2 := 5 + 2\log_2 S_0 = O_{p_1, \varepsilon}(1)$). On $\mathcal{P}_d^{(\ell)} := \{p \in (p_1, z_\ell] : p \nmid d\}$, write $u_1 = \prod_{p \in \mathcal{P}_d^{(\ell)},\, p \mid m} p$ and $u_2 = \prod_{p \in \mathcal{P}_d^{(\ell)},\, p \mid (m+d)} p$; primes in $(p_1, z_\ell]$ dividing $d$ cancel from $V_+(m+d) - V_+(m)$, leaving $\omega(u_2) - \omega(u_1) = h := kd - \Delta$.
  - Along the 10-shell partition $0 = \theta_0 < \theta_1 < \cdots < \theta_{10} = 2\alpha = \frac{9}{10}$ ($u_1 u_2 \in (M_\ell^{\theta_i}, M_\ell^{\theta_{i+1}}]$), the **2-D Selberg upper-bound sieve** (Friedlander–Iwaniec, *Opera de Cribro*, AMS Colloq. Publ. 57, 2010, Theorem 7.1; Halberstam–Richert, Ch. 6–7; *External input*) applies at level $D_i = M_\ell^{1 - \theta_{i+1} - \delta}$ with sieve parameter $s_i = (1 - \theta_{i+1} - \delta) u$ and uniform main-term multiplier $f_i(\delta) + o(1)$ where $f_i(\delta) := 1/\sigma_2(s_i)$. Because $Q_0 = O_{p_1, \varepsilon}(1)$ and the number of pairs $(s_1, s_2)$ is $O_{p_1, \varepsilon}(1)$, the total remainder summed over $1 \le |d| \le D_0$, $(s_1, s_2)$, and $u_1 u_2 \le M_\ell^{\theta_{i+1}}$ is $O_{p_1, \varepsilon}(L_\ell \cdot M_\ell^{\theta_{i+1}} (\log M_\ell) \cdot M_\ell^{1 - \theta_{i+1} - \delta} (\log M_\ell)^5) = O_{p_1, \varepsilon}(M_\ell^{1 - \delta} (\log M_\ell)^7) = o(M_\ell)$.
  - Put $T_i(d, h) := \Pr(S_d = h,\, U_{\mathrm{prod}} > M_\ell^{\theta_i})$ for the independent trinomial model $S_d = \sum_{p \in \mathcal{P}_d^{(\ell)}} \xi_p$, $U_{\mathrm{prod}} = \prod_{\xi_p \ne 0} p$. For $1 \le i \le 9$ and $\eta_i = c_i / \log z_\ell$, contour-shifted Fourier inversion ($t \mapsto t - i\lambda$) of $e^{-u \theta_i c_i} \mathbb{E}[\mathbf{1}_{S_d = h} U_{\mathrm{prod}}^{\eta_i}]$ has Euler factor $1 - \frac{2}{p} + \frac{2 p^{\eta_i} \cosh(\lambda + it)}{p}$: since $p^{\eta_i} \ge 1$ and $\sum_{p \in \mathcal{P}_d^{(\ell)}} \frac{p^{\eta_i} - 1}{p} = \mathrm{Ein}(c_i) + O(\frac{1}{\log z_\ell})$, the real part satisfies $\le \frac{2(p^{\eta_i} - 1)}{p} + \frac{2 p^{\eta_i}(\cosh\lambda - 1)}{p} - \frac{2(1 - \cos t)}{p}$ and the quadratic error sums to $O(1/p_1)$. At $|h| \le E_d^{2/3}$, choosing $\lambda = h/(2 E_d)$ yields $T_i(d, h) \le (1 + O(p_1^{-1}) + o(1)) R_i \cdot \frac{1}{\sqrt{4\pi E_d}} e^{-h^2/(4 E_d)}$ with $R_i := \min(1, \exp(-u \theta_i c_i + 2\,\mathrm{Ein}(c_i)))$ (and $R_0 = 1$); at $|h| > E_d^{2/3}$, $\lambda = \mathrm{sign}(h) \cdot \frac{1}{2} E_d^{-1/3}$ contributes $O(E_d^{-1/2} e^{-\frac{1}{5} E_d^{1/3}}) = o(1)$ after summing over $d$.
  - **Abel summation by parts with monotone Rankin weights:** Writing the 10-shell main term as $\sum_{i=0}^{9} f_i(\delta)(T_i - T_{i+1}) \le f_0(\delta) T_0 + \sum_{i=1}^{9} (f_i(\delta) - f_{i-1}(\delta)) T_i$ and replacing $T_i$ by $R_i$ times the Gaussian bound gives effective multiplier $\mathrm{eff}_{\sigma_2}(\delta) = f_0(\delta) + \sum_{i=1}^{9} (f_i(\delta) - f_{i-1}(\delta)) R_i = \sum_{i=0}^{8} f_i(\delta) (R_i - R_{i+1}) + f_9(\delta) R_9$. Because Section 5.2 explicitly certifies that the Rankin weights are **monotone non-increasing** ($1 = R_0 \ge R_1 \ge \cdots \ge R_9 > 0$, so every $R_i - R_{i+1} \ge 0$), replacing each exact $f_i(0) = 1/\sigma_2((1 - \theta_{i+1}) u)$ by its certified upper bound $\tilde{f}_i \ge f_i(0)$ is strictly monotone and valid!
  - **Periodic Gaussian Riemann sum over $d$:** For each fixed $(s_1, s_2, j, \Delta_W)$ and each residue class $d \equiv r \pmod{Q_0}$, the shift $|\Delta| \le B_2$ and step $k Q_0$ are **fixed** while $E_{\min} \sim E_{\max} \sim L_\ell \to \infty$ uniformly for $1 \le |d| \le D_0$, so comparing the monotone Riemann sum with $\int_{-\infty}^\infty \frac{e^{-u^2/(4 E_{\max})}}{\sqrt{4\pi E_{\min}}}\, du = \sqrt{E_{\max}/E_{\min}} \to 1$ gives $\frac{1}{k Q_0} + o(1)$. Multiplying by $\rho_{p_1}(s_1, s_2; r)$ and summing over $r \bmod Q_0$ and all $s_1, s_2 \le S_0$ ($s_i \not\equiv 2 \pmod 4$) gives at most the average density of $m, m+d \not\equiv 2 \pmod 4$ across $d \bmod 4$, namely $\frac{1}{4}\cdot\frac{3}{4} + \frac{3}{4}\cdot\frac{1}{2} = \frac{9}{16}$. Summing over $j \in \{0, 1, 2\}$, $\Delta_W \in \{-3, \ldots, 3\}$, and $\ell = 0, \ldots, K - 1$ ($\sum_\ell |I_\ell| \le M$) yields
    ```math
    \limsup_{M \to \infty} \frac{\mathrm{Col}(\mathcal{G}_+, 2)}{M}
      \le \frac{3 \cdot 7 \cdot \frac{9}{16} \cdot \mathrm{eff}_{\sigma_2}(\delta) \cdot \bigl(1 + O(p_1^{-1})\bigr)}{k}.
    ```
  - Using Euler–Maclaurin to certify $\gamma$, the exact closed form $\sigma_2(2v) = e^{-2\gamma}(2v^2 - v^2 \ln v - 2v + \frac{1}{2})$ on $v \in [1, 2]$, and pure-integer monotone stepping of $(v^{-2} \sigma_2(2v))' = -2 v^{-3} \sigma_2(2v - 2)$ on $v \in [2, 5]$ (step $1/256$), `scripts/phase26_mesoscopic_carries.py` Section 5.2 certifies $\mathrm{eff}_{\sigma_2}(0) \le 1.05623$ and $C_{U, +} \in [1.220305, 1.220322]$, yielding
    ```math
    k_{\mathrm{req}} \le \frac{\frac{7}{8} \cdot 3 \cdot 7 \cdot \frac{9}{16} \cdot 1.05623}{\frac{7}{8} \cdot \frac{3}{4} (1 - 2(0.000659 + 0.047083)) - \frac{1}{8} \cdot 1.220322} \le 24.75247 < 25.
    ```
    By continuity of $\sigma_2$ as $\delta \to 0$, letting $M \to \infty$ first and then $\varepsilon \to 0$ (so $\delta \to 0, p_1 \to \infty, K \to \infty$), Theorem C4.1(2)–(3) yields $1 - D^+(E_+(2^k); 2) > 0$ for every $k \ge 25$; at $k = 25$, the certified pre-limit gap is $\ge 4.3669 \times 10^{-5} > 4.36 \times 10^{-5}$, so taking $\varepsilon$ sufficiently small gives $1 - D^+(E_+(2^{25}); 2) \ge 4.36 \times 10^{-5} > 0$, and `GF-40` / `GF-44` supply $D^- > 0$.
(2) Replacing $(2B - 1) \mathrm{eff}_{\sigma_2}$ by $C$ and $p_{\mathrm{sm}} = p_W = 0$ at $k = 3, t = 2$ gives $\frac{7}{8}(\frac{3}{4} - \frac{9}{16} C) > \frac{1}{8} C_{U, +}$, i.e., $C < (84 - 16 C_{U, +})/63$, certified $\ge 1.02341$.
(3) Direct check: $(-1) \cdot 2^{-12m} + 2 \cdot 2^{-(12m+1)} = 0$ for every $m \ge 1$. $\square$

### 3.3 Exact carry-coupled base-$2^L$ simple-normality floor and base-256 simple nonnormality of $E_+(8)$

`GF-42` Theorem B3.2 established base-$2^L$ simple nonnormality using the free-boundary 4-state average $A_L = \frac{1}{3} - \frac{7 - (-1/2)^{L-1}}{18 L}$, which required $L = 13$ (base $8192$) for $E_+(8)$ and $k \ge 8$ for base-$4$ simple nonnormality of $E_+(2^k)$. By working directly with the exact 2-state carry bit $c_n \in \{0, 1\}$, we eliminate the boundary potential loss of $\frac{1 - (-1/2)^{L-1}}{6 L}$ completely and prove the **sharp** base-$2^L$ floor for every $L \ge 1$.

**Theorem C4.3 (Exact carry-coupled base-$2^L$ floor & base-256 simple nonnormality of $E_+(8)$; Paper proof + Finite certificate, zero external inputs).**
1. *(Exact floor for all $L \ge 1$.)* For every integer $L \ge 1$, over all **non-dyadic** real numbers $x \in \mathbb{R} \setminus \mathbb{Z}[\frac{1}{2}]$ (note that every real number simply normal in base $2^L$ is automatically non-dyadic, since dyadic rationals have terminating expansions ending in $0^\infty$),
   ```math
   m_1^{(2^L)} := \inf\bigl\{\overline{w}_\pm(x) : x \in \mathbb{R} \setminus \mathbb{Z}[\tfrac{1}{2}] \text{ simply normal in base } 2^L\bigr\}
     = \frac{1}{3} - \frac{2 + (-1/2)^{L - 1}}{9 L}.
   ```
   In particular, $m_1^{(2)} = 0$, $m_1^{(4)} = m_1^{(8)} = \frac{1}{4}$, $m_1^{(16)} = \frac{9}{32} = 0.28125$, $m_1^{(32)} = \frac{23}{80} = 0.2875$, $m_1^{(64)} = \frac{19}{64} = 0.296875$, $m_1^{(128)} = \frac{135}{448} \approx 0.301339$, and $m_1^{(256)} = \frac{313}{1024} \approx 0.305664$. Moreover, for **every $L \ge 2$**, the infimum $m_1^{(2^L)}$ is **attained** by an explicit irrational base-$2^L$ simply normal number.
2. *(Immediate base-$2^L$ simple nonnormality breakthroughs — zero external inputs.)* If $\overline{w}_\pm(x) < m_1^{(2^L)}$, then $x$ is simply nonnormal in base $2^L$ (and in every base $2^{mL}$; note also that $E_+(2^k)$ is irrational for every $k \ge 1$ by P. Borwein, *Proc. Camb. Phil. Soc.* 109 (1991), 253–260). With our certified enclosures $W_+ \in [0.908065, 0.908215]$ and DP-free majorant $W_+^{\mathrm{maj}} \in [0.936413, 0.936420]$:
   - **$E_+(8)$ is unconditionally simply nonnormal in base $256 = 2^8$** ($W_+/3 \le 0.302739 < \frac{313}{1024} = 0.305664\ldots$), improving `GF-42`'s base $8192$ by **$32\times$**.
   - **Sharpness barrier for $E_+(8)$ (Objective 4):** $L = 8$ (base $256$) is **sharp** for symmetric NAF weight alone: for every $1 \le L \le 7$ (bases $2, 4, 8, 16, 32, 64, 128$), $m_1^{(2^L)} \le \frac{135}{448} < 0.301340 < 0.302688 \le W_+/3$, and the explicit attaining irrational base-$2^L$ simply normal number has lower signed-digit density than $W_+/3$.
   - **$E_+(2^k)$ is unconditionally simply nonnormal in base $4$ and base $8$ for every $k \ge 4$**—starting at **$E_+(16)$ in base $4$**—even from the DP-free majorant ($W_+^{\mathrm{maj}}/4 \le 0.234105 < \frac{1}{4} = m_1^{(4)} = m_1^{(8)}$, slashing `GF-42`'s $k \ge 8$ for base $4$ and $k \ge 5$ for base $8$).
   - **$L_-(4)$ and $L_+(8)$ (cubic moduli $M \in \{7, 9, 13, 19, 37\}$, $\rho \le 0.268177$), $E_+^*(8)$ ($\rho = \frac{1}{4}$), and $E_{\mathrm{alt}, +}^*(8)$ ($\rho = \frac{1}{4}$) are all unconditionally simply nonnormal in base $16$** ($\rho < \frac{9}{32} = 0.28125$).
   - **$E_{+, \mathrm{odd}}(16)$ is unconditionally simply nonnormal in base $64$** ($\rho \le 0.294084 < \frac{19}{64} = 0.296875$).
3. *($E_+(4)$ signed cancellation deficit.)* At $k = 2$, the NAF cancellation deficit is certified as $W_+/2 - \frac{1}{3} \in [0.120699, 0.120775]$ (requiring $> 0.120699$ signed cancellations per bit to drop below $\frac{1}{3}$).

*Proof of (1).*
*Lower bound (2-state Markov proof, $\psi \equiv 0$):* Let $x = \sum_{n \ge 1} b_n 2^{-n} \in (0, 1) \setminus \mathbb{Z}[\frac{1}{2}]$ ($b_n \in \{0, 1\}$, not ending in $0^\infty$ or $1^\infty$) and let $x = \sum_{n \ge 1} s_n 2^{-n}$ ($s_n \in \{-1, 0, 1\}$) be any signed binary representation of $x$. Put $Y_n = \sum_{j \ge 1} b_{n+j} 2^{-j} \in (0, 1)$ and $Z_n = \sum_{j \ge 1} s_{n+j} 2^{-j} \in [-1, 1]$. Notice $Z_n \ne \pm 1$ strictly: if $Z_n = \pm 1$, then $2^n x \in \mathbb{Z}$, contradicting $x \notin \mathbb{Z}[\frac{1}{2}]$. Hence $Z_n \in (-1, 1)$ strictly, so $c_n := Y_n - Z_n \in (-1, 2) \cap \mathbb{Z} = \{0, 1\}$ satisfies $s_n = b_n + c_n - 2 c_{n-1}$ at every bit $n \ge 1$. Across any $L$-bit block $w = \sum_{r=1}^L b_{n+r} 2^{L-r} \in \{0, \ldots, 2^L - 1\}$, the block weight is at least
```math
h_L(w) := \min_{c_0, c_L \in \{0, 1\}} d_L(w, c_0, c_L)
  = \min\bigl(w_\pm(w),\, w_\pm(w + 1),\, w_\pm(2^L - w),\, w_\pm(2^L - 1 - w)\bigr),
```
where $d_L(w, c_0, c_L)$ is the minimum weight of an $L$-step path $c_0 \xrightarrow{w} c_L$ in the 2-state automaton on $\{0, 1\}$ (transitions: on $b = 0$, $0 \to 0$ cost $0$, $0 \to 1$ cost $1$, $1 \to 1$ cost $1$; on $b = 1$, $1 \to 1$ cost $0$, $1 \to 0$ cost $1$, $0 \to 0$ cost $1$).
*(Shortcut for base $4$: at $L = 2$, $w = 1$ (`01`) and $w = 2$ (`10`) have $h_2(1) = h_2(2) = 1$, so every base-$4$ digit in $\{1, 2\}$ forces $\ge 1$ nonzero signed bit regardless of boundary carries, immediately giving $\sigma_1(x; 2M)/(2M) \ge \frac{1}{2}(f_{1,M}(x; 4) + f_{2,M}(x; 4)) \to \frac{1}{4}$.)*

For general $L \ge 1$, define for every binary prefix $u$ the two-entry minimum-cost vector $(v_0(u), v_1(u))$ ending in state $c = 0$ vs $c = 1$ (starting from $(v_0(\varepsilon), v_1(\varepsilon)) = (0, 0)$), and put $m(u) := \min(v_0(u), v_1(u)) = h_{|u|}(u)$ and $\Delta(u) := v_1(u) - v_0(u) \in \{-1, 0, +1\}$. Tracing one bit $b \in \{0, 1\}$ gives the exact transitions:
- From $\Delta = 0$: $b = 0 \implies (m, +1)$ (cost $+0$); $b = 1 \implies (m, -1)$ (cost $+0$).
- From $\Delta = +1$: $b = 0 \implies (m, +1)$ (cost $+0$); $b = 1 \implies (m + 1, 0)$ (cost $+1$).
- From $\Delta = -1$: $b = 0 \implies (m + 1, 0)$ (cost $+1$); $b = 1 \implies (m, -1)$ (cost $+0$).

For uniform random bits, let $p_n := \Pr(\Delta(w_1 \cdots w_n) = 0)$. Then $p_0 = 1$ and $p_{n+1} = \frac{1}{2}(1 - p_n)$, whose unique solution is $p_n = \frac{1}{3}(1 + 2(-1/2)^n)$. Step $n + 1$ incurs cost $+1$ with probability $\frac{1}{2}(1 - p_n) = p_{n+1} = \frac{1}{3}(1 - (-1/2)^n)$, so summing over $n = 0, \ldots, L - 1$ and dividing by $L$ gives
```math
\frac{1}{L \cdot 2^L} \sum_{w = 0}^{2^L - 1} h_L(w)
  = \frac{1}{L} \sum_{n = 0}^{L - 1} \frac{1 - (-1/2)^n}{3}
  = \frac{1}{3} - \frac{2 + (-1/2)^{L - 1}}{9 L}.
```
Summing over disjoint $L$-bit blocks proves $\liminf \sigma_1(x; LM)/(LM) \ge m_1^{(2^L)}$ for every base-$2^L$ simply normal $x$.

*Exact attainment (explicit Eulerian-cycle witness for every $L \ge 2$):* Because the 2-state automaton is invariant under bit complement $(b, c, s) \mapsto (1 - b, 1 - c, -s)$, pairing each $w < 2^{L-1}$ with $\bar{w} = 2^L - 1 - w$ and choosing complement-symmetric optimal arcs $(c_0^*(w) \xrightarrow{w} c_L^*(w))$ and $(1 - c_0^*(w) \xrightarrow{\bar{w}} 1 - c_L^*(w))$ makes the $2^L$-edge directed multigraph on $\{0, 1\}$ **balanced** ($\deg_{\mathrm{out}} = \deg_{\mathrm{in}}$ at both vertices). Moreover, for every $L \ge 2$, the word $w = 1 = 0^{L-1} 1$ achieves $h_L(1) = 1$ via the cross-edge $0 \to 1$ ($w + 1 = 2$ has NAF weight $1$), and its complement $\bar{w} = 2^L - 2$ achieves $1$ via $1 \to 0$, so the multigraph is **strongly connected** and admits a single Eulerian cycle $C$ of length $2^L$ base-$2^L$ digits starting and ending at $c = 0$, visiting every digit $w \in \{0, \ldots, 2^L - 1\}$ exactly once at total weight $L \cdot 2^L m_1^{(2^L)}$. Concatenating $C, 0, C^2, 0, C^4, 0, C^8, \ldots$ (where each inserted digit `0` is a $0 \to 0$ self-loop of weight $0$) yields an **irrational** number (non-eventually-periodic gap lengths $2^r$) that is **simply normal in base $2^L$** (inserted `0`'s have density $O(\frac{\log M}{M}) = 0$) and admits a valid signed-digit expansion with exact density $\overline{w}_\pm(x) = m_1^{(2^L)}$. *(Explicit Eulerian cycles constructed and certified for all $2 \le L \le 8$ in `scripts/phase26_mesoscopic_carries.py` Section 5.4.)* $\square$

*Remark (Multiscale block-cancellation scaling for $E_+(4)$; extends `GF-42` Thm B4.1, External input: 2-D Fundamental Lemma).* Following `GF-42` Theorem B4.1, for any block length $B \ge 1$ define $\mathcal{B}_r := \sum_{j=1}^B a_+(Br + j) 2^{2(B-j)}$ and the $B$-block NAF cancellation rate $\bar{c}_{2, B}^{\mathrm{block}}(M) := \frac{1}{2 B \lfloor M/B \rfloor} \sum_{r=0}^{\lfloor M/B \rfloor - 1} \bigl(\sum_{j=1}^B w_\pm(a_+(Br + j)) - w_\pm(\mathcal{B}_r)\bigr)$. Tracking the $B$-dependence in the proof of `GF-42` Theorem B4.1 (with $L = \log\log M$, $\eta = L^{-1/4}$, $p_1 = \lceil L^{1/2} \rceil$, $K_0 = \lceil L^{1/4} \rceil$, $T = \lceil L^{1/2} \rceil$) shows that bad blocks occur with fraction $\ll B (\log\log L)/L^{1/4}$ (contributing $\ll \sqrt{B (\log\log L)/L^{1/4}}$ via Cauchy–Schwarz) while colliding good blocks contribute $\ll \frac{1}{B} \binom{B}{2} \frac{2B + L^{1/4}}{\sqrt{L}} \log L \ll \frac{B^2 \log L}{\sqrt{L}} + \frac{B \log L}{L^{1/4}}$. Thus $\bar{c}_{2, B(M)}^{\mathrm{block}}(M) \to 0$ continues to hold for growing blocks up to $B(M) = o\bigl((\log\log M)^{1/4} / \log\log\log M\bigr)$, whereas reaching the lattice collision scale $B(M) \asymp \sqrt{\log\log M}$ hits the same 2-point correlation barrier as $E(4)$ and $E^*(4)$. (This remark uses `GF-42` Thm B4.1's 2-D Fundamental Lemma; Theorem C4.3 itself uses zero external inputs.)

---

## 4. Track C5: Generalized Lambert Classifications and Unconditional Base-2 Disjunctivity

### 4.1 Complete order-$m$ Dirichlet character Lambert trichotomy and alternating cubic $L_{-,+}(4)$

In `GF-44` (`notes/phase25/naf-geometric-transfer.md` Lemma C.1), the Elementary Twisted Squarefull Convolution Lemma established nonnormality of cubic-character series $L_-(4)$ for moduli $M \in \{7, 9, 13, 19, 37\}$ where $\chi(2) \ne 1$, while moduli with $\chi(2) = 1$ (such as $M = 31, 43, 109, 127$) failed because $L_2^{\mathrm{std}} \approx 1.1842$ pushed $\rho_- > \frac{1}{3}$. We now resolve ALL primitive characters of every order $m \ge 1$ and show that the **alternating** cubic series $L_{-,+}(4)$ succeeds precisely on the $\chi(2) = 1$ moduli!

**Theorem C5.1 (Complete Order-$m$ Dirichlet Character Lambert Trichotomy & Alternating Cubic Classification; Paper proof + Finite certificate; External inputs: Dirichlet's theorem + Wirsing / Selberg–Delange [`GF-13`] for $m$ even; Evertse 1984 Thm 1 + Halász 1968 + Dirichlet's theorem for odd $m \ge 5$).**
Let $\chi \bmod M$ be a primitive Dirichlet character of exact multiplicative order $m \ge 1$, and let $c(n) = (1 * \chi)(n) = \sum_{d \mid n} \chi(d) \in \mathbb{Z}[\zeta_m]$.
1. **$m = 1$ (principal):** $c(n) = \tau(n)$, bounded NAF mean; $E(2^k)$ is simply nonnormal for $k \ge 3$ (`GF-36`).
2. **$m$ even ($m = 2, 4, 6, 8, \ldots$, including quartic $q = 5, 13, 17$ and sextic $q = 7, 13, 19$):** Since $\chi : (\mathbb{Z}/M\mathbb{Z})^\times \to \mu_m$ is surjective and $-1 = \zeta_m^{m/2} \in \mu_m$, the primes $p$ with $\chi(p) = -1$ form $\varphi(M)/m$ reduced residue classes modulo $M$ and therefore have **Dirichlet density $1/m > 0$**; every such prime satisfies $c(p) = 1 + \chi(p) = 0$. By `GF-13` (Dirichlet's theorem + Selberg–Delange / Wirsing; *External input*), $\#\{n \le X : c(n) \ne 0\} = O(X / (\log X)^{1/m}) = o(X)$ (sparse support), so every $\mathbb{Z}$-linear projection of $\sum c(n) b^{-kn}$ belongs to **$K_b$** for **every base $b \ge 2$ and every $k \ge 1$**.
3. **$m = 3$ (cubic — exact critical order, zero external inputs):** Since $1 + \omega = -\omega^2$ is a root of unity, $w_\pm(\Lambda(c(n)))$ has finite mean.
   - *(New Alternating Cubic Family $L_{-,+}(4)$ at $k = 2$ for $\chi(2) = 1$):* Define
     ```math
     L_{-,+}(4) := \sum_{m \ge 1} \frac{\frac{2}{\sqrt{3}} \Im \chi(m)}{4^m + 1}
       = \sum_{n \ge 1} c_{\mathrm{alt}, -}(n) 4^{-n}, \qquad
     c_{\mathrm{alt}, -}(2^e u) = (1 - e) \cdot \frac{2}{\sqrt{3}} \Im((1 * \chi)(u)) \quad (u \text{ odd})
     ```
     whenever $\chi(2) = 1$. Because $L_2^+ = \frac{1}{2} \sum_{e \ge 0} w_\pm(1 - e) 2^{-e} \approx 0.79605$ replaces $L_2^{\mathrm{std}} \approx 1.18419$, applying `GF-44`'s Elementary Twisted Squarefull Convolution Lemma ($\frac{2}{3}$ factor) certifies at $k = 2$:
     - $M = 31$: $\rho_- \in [0.228495, 0.228504] < \frac{1}{4}$;
     - $M = 43$: $\rho_- \in [0.230753, 0.230762] < \frac{1}{4}$;
     - $M = 109$: $\rho_- \in [0.230631, 0.230639] < \frac{1}{4}$;
     - $M = 127$: $\rho_- \in [0.243667, 0.243676] < \frac{1}{4}$.
     By `GF-44` and Theorem C4.3 ($m_1^{(4)} = m_1^{(8)} = \frac{1}{4}$), **$L_{-,+}(4)$ for $M \in \{31, 43, 109, 127\}$ is unconditionally binary order-2 nonnormal AND unconditionally simply nonnormal in base $4$ and base $8$**, with **zero external inputs**.
   - *(New Unitary Alternating Cubic $L_{-,+}^*(4)$ at $k = 2$, $\chi(2) = 1$):* Taking unitary divisors gives exact rational rate $\rho_-^* = \frac{2}{3} \cdot \frac{3}{4} / 2 = \frac{1}{4} < \frac{9}{32} < \frac{1}{3}$, yielding $D^- \ge \frac{1}{6}$, non-4-normality in base $2$, and unconditional simple nonnormality in **base $16$**.
   - *(Universal $k = 1$ Cubic Barrier; Objective 4):* For **every** primitive cubic $\chi$, every local Euler factor at $p > 2$ satisfies $L_p \ge \frac{1 - p^{-2}}{1 - p^{-3}}$, so $\frac{2}{3} W_\chi \ge \frac{2}{3} \frac{\zeta(3)}{\zeta(2)} \ge 0.48715 > \frac{1}{3}$ for $L_-(2)$, and $\frac{2}{3} W_{\mathrm{alt}} \ge \frac{2}{3} \cdot \frac{7}{6} L_2^+ \frac{\zeta(3)}{\zeta(2)} \ge 0.45243 > \frac{1}{3}$ even for $L_{-,+}(2)$. Thus symmetric NAF transfer is **uniformly obstructed at $k = 1$** across all cubic moduli.
4. **$m \ge 5$ odd (quintic $q = 11, 31$, septic $q = 29, 43$, nonic $q = 19, 27, 37, \ldots$) — Cyclotomic-Unit Divergence Barrier (Objective 4):**
   For every odd $m \ge 5$ and every nonzero $\mathbb{Z}$-linear projection $\Lambda : \mathbb{Z}[\zeta_m] \to \mathbb{Z}$, the average NAF weight **diverges**:
   ```math
   \lim_{X \to \infty} \frac{1}{X} \sum_{n \le X} w_\pm\bigl(\Lambda((1 * \chi)(n))\bigr) = +\infty.
   ```
   Thus the condition $\mathrm{odd}(\lambda(M)) \mid 3$ of `GF-42` Theorem B5.3 is a **sharp algebraic boundary** for bounded NAF transfer.

*Proof of (4) (complete proof for $m = 5$ and every odd $m \ge 5$, explicitly treating null directions and degenerate $S$-unit subsums).*
We first give the concrete quintic case $m = 5$ (which exposes an important null-direction subtlety) and then the full unified proof for every odd $m \ge 5$.

- **Case $m = 5$ (explicit $\mathbb{Z}[\zeta_5]$ arithmetic and null-direction resolution):** Put $\varphi = \frac{1 + \sqrt{5}}{2} = -\zeta_5^2 - \zeta_5^3 \in \mathbb{Z}[\zeta_5]^\times$ ($\varphi^{-1} = \zeta_5 + \zeta_5^4$). Exact ring arithmetic (`scripts/phase26_mesoscopic_carries.py` Section 6.4) verifies:
  ```math
  1 + \zeta_5 = -\zeta_5^3 \varphi, \qquad
  1 + \zeta_5^4 = -\zeta_5^2 \varphi, \qquad
  1 + \zeta_5^2 = \zeta_5 \varphi^{-1}, \qquad
  1 + \zeta_5^3 = \zeta_5^4 \varphi^{-1}.
  ```
  Hence for every squarefree integer $n$ coprime to $M$, putting $k_j(n) := \#\{p \mid n : \chi(p) = \zeta_5^j\}$ ($0 \le j \le 4$),
  ```math
  (1 * \chi)(n) = 2^{k_0(n)} (-1)^{k_1(n) + k_4(n)} \zeta_5^{\tilde{t}(n)}\, \varphi^{r(n)}, \qquad
  \tilde{t}(n) \equiv 3 k_1 + k_2 + 4 k_3 + 2 k_4 \pmod 5, \qquad
  r(n) = (k_1 + k_4) - (k_2 + k_3),
  ```
  verified identically in $\mathbb{Z}[\zeta_5]$ across all $1{,}115$ squarefree $n \le 2000$ coprime to $11$. *Caution on null directions:* it is **false** that $u_r^{(t)} := \Lambda(\zeta_5^t \varphi^r)$ is non-degenerate for *every* residue $t \bmod 5$: for $\Lambda(a + b\zeta_5 + c\zeta_5^2 + d\zeta_5^3) = c - d$, $\varphi^r = F_{r-1} - F_r(\zeta_5^2 + \zeta_5^3)$ gives $\Lambda(\varphi^r) \equiv 0$ identically at $t = 0$ (verified for $0 \le r < 40$ in Section 6.4). Instead, because $\{1, \zeta_5, \zeta_5^2, \zeta_5^3, \zeta_5^4\}$ spans $\mathbb{Z}[\zeta_5]$ and $\Lambda \ne 0$, there exists at least one residue **$t^* \in \{0, 1, 2, 3, 4\}$ with $u_0 := \Lambda(\zeta_5^{t^*}) \ne 0$** (for $\Lambda = c - d$, $t^* = 2$ gives $u_0 = 1$ and $u_r^{(2)} = F_{r-1}$, verified for $0 \le r < 40$ in Section 6.4). Since $\varphi^2 = \varphi + 1$, $u_r^{(t^*)} = \alpha \varphi^r + \beta (-\varphi^{-1})^r$ with $\alpha = (u_1 + u_0 \varphi^{-1})/\sqrt{5}$ and $\beta = (u_0 \varphi - u_1)/\sqrt{5}$ ($u_1 = \Lambda(\zeta_5^{t^*} \varphi) \in \mathbb{Z}$); because $u_0 \in \mathbb{Z} \setminus \{0\}$ while $\varphi, \varphi^{-1} \notin \mathbb{Q}$, **both $\alpha \ne 0$ and $\beta \ne 0$**. Now fix any $B \ge 1$ and suppose $w_\pm(u_r^{(t^*)}) \le B$, i.e. $\alpha \varphi^r + \beta (-\varphi^{-1})^r = \sum_{\ell=1}^B \varepsilon_\ell 2^{e_\ell}$. Taking a minimal (non-degenerate) vanishing subsum containing $\alpha \varphi^r$: if it excludes $\beta(-\varphi^{-1})^r$, then $\alpha \varphi^r \in \mathbb{Q}$, which holds for at most one $r$ (since $\varphi^k \notin \mathbb{Q}$ for $k \ne 0$); if it includes $\beta(-\varphi^{-1})^r$, then by **Evertse (1984, *Compos. Math.* 53, Theorem 1)** on non-degenerate $S$-unit equations in $\mathbb{Q}(\sqrt{5})$ with $S = \{\text{infinite places}\} \cup \{\text{places above } 2, \text{ and valuations of } \alpha, \beta\}$, the ratio $\frac{\alpha}{\beta}(-\varphi^2)^r$ takes only finitely many values, allowing only finitely many $r \in \mathbb{Z}$. Meanwhile, by Halász's theorem (1968), $\{n \le X : \mu^2(n) = 1,\, \gcd(n, M) = 1,\, \tilde{t}(n) \equiv t^* \pmod 5\}$ has positive asymptotic density $\delta_M / 5 > 0$ ($\delta_M := \frac{6}{\pi^2} \prod_{p \mid M} \frac{p}{p+1}$), while for every fixed $r_0 \in \mathbb{Z}$ and every $Q \ge 1$, $\{n \le X : r(n) \equiv r_0 \pmod Q\}$ has density $1/Q$ (again by Halász on $e(b r(n)/Q)$, $1 \le b < Q$), forcing $\#\{n \le X : r(n) = r_0\} = o(X)$. Thus $w_\pm(\Lambda((1 * \chi)(n))) > B$ on a set of asymptotic density $\delta_M / 5 > 0$ for every $B \ge 1$, proving divergence.

- **General odd $m \ge 5$ (full Galois-orbit / minimal-subsum proof):** Fix any odd $m \ge 5$ and any nonzero $\mathbb{Z}$-linear $\Lambda : \mathbb{Z}[\zeta_m] \to \mathbb{Z}$. Let $K = \mathbb{Q}(\zeta_m)$ and $G = \operatorname{Gal}(K/\mathbb{Q})$ ($|G| = \varphi(m)$). By non-degeneracy of the trace pairing on $K/\mathbb{Q}$, there is a unique nonzero $c \in K^\times$ such that $\Lambda(x) = \operatorname{Tr}_{K/\mathbb{Q}}(cx) = \sum_{\sigma \in G} c_\sigma \sigma(x)$ with $c_\sigma := \sigma(c) \ne 0$ for every $\sigma \in G$. Because $m$ is odd, every $1 + \zeta_m^j$ ($1 \le j \le m - 1$) is a cyclotomic unit in $\mathbb{Z}[\zeta_m]^\times$ with explicit inverse $(1 + \zeta_m^j)^{-1} = \sum_{s=0}^{(m-1)/2} \zeta_m^{2sj} \in \mathbb{Z}[\zeta_m]$ (verified identically in $\mathbb{Z}[\zeta_m]$ for $m \in \{5, 7, 9\}$ in Section 6.4). For every squarefree $n$ coprime to $M$, putting $\mathbf{k}(n) = (k_1(n), \ldots, k_{m-1}(n))$ ($k_j(n) = \#\{p \mid n : \chi(p) = \zeta_m^j\}$) and $u_\sigma(\mathbf{k}) := \prod_{j=1}^{m-1} (1 + \sigma(\zeta_m)^j)^{k_j} \in \mathbb{Z}[\zeta_m]^\times$, 2-scale invariance gives $w_\pm(\Lambda((1 * \chi)(n))) = w_\pm\bigl(\sum_{\sigma \in G} c_\sigma u_\sigma(\mathbf{k}(n))\bigr)$.

  1. *Avoiding all conjugate-pair null directions simultaneously:* For every $\sigma \in G$, $\frac{1 + \bar{\sigma}(\zeta_m)^j}{1 + \sigma(\zeta_m)^j} = \sigma(\zeta_m)^{-j}$, so $\frac{u_{\bar{\sigma}}(\mathbf{k})}{u_\sigma(\mathbf{k})} = \sigma(\zeta_m)^{-t(\mathbf{k})}$ where $t(\mathbf{k}) := \sum_{j=1}^{m-1} j k_j \bmod m$. Hence each conjugate pair $\{\sigma, \bar{\sigma}\} \subseteq G$ satisfies $c_\sigma u_\sigma(\mathbf{k}) + c_{\bar{\sigma}} u_{\bar{\sigma}}(\mathbf{k}) = 0$ on **at most one** residue class of $t(\mathbf{k}) \bmod m$. Since there are only $\varphi(m)/2 \le (m - 1)/2 < m$ conjugate pairs in $G$, there exists a residue class **$t^* \in \mathbb{Z}/m\mathbb{Z}$** avoiding every conjugate-pair cancellation simultaneously. Set $\mathcal{E}(t^*) := \{n \le X : \mu^2(n) = 1,\, \gcd(n, M) = 1,\, t(\mathbf{k}(n)) \equiv t^* \pmod m\}$.
  2. *Reduction of bounded NAF weight on $\mathcal{E}(t^*)$ to finitely many affine hyperplanes:* Fix $B \ge 1$ and let $S$ be the fixed finite set of places of $K$ consisting of all infinite places, all places above $2$, and all finite places where any $c_\sigma$ has nonzero valuation. If $n \in \mathcal{E}(t^*)$ satisfies $w_\pm(\Lambda((1 * \chi)(n))) \le B$, then $\sum_{\sigma \in G} c_\sigma u_\sigma(\mathbf{k}(n)) - \sum_{\ell=1}^{B'} \varepsilon_\ell 2^{e_\ell} = 0$ for some $0 \le B' \le B$, $\varepsilon_\ell \in \{-1, 1\}$, and $e_\ell \in \mathbb{Z}$, an $S$-unit equation in $\mathcal{O}_{K, S}^\times$. Fix one $\sigma_0 \in G$ and take a **minimal** (no proper nonempty vanishing subsum) vanishing subsum $(\mathcal{I}, J)$ containing $\sigma_0$: $\sum_{\sigma \in \mathcal{I}} c_\sigma u_\sigma(\mathbf{k}) - \sum_{\ell \in J} \varepsilon_\ell 2^{e_\ell} = 0$. Since $m$ is odd, $\gcd(\frac{m-1}{2}, m) = 1$, so there exists $\tau \in G$ mapping $\zeta_m \mapsto \zeta_m^{(m-1)/2}$; choosing $j_1 \in \{1, \ldots, m - 1\}$ with $\sigma_0(\zeta_m)^{j_1} = \zeta_m$ gives $\tau(\sigma_0(\zeta_m)^{j_1}) = \zeta_m^{(m-1)/2}$ and hence $|1 + \sigma_0(\zeta_m)^{j_1}| = 2\cos(\frac{\pi}{m}) > 1 > 2\sin(\frac{\pi}{2m}) = |1 + \tau\sigma_0(\zeta_m)^{j_1}|$, so $\mathbf{v}_{\sigma_0, \tau} \cdot \mathbf{k} := \sum_{j=1}^{m-1} k_j \log\left|\frac{1 + \tau\sigma_0(\zeta_m)^j}{1 + \sigma_0(\zeta_m)^j}\right|$ is a **nonzero** linear functional. There are four exhaustive cases for $(\mathcal{I}, J)$:
     - *$\mathcal{I} = \{\sigma_0\}$:* Then $c_{\sigma_0} u_{\sigma_0}(\mathbf{k}) \in \mathbb{Q}^\times$, so $\frac{\tau(u_{\sigma_0}(\mathbf{k}))}{u_{\sigma_0}(\mathbf{k})} = \frac{c_{\sigma_0}}{\tau(c_{\sigma_0})}$; taking $\log|\cdot|$ confines $\mathbf{k}(n)$ to one affine hyperplane $\mathbf{v}_{\sigma_0, \tau} \cdot \mathbf{k}(n) = \text{const}$.
     - *$\mathcal{I} = \{\sigma_0, \bar{\sigma}_0\}$ and $J = \emptyset$:* **Impossible** on $\mathcal{E}(t^*)$ by our choice of $t^*$.
     - *$\mathcal{I} = \{\sigma_0, \bar{\sigma}_0\}$ and $J \ne \emptyset$:* By **Evertse (1984, *Compos. Math.* 53, Theorem 1)**, for any $\ell_0 \in J$ the projective ratio $c_{\sigma_0} u_{\sigma_0}(\mathbf{k}) / 2^{e_{\ell_0}}$ takes only finitely many values $\gamma \in K^\times$; applying $\tau$ cancels $2^{e_{\ell_0}} \in \mathbb{Q}$ and forces $\frac{\tau(u_{\sigma_0}(\mathbf{k}))}{u_{\sigma_0}(\mathbf{k})} = \frac{\tau(\gamma/c_{\sigma_0})}{\gamma/c_{\sigma_0}}$, confining $\mathbf{k}(n)$ to finitely many affine hyperplanes $\mathbf{v}_{\sigma_0, \tau} \cdot \mathbf{k}(n) = \text{const}$.
     - *$\mathcal{I}$ contains some $\sigma_1 \notin \{\sigma_0, \bar{\sigma}_0\}$:* By Evertse (1984, Theorem 1), $\frac{u_{\sigma_1}(\mathbf{k})}{u_{\sigma_0}(\mathbf{k})}$ takes only finitely many values $\gamma \in K^\times$. Since $\sigma_1 \notin \{\sigma_0, \bar{\sigma}_0\}$, we have $\sigma_1(\zeta_m)^{j_1} = \zeta_m^b$ with $b' := \min(b \bmod m, m - (b \bmod m)) \in \{2, \ldots, \frac{m-1}{2}\}$, so $|1 + \sigma_1(\zeta_m)^{j_1}| = 2\cos(\frac{\pi b'}{m}) < 2\cos(\frac{\pi}{m}) = |1 + \sigma_0(\zeta_m)^{j_1}|$ (verified for $m \in \{5, 7, 9\}$ in Section 6.4). Taking $\log|\cdot|$ confines $\mathbf{k}(n)$ to finitely many affine hyperplanes $\mathbf{v}_{\sigma_0, \sigma_1} \cdot \mathbf{k}(n) = \text{const}$ with $\mathbf{v}_{\sigma_0, \sigma_1} \ne \mathbf{0}$.
  3. *Positive density of $\mathcal{E}(t^*)$ and zero density of every affine hyperplane (via Halász):* By Fourier orthogonality mod $m$, $|\mathcal{E}(t^*)|/X \to \delta_M / m > 0$ because for every $1 \le a \le m - 1$, $f_a(n) := \mu^2(n) \mathbf{1}_{\gcd(n, M)=1} e(a t(\mathbf{k}(n))/m)$ takes $f_a(p) = 1$ on $\chi(p) = 1$ (density $1/m$) and $f_a(p) = e(a/m) \ne 1$ on $\chi(p) = \zeta_m$ (density $1/m$), so $\sum_p \frac{1 - \Re(f_a(p) p^{-is})}{p} = \infty$ for all $s \in \mathbb{R}$ (at $s = 0$ by Dirichlet's theorem on $\chi(p) = \zeta_m$; at $s \ne 0$ by $\chi(p) = 1$ and classical non-vanishing of $L(1 + is, \chi^r)$), whence **Halász's theorem (1968)** gives $\frac{1}{X} \sum_{n \le X} f_a(n) \to 0$. Similarly, for any nonzero $\mathbf{v} \in \mathbb{R}^{m-1}$ (pick $j^*$ with $v_{j^*} \ne 0$) and any $C \in \mathbb{R}$, the Fejér identity $\mathbf{1}_{y = 0} \le \bigl(\frac{\sin \pi y}{\pi y}\bigr)^2 = \int_{-1}^{1} (1 - |\theta|) e(\theta y)\, d\theta$ yields
     ```math
     \frac{1}{X} \#\bigl\{n \le X : \mathbf{v} \cdot \mathbf{k}(n) = C\bigr\}
       \le \int_{-1}^{1} (1 - |\theta|) e(-\theta C) \left(\frac{1}{X} \sum_{n \le X} g_\theta(n)\right) d\theta, \qquad
     g_\theta(n) := e\bigl(\theta\, \mathbf{v} \cdot \mathbf{k}(n)\bigr).
     ```
     For every $\theta \in [-1, 1] \setminus \frac{1}{v_{j^*}} \mathbb{Z}$ (all but finitely many $\theta$), $g_\theta(p) = e(\theta v_{j^*}) \ne 1$ on $\chi(p) = \zeta_m^{j^*}$ while $g_\theta(p) = 1$ on $\chi(p) = 1$, so Halász's theorem gives $\frac{1}{X} \sum_{n \le X} g_\theta(n) \to 0$. By Dominated Convergence, every affine hyperplane has asymptotic density $0$.

  Combining (1)–(3), for every $B \ge 1$ we have $w_\pm(\Lambda((1 * \chi)(n))) > B$ on a set of asymptotic density $\delta_M / m > 0$, whence $\frac{1}{X} \sum_{n \le X} w_\pm(\Lambda((1 * \chi)(n))) \to +\infty$. $\square$

### 4.2 New full-density quadratic-twisted family $\tau_3 * \chi_D$

**Theorem C5.2 (Full-density quadratic-twisted family $\tau_3 * \chi_D$; Paper proof + Finite certificate; External inputs: None for (1) and base-2 simple nonnormality in (2); 2-D Fundamental Lemma, Dirichlet's theorem, and Halász 1968 for $D^+ < 1$, $\notin K_2$, and $D^-(2^k) \to 1$).**
Let $\chi_D$ be any primitive real quadratic Dirichlet character ($\chi_D(n) = (\frac{D}{n})$) and define $a_D(n) := (\tau_3 * \chi_D)(n) = \sum_{d \mid n} \tau_3(d) \chi_D(n/d) = 2^{V_D(n)} U_D(n)$ (with $U_D(n) = \mathrm{odd}(a_D(n))$) and $F_D(2^k) := \sum_{n \ge 1} a_D(n) 2^{-kn}$.
1. *(Full nonnegative support and prime power-of-2 property.)* For every prime $p \nmid D$, $a_D(p) = 3 + \chi_D(p) \in \{2, 4\}$ (both powers of $2$, so $s_2(a_D(p)) = 1$ and $U_D(p) = 1$), and for every $e \ge 0$:
   ```math
   a_D(p^e) = \begin{cases}
     \binom{e + 3}{3} & \text{if } \chi_D(p) = +1, \\
     \binom{e + 2}{2} & \text{if } \chi_D(p) = 0, \\
     \bigl\lfloor \frac{e + 2}{2} \bigr\rfloor \bigl\lfloor \frac{e + 3}{2} \bigr\rfloor & \text{if } \chi_D(p) = -1.
   \end{cases}
   ```
   In particular $a_D(n) \ge 1$ for **every** $n \ge 1$ (full density $1$), $V_D(p) = v_2(a_D(p)) = 2$ if $\chi_D(p) = +1$ and $1$ if $\chi_D(p) = -1$, and $C_{U, D} := \lim_{X \to \infty} \frac{1}{X} \sum_{n \le X} U_D(n) = \prod_p (1 - \frac{1}{p}) \sum_{e \ge 0} U_D(p^e) p^{-e} < \infty$.
2. *(Unconditional simple nonnormality — zero external inputs.)* By submultiplicativity of $s_2$, $\limsup f_{1, N}(F_D(2^k); 2) \le C_{\mathrm{pop}}(D) / k$, where Section 6.5 certifies:
   - **$D = +5$:** $C_{\mathrm{pop}}(+5) \in [1.425543, 1.425568] \implies C_{\mathrm{pop}}(+5)/3 \le 0.475190 < \frac{1}{2}$ (**unconditional simple nonnormality and $D^- > 0$ already for all $k \ge 3$**, zero external inputs);
   - **$D = -3$:** $C_{\mathrm{pop}}(-3) \in [1.584160, 1.584188] \implies C_{\mathrm{pop}}(-3)/4 \le 0.396047 < \frac{1}{2}$ (all $k \ge 4$);
   - **$D = -4$:** $C_{\mathrm{pop}}(-4) \in [1.751324, 1.751354] \implies C_{\mathrm{pop}}(-4)/4 \le 0.437839 < \frac{1}{2}$ (all $k \ge 4$);
   - **$D = +8$:** $C_{\mathrm{pop}}(+8) \in [1.717434, 1.717464] \implies C_{\mathrm{pop}}(+8)/4 \le 0.429366 < \frac{1}{2}$ (all $k \ge 4$).
3. *(Explicit $k$-ranges for $D^+ < 1$, $\notin K_2$, and construction-radix $D^- \to 1$.)* For **every** primitive quadratic $\chi_D$ and **every integer $k > C_{U, D}$**, we have unconditionally
   ```math
   D^+(F_D(2^k); 2) < 1, \qquad F_D(2^k) \notin K_2,
   ```
   and for **every integer $k \ge 1$**,
   ```math
   D^-\bigl(F_D(2^k); 2^k\bigr) \ge \max\!\left(0,\; 1 - 2\sqrt{\frac{C_{U, D}}{k}}\right), \qquad
   1 - D^-\bigl(F_D(2^k); 2^k\bigr) \ll_D \frac{\log k}{k} \longrightarrow 0 \quad (k \to \infty).
   ```
   Using the pure-integer certified odd-part means $C_{U, D}$ of Section 6.5b:
   - **$D = +5$:** $C_{U, +5} \in [2.602773, 2.602948] < 3 \implies$ **$0 < D^-(F_{+5}(2^k); 2) \le D^+(F_{+5}(2^k); 2) < 1$ and $F_{+5}(2^k) \notin K_2$ for all $k \ge 3$**;
   - **$D = -3$:** $C_{U, -3} \in [3.321945, 3.322168] < 4 \implies$ **$0 < D^- \le D^+ < 1$ and $\notin K_2$ for all $k \ge 4$**;
   - **$D = +8$:** $C_{U, +8} \in [3.944773, 3.945037] < 4 \implies$ **$0 < D^- \le D^+ < 1$ and $\notin K_2$ for all $k \ge 4$**;
   - **$D = -4$:** $C_{U, -4} \in [4.347688, 4.347979] < 5 \implies$ **$0 < D^- \le D^+ < 1$ and $\notin K_2$ for all $k \ge 5$**.

*Proof of (3).*
- *$D^+(F_D(2^k); 2) < 1$ and $F_D(2^k) \notin K_2$ for all $k > C_{U, D}$:* Since $a_D(m) = 2^{V_D(m)} U_D(m) \ge 1$ everywhere, $a_D(m) \le \tau_4(m) \ll_\varepsilon m^\varepsilon$, and $C_{U, D} < \infty$, `GF-42` Lemma B1.2 gives dead-position density $|\mathcal{D}_N|/N \ge 1 - C_{U, D}/k - o(1) > 0$ whenever $k > C_{U, D}$. We adapt `GF-42` Theorem B1.3 Steps 1–4 to the two-valued prime weight $V_D(p) \in \{1, 2\}$:
  - Define the good set $\mathcal{G}$ exactly as in `GF-42` Thm B1.3 Step 1 with $p_1 \ge \max(5, |D|, \lceil 200/\varepsilon \rceil)$; on $\mathcal{G}$, $V_D(m) = \omega_{\mathrm{inert}}(m) + 2 \omega_{\mathrm{split}}(m) + V_{\mathrm{bdd}}(m)$ with $0 \le V_{\mathrm{bdd}}(m) \le B_0 := K_0 + 2\lfloor 1/\eta \rfloor$.
  - For $d > D_0 := \lceil (20 L + G + B_0)/k \rceil$, $kd < V_D(n) + G$ forces $\omega(n) > 10 L$, so Step 2 bounds the tail identically by $O(M (\log M)^{3 - 10\ln 2}) = o(M)$.
  - For $1 \le d \le D_0$, the **standard 2-D Fundamental Lemma** on $\mathcal{P}_d = \{p \in (p_1, M^\eta] : p \nmid d\}$ ($g(p) = 2/p$) applies **unchanged** to $A_d(u_1, u_2)$, producing the independent random sum $S_d = \sum_{p \in \mathcal{P}_d} \xi_p$ where $\xi_p \in \{-1, 0, +1\}$ (with $\Pr(\xi_p = \pm 1) = 1/p$) for inert primes $\chi_D(p) = -1$ and $\xi_p \in \{-2, 0, +2\}$ (with $\Pr(\xi_p = \pm 2) = 1/p$) for split primes $\chi_D(p) = +1$.
  - Put $E_d^{(-)} := \sum_{p \in \mathcal{P}_d,\, \chi_D(p) = -1} \frac{1}{p}$ and $E_d^{(+)} := \sum_{p \in \mathcal{P}_d,\, \chi_D(p) = +1} \frac{1}{p}$. By Dirichlet's theorem on primes in arithmetic progressions, $E_d^{(-)}, E_d^{(+)} = \frac{1}{2} L + O_{\chi_D, \eta, p_1}(1) - O(\log\log\log L)$ uniformly for $1 \le d \le D_0$, so the variance $V_d := 2 E_d^{(-)} + 8 E_d^{(+)} = (5 + o(1)) L$ satisfies $V_{\max}/V_{\min} \to 1$. In the contour-shifted Fourier integral $\Pr(S_d = h) = \frac{e^{-\lambda h}}{2\pi} \int_{-\pi}^{\pi} e^{-iht} \prod_{\chi_D(p)=-1}(1 + \frac{2(\cosh(\lambda + it) - 1)}{p}) \prod_{\chi_D(p)=+1}(1 + \frac{2(\cosh(2\lambda + 2it) - 1)}{p})\, dt$ ($0 \le \lambda \le \frac{1}{2} L^{-1/3}$): on $|t| \in [\pi/2, \pi]$, $\cos t \le 0$ forces the real exponent to be $\le -2 E_d^{(-)} + O(L^{1/3}) \le -\frac{1}{2} L$, contributing $O(e^{-L/2})$ (ruling out any secondary peak at $t = \pm \pi$ from $\cos 2t = 1$); on $L^{-1/3} < |t| \le \pi/2$, $2 E_d^{(-)}(1 - \cos t) \ge \frac{4}{\pi^2} E_d^{(-)} L^{-2/3} \gg L^{1/3}$ while $\cos 2t - 1 \le 0$, contributing $O(e^{-c L^{1/3}})$; and on $|t| \le L^{-1/3}$, $2 E_d^{(-)}\cosh\lambda(1 - \cos t) + 2 E_d^{(+)}\cosh(2\lambda)(1 - \cos 2t) = (\frac{1}{2} V_d + O(L^{1/3})) t^2 + O(L t^4)$, giving the Gaussian peak $\frac{1 + o(1)}{\sqrt{2\pi V_d}}$. Choosing $\lambda = h / V_d$ for $0 \le h \le V_d^{2/3}$ (and $\lambda = \frac{1}{4} V_d^{-1/3}$ for $h > V_d^{2/3}$) yields $\Pr(S_d = h) \le \frac{1 + \varepsilon}{\sqrt{2\pi V_d}} e^{-h^2/(2 V_d)} + O(e^{-L/3})$. Summing over $d \ge 1$ integrates $\int_0^\infty \frac{e^{-u^2/(2 V_{\max})}}{\sqrt{2\pi V_{\min}}}\, du = \frac{1}{2}\sqrt{V_{\max}/V_{\min}} \to \frac{1}{2}$, cancelling $V_d \sim 5L$ identically and giving $\limsup \frac{1}{N} \sum_{a=1}^N (Z_a^{\mathcal{G}})^2 \le \frac{G}{k} + (1 + \varepsilon)^4 \frac{(G + B_0)^2}{k^2}$. Paley–Zygmund and `GF-42` Lemma B1.2(2)–(3) then yield $D^+(F_D(2^k); 2) < 1$ and $F_D(2^k) \notin K_2$ for every $k > C_{U, D}$.
- *Construction-radix limit $D^-(F_D(2^k); 2^k) \to 1$:* In `GF-42` Theorem B2.1, the only arithmetic input is $\frac{1}{N} \sum_{n \le N} U_D(n)^s e(u V_D(n)/k) \to 0$ for every $1 \le u \le k - 1$ and $s \in (0, 1]$. After $y$-good squarefree-tail truncation (`GF-36` Lemma 3.2, valid since $U_D(p) = 1$ for $p > |D|$ and $U_D(p^e) \le \binom{e+3}{3}$), the 1-bounded multiplicative function $f(r) = \mathbf{1}_{\mathrm{good}}(r) e(u V_D(r)/k)$ satisfies $f(p) = e(u/k) \ne 1$ on inert primes $\chi_D(p) = -1$ (density $1/2$) and $f(p) = e(2u/k)$ on split primes $\chi_D(p) = +1$ (density $1/2$). Hence for every $t \in \mathbb{R}$, $\sum_p \frac{1 - \Re(f(p) p^{-it})}{p} = \infty$ (at $t = 0$ from inert primes; at $t \ne 0$ from non-vanishing of $\zeta(1 + it)$ and $L(1 + it, \chi_D)$). By Halász's theorem (1968), $V_D(n) \bmod k$ equidistributes uniformly over all $k$ classes ($g = 1$, no coset loss for any $k \ge 1$), so `GF-42` Theorem B2.1(1)–(3) applies with $g = 1$ and gives $1 - D^-(F_D(2^k); 2^k) \le \inf_{0 < s \le 1} (\frac{2^s(s+1) C_{U, D}(s)}{k(2^s - 1)})^{1/(s+1)} \le 2\sqrt{C_{U, D}/k}$ and $O_D(\frac{\log k}{k}) \to 0$.
- *Certified $C_{U, D}$ enclosures:* Section 6.5b computes the exact local Euler factors for $p \le 20{,}000$ with exact generating-function prime-power tail $(1 - 1/p)^{-3} - (1 - 1/p) \sum_{e < E_{\max}} \binom{e+3}{3} p^{-e}$ and prime tail $L_p(U_D) \le 1 + 4/p^2 + 17/p^3$ ($p > 20{,}000$), certifying all four enclosures and explicit thresholds $k_+(5) = 3$, $k_+(-3) = 4$, $k_+(8) = 4$, $k_+(-4) = 5$. $\square$

### 4.3 Unconditional base-2 disjunctivity of $E(2^k)$, $E_{\mathrm{odd}}(2^k)$, and $E_+(2^k)$ for every $k \ge 1$

Resolving `GF-42` Open Question 4 completely—with **zero external inputs**—we prove quantitative base-2 disjunctivity simultaneously for $E(2^k)$, $E_{\mathrm{odd}}(2^k)$, and the signed series $E_+(2^k)$ for **every $k \ge 1$**.

**Theorem C5.3 (Unconditional Base-2 Disjunctivity of $E(2^k), E_{\mathrm{odd}}(2^k), E_+(2^k)$ for all $k \ge 1$; Paper proof + Finite certificate, zero external inputs).**
Let $k \ge 1$, $F \in \{E(2^k), E_{\mathrm{odd}}(2^k), E_+(2^k)\}$, and let $w \in \{0, 1\}^\ell$ ($\ell \ge 1$) be **any** finite binary word. Then for all sufficiently large $N$ (depending on $k, w$), counting occurrences wholly contained within the first $N$ fractional binary digits $d_1(F; 2), \ldots, d_N(F; 2)$,
```math
\#\bigl\{0 \le n \le N - \ell : d_{n+1}(F; 2) \cdots d_{n+\ell}(F; 2) = w\bigr\}
  \ge N \exp\!\left(-\frac{37}{k} (\log\log N)^3\right).
```
In particular:
1. For **every $k \ge 3$**, $E(2^k)$, $E_{\mathrm{odd}}(2^k)$, and $E_+(2^k)$ are **unconditionally disjunctively nonnormal in base $2$**: every binary word appears with the above lower count, while $D^-(F; 2) > 0$ (`GF-36` for $E(2^k)$ and $E_{\mathrm{odd}}(2^k)$; `GF-40` / `GF-44` for $E_+(2^k)$).
2. At $k = 1$, **$E_{\mathrm{odd}}(2)$ (`BC-38`)** and **$E_+(2)$ (`BC-39`)**, alongside **$E(2)$ (`BC-37`)**, are **unconditionally disjunctive in base $2$** with zero external inputs. *(Attribution & evidence note: Captain Sude's external elementary Lean release `erdos-borwein-disjunctivity-elementary` (8 September 2026) gives a **Lean-verified** count $\ge N \exp(-70{,}000 (\log\log N)^3)$ for $E(2)$ (`BC-37`) using elementary CRT prime-planting, squarefree cofactors, and a variable reading position; Theorem C5.3 is a **Paper proof** (not yet formalized in Lean 4) in the same elementary CRT + Markov lineage that introduces the odd-target guard-bit lemma for signed tails, unified $3^{W-1}$ planting across all three series $E(2^k), E_{\mathrm{odd}}(2^k), E_+(2^k)$ for every $k \ge 1$, and tight triangular $Q_s$ prime counts reducing the paper exponent constant to $37/k$. No benchmark file is modified here.)*

*Proof.*
**Step 1 (Odd-Target Guard-Bit Lemma — works identically for signed and unsigned tails).** Encode the target word $w = b_1 \cdots b_\ell \in \{0, 1\}^\ell$ as the **odd** integer
```math
W := 2^{\ell + 1} + 2 \cdot \mathrm{val}_2(w) + 1 \in \bigl[2^{\ell + 1} + 1,\, 2^{\ell + 2} - 1\bigr],
```
whose binary expansion is `1` $\cdot w \cdot$ `1` (length $\ell + 2$). Because $W$ is **odd**, its least significant bit is `1`. Therefore, for **every** real perturbation $\varepsilon \in (-1, 1)$—positive **or** negative—we have $\lfloor W + \varepsilon \rfloor \in \{W - 1, W\}$:
- if $0 \le \varepsilon < 1$, $\lfloor W + \varepsilon \rfloor = W$, whose middle $\ell$ bits are $w$;
- if $-1 < \varepsilon < 0$, $\lfloor W + \varepsilon \rfloor = W - 1$, which flips **only** the LSB `1` $\to$ `0` and leaves all higher bits (in particular the middle $\ell$ bits $w$) unchanged.

This is a 2-line algebraic identity needing no finite certificate (`scripts/phase26_mesoscopic_carries.py` Section 6.6 additionally sanity-checks it on all $62$ words of length $1 \le \ell \le 5$ across signed rationals in $(-1, 1)$ alongside $1{,}000$ coefficient/multiplicativity checks and $6/6$ end-to-end toy CRT plantings on $E(8), E_{\mathrm{odd}}(8), E_+(8)$).

**Step 2 (Unified $3^{W-1}$ planting across $E, E_{\mathrm{odd}}, E_+$).** Set $X := \lfloor N/k \rfloor$, $L := \log\log X$, and $S_2 := \lceil \frac{\log_2 X}{k} \rceil$. Define
```math
r := \lceil 2 \log_2 \log X \rceil, \qquad
R := r + \lfloor 3 L \rfloor + \ell + 4, \qquad
S := \left\lfloor \frac{R}{k} \right\rfloor.
```
Choose pairwise disjoint sets of primes all strictly exceeding $\max(4 \log_2 X, 3^{W-1}, S + S_2 + 10)$:
- $P_0$: product of $r$ distinct primes;
- $Q_s$ ($1 \le s \le S$): product of $R - k s \ge 0$ distinct primes.

The total number of planted primes is $T_{\mathrm{pr}} = r + \sum_{s=1}^S (R - ks) \le r + \frac{R^2}{2k}$. Since the smallest planted prime is $\asymp \log X$ and $T_{\mathrm{pr}} = O(L^2)$, by Chebyshev's elementary prime bound every planted prime is $\ll \log X$, so $\log p \le (1 + o(1)) L$. Put $M_0 := 2 \cdot 3^W \cdot P_0^2 \cdot \prod_{s=1}^S Q_s^2$. Then
```math
\log M_0 = O_w(1) + 2 \sum_{p\text{ planted}} \log p \le \frac{R^2}{k}(1 + o(1)) L.
```
Since $R = (\frac{2}{\ln 2} + 3 + o(1)) L$ and Section 6.6 certifies $(\frac{2}{\ln 2} + 3)^2 \le 34.6379 < 35 < 37$, we obtain $M_0 \le \exp\bigl(\frac{35}{k} L^3\bigr)$ (in particular $M_0 \le X^{1/4}$) for all large $X$.

By the Chinese Remainder Theorem, pick $m_* \in [1, M_0)$ satisfying:
- $m_* \equiv 1 \pmod 2$ (so $m_0$ is **odd**);
- $m_* \equiv 3^{W - 1} \pmod{3^W}$ (so $3^{W-1} \parallel m_0$);
- $m_* \equiv P_0 \pmod{P_0^2}$ (so $P_0 \parallel m_0$);
- $m_* \equiv s + Q_s \pmod{Q_s^2}$ for each $1 \le s \le S$ (so $Q_s \parallel (m_0 - s)$).

**Step 3 (Typical $t \in [1, T']$ with explicit truncation and exact signed isolation).** Put $T := \lfloor (X - S_2) / M_0 \rfloor$ and $T' := T - 1$. Consider $m_0 = m_0(t) := m_* + M_0 t$ for all integers **$t \in [1, T']$** (exactly $T'$ candidates). Since $1 \le m_* < M_0$, every $t \in [1, T']$ satisfies
```math
M_0 < m_0(t) < M_0 + M_0(T - 1) = M_0 T \le X - S_2
```
strictly (eliminating any $k M_0$ overshoot beyond $N$!). Because $M_0 \le X^{1/4}$, we have $T' \ge \frac{1}{2} X^{3/4}$ (so $\sqrt{X} = o(T')$) and $T' \ge \frac{X}{2 M_0}$ for all large $X$. Since $\gcd(m_*, M_0) = 3^{W-1} P_0$ (as every $p \mid Q_s$ exceeds $S \ge s$, so $p \nmid m_*$), we may write $m_0(t) = 3^{W-1} P_0 u(t)$ where $u(t) = a_0 + b_0 t < X$ has $\gcd(a_0, b_0) = 1$ and $\gcd(u(t), 6 P_0 \prod_{s=1}^S Q_s) = 1$ for every $t$. Call $t \in [1, T']$ *good* if:
1. *$u(t)$ is squarefree:* Every prime $p$ with $p^2 \mid u(t)$ satisfies $p \ge 5$, $p \nmid b_0$, and $p \le \sqrt{X}$. Splitting at $Y := T'^{1/2}$:
   - For $5 \le p \le Y$ ($p \nmid b_0$), $a_0 + b_0 t \equiv 0 \pmod{p^2}$ has at most $\lfloor T'/p^2 \rfloor + 1 \le T'/p^2 + 1$ solutions in $[1, T']$, summing to at most $T' \sum_{p \ge 5} p^{-2} + Y \le \frac{7}{50} T' + T'^{1/2}$ (since $\sum_{p \ge 5} p^{-2} \le \frac{1}{25} + \sum_{k \ge 3} \frac{1}{(2k-1)(2k+1)} = \frac{1}{25} + \frac{1}{10} = \frac{7}{50}$).
   - For $Y < p \le \sqrt{X}$ ($p \nmid b_0$), since $p^2 > T'$, there is at most $1$ solution $t \in [1, T']$ per prime, contributing at most $\pi(\sqrt{X}) \le \sqrt{X} = o(T')$.
   Hence condition (1) excludes at most $(\frac{7}{50} + o(1)) T'$ values of $t \in [1, T']$.
2. *$\omega(u(t)) \le 3 L$:* Truncate the distinct prime factors of $u(t)$ explicitly at $Y = T'^{1/2} \ge \frac{1}{2} X^{3/8}$. Because $u(t) < X$, every $t \in [1, T']$ satisfies $\omega_{> Y}(u(t)) \le \lfloor \frac{\log X}{\log Y} \rfloor \le 2$ deterministically (for large $X$). For $p \le Y$ ($p \nmid b_0$), $p \mid u(t)$ holds for at most $T'/p + 1$ integers $t \in [1, T']$, so
   ```math
   \sum_{t = 1}^{T'} \omega(u(t))
     \le 2 T' + \sum_{p \le Y} \left(\frac{T'}{p} + 1\right)
     \le T' \bigl(L + O(1)\bigr) + T'^{1/2} = (1 + o(1)) T' L.
   ```
   By Markov's inequality, condition (2) excludes at most $(\frac{1}{3} + o(1)) T'$ values of $t \in [1, T']$.
3. *$\sum_{j = 1}^{S_2} \tau(m_0(t) + j) 2^{-kj} \le \frac{1}{8} \cdot 2^r$:* Fix $1 \le j \le S_2$ and put $g_j := \gcd(m_* + j, M_0)$. Because every planted prime $p \mid P_0 \prod_{s=1}^S Q_s$ exceeds $S + S_2 + 10 > s + j$, no prime $p \mid Q_s$ can divide $m_* + j$ (else $p \mid (s + j)$), and no prime $p \mid P_0$ can divide $m_* + j$ (else $p \mid j$). Hence $g_j = \gcd(m_* + j, 2 \cdot 3^W) \mid 2 \cdot 3^{\min(W, v_3(j)+1)} \mid 2 \cdot 3^W$, so $\tau(g_j) \le 2(W + 1)$ uniformly in $j$. Write $m_0(t) + j = g_j v_j(t)$ with $v_j(t) = a_j + b_j t$, $\gcd(a_j, b_j) = 1$, and $1 \le v_j(t) \le m_0(t) + j < X$ (from $m_0(t) < X - S_2$). By Dirichlet's hyperbola method, $\tau(v_j(t)) \le 2 \#\{d < \sqrt{X} : d \mid v_j(t)\}$; only integers $d < \sqrt{X}$ with $\gcd(d, b_j) = 1$ can divide $a_j + b_j t$, each occurring at most $T'/d + 1$ times in $[1, T']$. Summing over $d < \sqrt{X}$ and using $\sqrt{X} = o(T')$ yields
   ```math
   \frac{1}{T'} \sum_{t = 1}^{T'} \tau(m_0(t) + j)
     \le \tau(g_j) \cdot \frac{2}{T'} \sum_{d < \sqrt{X}} \left(\frac{T'}{d} + 1\right)
     \le 2 \tau(g_j) \log X \le 4(W + 1) \log X
   ```
   for all large $X$, uniformly for $1 \le j \le S_2$. Summing against $2^{-kj}$ gives $\frac{1}{T'} \sum_{t=1}^{T'} \sum_{j=1}^{S_2} \tau(m_0(t) + j) 2^{-kj} \le 4(W + 1) \log X = o_w(2^r)$ (as $2^r \ge (\log X)^2$), so Markov's inequality excludes at most $o_w(T')$ values of $t \in [1, T']$.

Combining (1)–(3) on the $T'$ integers $t \in [1, T']$ leaves at least
```math
\left(1 - \frac{7}{50} - \frac{1}{3} - o_w(1)\right) T'
  = \left(\frac{79}{150} - o_w(1)\right) T'
  \ge \frac{1}{2} T'
```
good integers $t \in [1, T']$ for all sufficiently large $N$.

For any good $t$:
- Because $m_0 = 3^{W-1} P_0 u(t)$ is **odd** with $P_0 u(t)$ squarefree and coprime to $6$, all three arithmetic coefficients coincide **identically**:
  ```math
  \tau(m_0) = \tau_{\mathrm{odd}}(m_0) = a_+(m_0) = +W \cdot 2^{V_0}, \qquad V_0 := r + \omega(u(t)) \le r + \lfloor 3L \rfloor.
  ```
- Set the target bit-shift $J := k m_0 - V_0$. Then $2^J \cdot a(m_0) 2^{-k m_0} = W$ **exactly**.
- *Terms $m < m_0$:*
  - For $m = m_0 - s$ with $1 \le s \le S$: since $Q_s \parallel (m_0 - s)$ has $R - ks$ distinct odd prime factors, $2^{R - ks} \mid a(m_0 - s)$ for all three multiplicative functions $a \in \{\tau, \tau_{\mathrm{odd}}, a_+\}$ (as $Q_s$ is odd squarefree, so $\tau(Q_s) = \tau_{\mathrm{odd}}(Q_s) = 2^{R - ks}$ divides $a(m_0 - s)$ regardless of sign and even when $m_0 - s$ is even). Therefore
    ```math
    2^J \cdot a(m_0 - s) 2^{-k(m_0 - s)} = \frac{a(m_0 - s)}{2^{R - ks}} \cdot 2^{(R - ks) + ks - V_0} \in 2^{R - V_0} \mathbb{Z} \subseteq 2^{\ell + 4} \mathbb{Z},
    ```
    contributing an **exact integer multiple of $2^{\ell + 4}$** (strictly above the MSB of $W < 2^{\ell + 2}$ — zero interference with $W$, even for negative $a_+$).
  - For $m < m_0 - S$: $k(m_0 - m) \ge k(S + 1) > R \ge V_0 + \ell + 4$, so $2^J \cdot a(m) 2^{-km} \in 2^{k(m_0 - m) - V_0} \mathbb{Z} \subseteq 2^{\ell + 4} \mathbb{Z}$ **automatically**.
- *Terms $m > m_0$:* Every $a \in \{\tau, \tau_{\mathrm{odd}}, a_+\}$ satisfies $|a(m)| \le \tau(m)$ for all $m \ge 1$ (since $|1 - e| \le e + 1$ for every $e \ge 0$). Splitting at $S_2 = \lceil \frac{\log_2 X}{k} \rceil$:
  ```math
  |\varepsilon| := \left|2^J \sum_{m > m_0} a(m) 2^{-km}\right|
    \le 2^{-V_0} \sum_{j = 1}^{S_2} \tau(m_0 + j) 2^{-kj} + 2^{-V_0} \sum_{j > S_2} \tau(m_0 + j) 2^{-kj}.
  ```
  By condition (3) (and $V_0 \ge r$), the first sum is $\le \frac{1}{8}$. For the second sum, $\tau(m_0 + j) \le 2\sqrt{m_0 + j} < 2\sqrt{X + j}$ and $k S_2 \ge \log_2 X$, so $\sum_{j > S_2} 2\sqrt{X + j}\, 2^{-kj} \le 4 \sqrt{X} \cdot X^{-1} = 4 X^{-1/2} < \frac{1}{8}$ deterministically for all large $X$.

Hence $|\varepsilon| < \frac{1}{8} + \frac{1}{8} = \frac{1}{4} < 1$, and by Step 1 the binary digits of $F$ at positions $J - \ell, \ldots, J - 1$ equal **$w$ identically**—an occurrence at 0-based start $n(t) := J(t) - \ell - 1$. Because $M_0 < m_0(t) < X - S_2 \le N/k - (\log_2 X)/k$ and $r \le V_0(t) \le r + 3L$, we have $0 \le n(t) < n(t) + \ell = J(t) - 1 < N - \log_2 X < N$ for all large $N$, so every occurrence lies **wholly inside $[0, N)$**. Finally, distinct good $t_1 < t_2$ satisfy $J(t_2) - J(t_1) = k M_0 (t_2 - t_1) - (V_0(t_2) - V_0(t_1)) \ge k M_0 - 3L > 0$, so the starts $n(t)$ are **strictly distinct**, yielding at least
```math
\frac{1}{2} T' \ge \frac{X}{4 M_0} \ge \frac{N}{5 k} \exp\!\left(-\frac{35}{k} (\log\log N)^3\right)
  \ge N \exp\!\left(-\frac{37}{k} (\log\log N)^3\right)
```
distinct occurrences of $w$ wholly contained in $[0, N)$ for all sufficiently large $N$. $\square$

---

## 5. Prior Art, Attribution, and External Inputs Verification Table

| External Input | Exact Statement Used | Where Used | Hypotheses Verified |
| :--- | :--- | :--- | :--- |
| **Wirsing (1967)** (*Acta Math. Acad. Sci. Hungar.* 18, 411–467) / **Selberg–Delange** (`GF-13`) | Real multiplicative $f$ with $|f| \le 1$ and $\sum_p (1 - f(p))/p = \infty$ has mean $0$; sparse-support count $O(X / (\log X)^{1/m})$ when $f(p) = 0$ on Dirichlet density $1/m$. | Thm C1.4(1) ($q = 2$ parity split, via `GF-41` Thm 3.2); Thm C5.1(2) ($m$ even, via `GF-13`) | $f = \mu \cdot \mathbf{1}_{(\cdot, s)=1}$ and $(-1)^\omega$ satisfy $f(p) = -1$ at all large primes; for even $m$, $\chi(p) = -1$ has Dirichlet density $1/m$. ✓ |
| **Halász (1968)** (*Acta Math. Acad. Sci. Hungar.* 19, 365–403) + **Dirichlet's theorem / non-vanishing of $L(1 + is, \psi)$** | Multiplicative $f$ with $|f| \le 1$ and $\inf_s \sum_p (1 - \Re(f(p) p^{-is}))/p = \infty$ has mean $0$; prime reciprocal density in arithmetic progressions. | Thm C1.4(1) (general mod $q$, via `GF-42` Thm B1.5); Thm C5.1(4) (positive density of $\mathcal{E}(t^*)$ and zero density of affine hyperplanes); Thm C5.2(3) ($V_D \bmod k$ equidistribution and split/inert densities) | Verified in every case: $f(p) = 1$ on $\chi(p) = 1$ (density $> 0$, handling $s \ne 0$ via $L(1 + is, \psi) \ne 0$) and $f(p) = \omega_0 \ne 1$ on positive prime density (handling $s = 0$). ✓ |
| **2-D & 3-D Fundamental Lemma of the Combinatorial Sieve** (Halberstam–Richert 1974 Thm 2.5; Iwaniec–Kowalski 2004 §6.4; Tenenbaum 2015 Ch. I.4 Thm 3) | Uniform sieve upper bound $S(\mathcal{A}, \mathcal{P}, z) \le X V(z) (1 + O(e^{-s \log s + O(s)})) + \sum_{q \le D} |R_q|$ for $\kappa \in \{2, 3\}$. | Thm C1.4(2) (mesoscopic $G$-window), Thm C3.1 ($\kappa = 3$), Remark after Thm C4.3 (via `GF-42` Thm B4.1), Thm C5.2(3) ($\kappa = 2$) | $\kappa = 2$ ($p > p_1 \ge 5$, $g(p) = 2/p \le \frac{2}{5}$); $\kappa = 3$ ($p > 5, p \notin \mathcal{Q}$, $g(p) = 3/p \le \frac{3}{7}$); $|R_q| \le \kappa^{\omega(q)}$. ✓ |
| **2-D Selberg Upper-Bound Sieve** (Friedlander–Iwaniec, *Opera de Cribro*, 2010, Thm 7.1; Halberstam–Richert Ch. 6–7) | $S(\mathcal{A}, \mathcal{P}, z) \le X V(z) (\frac{1}{\sigma_2(s)} + o(1)) + \sum_{q < D} \tau_3(q) |R_q|$ with $(v^{-2} \sigma_2(2v))' = -2 v^{-3} \sigma_2(2v - 2)$. | Thm C1.4(2) ($C_{\mathrm{lat}} = 180$), Thm C4.2(1) ($k_0 = 25$) | $g(p) = 2/p$ on $p \in (p_1, z_\ell]$, $p \nmid d$; fixed modulus $Q_0 = O_{p_1, \varepsilon}(1)$ in C4.2 (level $D_i = M_\ell^{1 - \theta_{i+1} - \delta}$, remainder $O_{p_1, \varepsilon}(M_\ell^{1 - \delta}(\log M_\ell)^7)$) and $Q \le M^{o(1)}$ in C1.4(2) ($D = M^{1/2}$, remainder $O(M^{3/4+\varepsilon})$). ✓ |
| **General Linear-Forms Maynard (2015, 2016) / Polymath8b (2014)** (*Ann. Math.* 181; *Compos. Math.* 152, Thm 3.1; *Res. Math. Sci.* 1:12, $M_{50} > 4$ at $\theta = \frac{1}{2} - \varepsilon$) | Every admissible $50$-tuple of affine linear forms $L_i(t) = a_i t + b_i$ ($a_i > 0$, $\gcd(a_i, b_i) = 1$, pairwise linearly independent) contains $\ge 2$ primes for $\gg T / (\log T)^{50}$ values of $t \le T$. | Thm C3.3(2) | Admissibility, $\gcd(a_i, b_i) = 1$, and $a_i b_j \ne a_j b_i$ proved for all $k, p$ and checked for $k = 2, 3$ across $p \le 100$. ✓ |
| **General Linear-Forms Goldston–Graham–Pintz–Yıldırım (2009)** (*Proc. LMS* 98(3)) | Every admissible $3$-tuple of affine linear forms contains $\ge 2$ $E_2$-numbers infinitely often. | Thm C3.3(2) | Admissibility, coprimality, and pairwise linear independence of $\{L_1, L_2, L_3\}$ verified for all $p$. ✓ |
| **Evertse (1984)** (*Compos. Math.* 53, Theorem 1) | For any number field $K$, finite place set $S \supseteq S_\infty$, and $n \ge 2$, the equation $x_1 + \cdots + x_n = 0$ in $\mathcal{O}_{K, S}^\times$ has only finitely many projective solutions with no proper nonempty vanishing subsum. | Thm C5.1(4) (odd $m \ge 5$ barrier only) | Applied strictly to **minimal** (non-degenerate) vanishing subsums in $K = \mathbb{Q}(\zeta_m)$ with $S$ containing $S_\infty$, places above $2$, and valuations of $c_\sigma$; conjugate-pair null directions excluded via $t^*$. ✓ |

*Attribution notes:* The 2-column stationarity framework builds on `GF-41` (`notes/phase25/e4-carry-correlations.md`, Track A) and `CC-49` (`notes/phase17/erdos-borwein-bias.md`). The signed isolated-odd-arrival framework and base-$2^L$ NAF transfer build on `GF-40` and `GF-42` (`notes/phase25/generalized-lambert-and-eplus.md`, Track B); irrationality of $E_+(2^k)$ and $E_{\mathrm{odd}}(2^k)$ is due to P. Borwein (*Proc. Camb. Phil. Soc.* 109 (1991), 253–260; 1992). The cubic twisted convolution builds on `GF-44` (`notes/phase25/naf-geometric-transfer.md`, Track C of Phase 25). Base-2 disjunctivity of $E(2)$ (`BC-37`) at $k = 1$ with exponent constant $70{,}000$ was previously established and **Lean-verified** by Captain Sude (`erdos-borwein-disjunctivity-elementary`, 8 September 2026) via elementary CRT prime-planting with squarefree cofactors and a variable reading position; Theorem C5.3 is an elementary **Paper proof** in the same spirit that handles signed tails via the odd-target guard-bit lemma, unifies $E(2^k), E_{\mathrm{odd}}(2^k), E_+(2^k)$ for all $k \ge 1$ via $3^{W-1}$ planting, and sharpens the paper exponent constant to $37/k$ with zero external inputs.

---

## 6. Exact Reproduction, Certificate Audit, Open Questions, and Proposed Registry Entries

### 6.1 Exact reproduction and assertion audit

Run `python -B scripts/phase26_mesoscopic_carries.py` (standard library only, Python $\ge 3.10$, ~5–6 s on Windows). It exits with code `0` and prints:

```text
ALL CHECKS PASSED: 24497 [exact] + 2828 [encl] = 27325 zero-float theorem checks (plus 3 [finite] prefix measurements).
```

| Script Section | What is Certified (Zero Floats Anywhere in the Script) |
| :--- | :--- |
| **1 (C1.1 & C1.4(2))** | Self-contained $\mu \in [2.076318, 2.076347]$; $\nu \bmod 8$ and $p_J \bmod 8$ at scale $2^{-100}$; 2-column adjacent inequality on all $64$ triples (exact equality on $48/64$); $\mathbb{E}[\Psi_{2,\mathrm{adj}}] \in [0.356817, 0.356889]$; $B_2^{\mathrm{adj}} \le 0.486661$, $D^- \ge 0.013339$; closed-form 1-col + all-order stationarity star-orbit converse ($\ge 0.380742$, with exact mass $= 1$, exact 1-col marginal $= p_J$, and exact window formula checks); C1.4(2) dyadic-shell constant $C_{\mathrm{lat}} \le 180$ (`C_lat_raw <= 175.410682`, multiplied by $1/\sigma_2(10)$ in `main()`). |
| **2 (C1.2)** | Exact $35 \times 35$ `Fraction` Gauss–Jordan inverse for 7-var $r = 3$ countermodel ($\ge 0.378089$, plus exact assertions that all six derived column-count second factorial moments equal $1/4$); binomial identity for $K \in \{1, 3, 5, 7\}$; 2-col Shifted Split-Bonferroni $r = 7$ ($\le 0.369593$); 8-atom denominator-$24$ i.i.d. $r = 2$ countermodel ($\ge 0.400955$); Young-split global i.i.d. $r = 3$ cubic + all $1{,}800$ box points ($\le 0.369859$). |
| **3 (C1.3 & C2)** | $\mathbb{E}_{Q_3}[R_3/8] \in [0.323087, 0.323132]$; all four $\mathbb{Z}/8\mathbb{Z}$ proper-subset obstructions ($> 0.370231$); $\phi_{E(4)}(h)$ enclosures ($h \in \{1,3,5,7,9,11\}$, width $\le 4.0 \times 10^{-6}$); exact Sturm root counts `(0, 0)` for $M = 12$ majorant ($\mathbb{E}[T_{12}] \in [0.497296, 0.497302]$); $23 \times 23$ pure-integer Neumann certificate ($q \le 10^{-9}$) for $M = 11$ countermeasure ($\mu_{11}([1/2, 1)) \ge 0.503909$); $E(2)$ $W = 8$ Bonferroni excess at $r = 46$ ($\le 0.002220 < 0.0028923$). |
| **4 (C3)** | 4-nomial identity on $121$ rational pairs; $A = \sqrt{3}$ SOS identity $(A^2 - 3)^2 (4 A^2 - 3) \ge 0$; CRT admissible $k$-tuple identities, $\gcd(a_i, b_i) = 1$, and pairwise linear independence for $k = 2, 3$ across all $p \le 100$; $526$ concrete $E^*(4)$ collision columns for $n \le 5000$. |
| **5 (C4)** | Certified $1200$-bit prefixes of $E_+(8), E_+(16), E_+(32)$: signed carries $q_n$, $a'_n \in \{-1, 0, 1\}$, Signed Carry Conservation, Exponential Carry-Growth ($t = 0..3$) with exact $2(|q_N| - |q_0|)$ boundary term, transition bound; Euler–Maclaurin $\gamma$, monotone pure-integer $1/\sigma_2(s)$ ($M_{\mathrm{step}} = 256$), dyadic-block smooth tail $< 10^{-10}$, verified non-increasing Rankin weights $R_i$ and exact 10-shell Abel sum certifying $k_0 = 25$ ($k_{\mathrm{req}} \le 24.75247$, gap $\ge 4.36 \times 10^{-5}$); conditional $E_+(8)$ threshold $C < 1.02341$; periodic zero-sum barrier; 2-state carry automaton $m_1^{(2^L)}$ ($L = 1..9$) + Hierholzer Eulerian attaining tours ($L = 2..8$); DP-free $W_+^{\mathrm{maj}} \in [0.936413, 0.936420]$ ($E_+(16)$ base-$4$) and true $W_+ \in [0.908065, 0.908215]$ ($E_+(8)$ base-$256$, sharp vs $L = 7$); $E_+(4)$ deficit $[0.120699, 0.120775]$; $E_{+,\mathrm{odd}}(16)$ base-$64$. |
| **6 (C5)** | Alternating cubic $L_{-,+}(4)$ ($M \in \{31, 43, 109, 127\}$, all $\rho_- < \frac{1}{4}$); standard cubic $L_-(4), L_+(8)$ ($M \in \{7, 9, 13, 19, 37\}$, all $\rho < \frac{9}{32}$); unitary alternating cubic $\rho_-^* = \frac{1}{4}$; universal $k = 1$ cubic barrier ($\ge 0.48715$ std, $\ge 0.45243$ alt); exact $\mathbb{Z}[\zeta_5]$ ring identity on all $1{,}115$ squarefree $n \le 2000$ coprime to $11$, explicit $\Lambda = c - d$ null-direction vs $t^* = 2$ Fibonacci check ($r < 40$), and $\mathbb{Z}[\zeta_m]$ cyclotomic-unit inverses + modulus separation ($m = 5, 7, 9$); $\tau_3 * \chi_D$ ($D \in \{-3, -4, 5, 8\}$) closed form, $C_{\mathrm{pop}}$, and certified $C_{U, D}$ enclosures ($k_+(5) = 3$, $k_+(-3) = 4$, $k_+(8) = 4$, $k_+(-4) = 5$); C5.3 Odd-Target Guard-Bit checks on $(-1, 1)$, $1{,}000$ direct Lambert coefficient & odd-squarefree multiplicativity checks, unified $3^{W-1}$ identity, $6/6$ end-to-end deterministic-trial-division toy CRT plantings on $E(8), E_{\mathrm{odd}}(8), E_+(8)$, and $(2/\ln 2 + 3)^2 \le 34.6379 < 37$; plus $3$ `[finite]` 4-bit word checks on $1200$-bit prefixes of $E(8), E_+(8), E_+(2)$ (finite measurements only). |

### 6.2 Open questions

1. **Unconditional `LLB(c)` for $E^*(4)$ (along a subsequence of scales).** With `PUB(C)` now unconditionally proved (Theorem C3.1), proving $\#\{n \in (x_j/2, x_j] : \omega(n+d) - \omega(n) = 2d\} \ge c x_j / \sqrt{\log\log x_j}$ uniformly for $1 \le d \le \sqrt{\log\log x_j}$ along even a single sequence $x_j \to \infty$ immediately proves $\liminf f_{1, N}(E^*(4); 2) < \frac{1}{2}$ (unconditional simple nonnormality of $E^*(4)$).
2. **Closing $4 \le r_{\min}^{\mathrm{marked}}(E(4); W = 3) \le 7$.** Does the exact minimal 7-variable marked factorial-moment order for $E(4)$ at $W = 3$ equal $4$, $5$, $6$, or $7$? (A general LP over 2-column degree-$4$ or $5$ polynomials with global Young/SOS certification may push $7$ down to $5$ or $4$.)
3. **Bridging $k_0 = 25$ down to $D^+(E_+(8); 2) < 1$ ($k = 3$).** Theorem C4.2 shows that any 2-point lattice pair-correlation constant $C < 1.02341$ settles $D^+(E_+(8); 2) < 1$, while parity-blind sieves hit the $C = 2$ barrier. Can a 2-point correlation bound breaking parity on average over $d \asymp \sqrt{\log\log M}$ (or an asymmetric signed-carry mechanism bypassing $W_+/3$) push $k_0 = 25$ down to $k = 3$?
4. **Base-2 simple normality of $E_+(8)$ and base-2 nonnormality of $E_+(4)$.** Theorem C4.3 settles base-$256$ simple nonnormality of $E_+(8)$ (sharp for symmetric NAF weight) and base-$4$ simple nonnormality of $E_+(16)$, while base-$2$ simple normality of $E_+(8)$ and any base-$2$ nonnormality of $E_+(4)$ (deficit $[0.120699, 0.120775]$) remain open.

### 6.3 Proposed registry entries (for coordinator review; no registry files edited here)

- **`GF-48` (C1–C2):** *Two-column adjacent-pair criterion ($k_{\min} = 2$), factorial-moment hierarchy ($4 \le r_{\min}^{\mathrm{marked}} \le 7$, $r_{\min}^{\mathrm{iid}} = 3$), exact trigonometric threshold ($M_{\min}(E(4)) = 12$), explicit lattice-scale second-moment bound ($C_{\mathrm{lat}} = 180$), and $E(2)$ $W = 8$ order-$46$ Bonferroni reduction.*
- **`GF-49` (C3):** *Unconditional `PUB(C)` for $E^*(4)$ (using only the 3-D Fundamental Lemma, reducing simple nonnormality to `LLB(c)` alone) and unconditional zero-external-input $N \exp(-C L \log L)$ and linear-forms Maynard-sieve $N/(\log N)^{50}$ collision lower bounds.*
- **`GF-50` (C4):** *Signed Carry Conservation, Exponential Carry-Growth Lemma, explicit $k_0 = 25$ for $D^+(E_+(2^k); 2) < 1$ via dyadic-block 10-shell 2-D Selberg sieve ($> 1.2 \times 10^9\times$ sharpening of `GF-42` Thm B1.4), sharp large-window barrier for $E_+(8)$, exact carry-coupled floor $m_1^{(2^L)} = \frac{1}{3} - \frac{2 + (-1/2)^{L-1}}{9L}$, base-$256$ simple nonnormality of $E_+(8)$ (sharp at $L = 8$), and base-$4$ simple nonnormality of $E_+(2^k)$ ($k \ge 4$).*
- **`GF-51` (C5.1–C5.2):** *Complete order-$m$ Dirichlet character Lambert trichotomy (alternating cubic $L_{-,+}(4)$ base-$4$/$8$ simple nonnormality at $k = 2$, universal $k = 1$ cubic barrier, and general odd $m \ge 5$ cyclotomic-unit divergence barrier) and full-density $\tau_3 * \chi_D$ family (simple nonnormality $k \ge 3$ for $D = 5$ and $k \ge 4$ for $D \in \{-3, -4, 8\}$; certified $C_{U, D}$ giving $0 < D^- \le D^+ < 1$ and $\notin K_2$ for $k \ge 3, 4, 4, 5$ and $D^-(2^k) \to 1$).*
- **`GF-52` (C5.3, standalone — zero external inputs):** *Elementary zero-external-input base-2 disjunctivity $\ge N \exp(-(37/k)(\log\log N)^3)$ (wholly inside $[0, N)$) of $E(2^k), E_{\mathrm{odd}}(2^k), E_+(2^k)$ for every $k \ge 1$ (resolving `GF-42` OQ4, establishing disjunctive nonnormality for $k \ge 3$, and proving base-2 disjunctivity of $E_{\mathrm{odd}}(2)$ [`BC-38`] and $E_+(2)$ [`BC-39`] alongside $E(2)$ [`BC-37`]).*
