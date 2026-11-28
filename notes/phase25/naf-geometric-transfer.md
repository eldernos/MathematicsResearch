# Non-Adjacent Signed-Digit Geometric Transfer, Order-4 Nonnormality of $E_+(8)$, Sharp Order-3 Barrier, and Cubic-Character $L_-(4)$ Classification

Phase 25, Addendum Track I. Companion verification and certificate script: [`scripts/phase25_naf_transfer.py`](../../scripts/phase25_naf_transfer.py) (Python 3.10+, standard library only; `python -B scripts/phase25_naf_transfer.py` exits with code `0` in ~29 s, passing **418,091 assertions**: **417,978 `[exact]`**, **104 `[encl]`**, and **9 `[finite]`**).

**Scope, evidence discipline, and benchmark stability disclaimer.**
- Every theorem proved here carries an explicit repository evidence label (`Paper proof`, `Finite certificate`, `External input`, `Conditional`, `Finite measurement`, `Open`) following [`docs/research-objectives.md`](../../docs/research-objectives.md).
- Every numerical constant entering any theorem or bound is a **Finite certificate** computed exclusively with exact Python `int` and `fractions.Fraction` arithmetic (including scale-$2^{-192}$ integer outward rounding). **Zero floating-point arithmetic enters any certificate.**
- The core results of this note — Lemma A.1 and Theorem A.2 (General & Multi-Radix $2^s$ NAF Geometric Transfer), Theorems B.1–B.3 ($E_+(2^k)$ discrepancy bounds, multi-radix extensions, DP-free Lean majorants, and an independent NAF-language re-derivation of the sharp order-3 barrier for $L \le 4$), Lemma C.1 and Theorem C.2 (the elementary $\frac{2}{3}$ twisted convolution lemma, first unconditional nonnormality of $L_-(4)$ at $k = 2$, sharpened $L_-(8)$ bounds, and $L_+(8)$ multi-radix/higher-moduli extensions), and Theorem C.3 ($E_+^*(8)$, $E_{+, \rm odd}(16)$, $F_{2^k, +}(\tau_r)$) — require **ZERO external inputs** (Lemma A.1 invokes the kernel-verified repository lemmas `signedWeight_add_le`/`signedWeight_sub_le` from `NormalityChecker/DigitMassTransfer.lean`, and Lemma C.1 proves the cubic $\frac{2}{3}$ phase factor elementarily without Selberg–Delange or Halász). Several base-2 results for $E_+(8)$, $L_+(8)$, and $L \le 4$ order-normality barriers were proved independently in sibling Phase 25 Track D ([`notes/phase25/digit-complexity-and-lp-witnesses.md`](digit-complexity-and-lp-witnesses.md), Theorems 1.2, 1.7, 2.3, 2.5, 2.6, Lemma 2.4), and all shared results are explicitly cross-referenced below.
- Section 8.2 reports **Finite measurements only** ($N = 4000$ certified bits). Finite digit statistics are never asymptotic evidence and are never used inside any proof.
- The Lean 4 declarations in Section 7 are an uncompiled formalization blueprint for Stage 3, not yet kernel-verified code.
- This note has not received independent human peer review; any subsequent cross-model review is **not** independent human peer review (`AGENTS.md`, `docs/research-objectives.md`).
- **Benchmark stability:** Nothing in this note changes the status of any constant in the fixed 50-constant benchmark roster `BC-01`…`BC-50` ([`docs/benchmarks/classical-constants.toml`](../../docs/benchmarks/classical-constants.toml)). In particular, full normality and simple normality of $E(2)$ (`BC-37`), $E_+(2)$ (`BC-39`), $E(4)$, $E_{\rm odd}(4)$, $E^*(4)$, $E_+(4)$, $E_+^*(4)$, and $L_+(4)$, as well as **base-2 simple normality of $E_+(8)$** and **base-4 simple normality of $L_-(4)$**, remain **Open**.

---

## Results at a Glance

| ID | Main Result | Evidence Label | External Inputs | Standing Objectives |
| --- | --- | --- | --- | --- |
| **I.A1** | **Non-Adjacent Signed-Digit Geometric Transfer:** Elementary equivalence $w_{\rm rec}(|A|) = w_{\min}(A) = w_{\rm NAF}(A)$ (using kernel-verified `signedWeight_add_le`/`signedWeight_sub_le` from `DigitMassTransfer.lean` as a repository input), strict finite-NAF tail bound $|S_j| < \frac{2}{3} 2^{-\ell}$, and universal series transfer proving $D^-(x; 2) \ge \max\{0,\, \sup_{\ell \ge 1}(1 - \frac{4}{3} 2^{-\ell} - \frac{\ell C}{k})\}$ whenever $\log(1+|a(n)|) = o(n)$ and $\limsup \frac{1}{X}\sum_{n \le X} w_\pm(a(n)) \le C$. At $\ell = 2$, $2(\frac{1}{3} - \rho)$ independently recovers Phase 25 Track D Thm. 2.3 (which derived the two-sided exact middle-interval formula of Track D Thm. 1.2 and extended the threshold from $\frac{1}{4}$ to $\frac{1}{3}$); **unique to I.A1** are the automaton-free NAF tail proof and the general-$\ell$ ($\ell \ge 3$) family strictly dominating both `GF-36` Thm. 7.1 and $2(\frac{1}{3}-\rho)$ at every $\rho < \frac{1}{6}$ with $D^- \to 1$ as $\rho \to 0^+$ (§2–3) | Paper proof (+ Lean repo input); Finite certificate (NAF equivalence on $A \in [-8192, 8192]$; 10,656 dyadic cases on $A \in [-512, 512]$ + special values) | **None** | Obj. 2, Obj. 3 |
| **I.A2** | **Multi-Radix $2^s$ Geometric Transfer (unique to Track I):** Pairwise-disjoint $s$-bit block covering yields directly $D^-(x; 2^s) \ge \max\{0,\, \sup_{r \ge 1}(1 - \frac{4}{3} 2^{-sr} - \frac{rsC}{k})\}$ with **zero radix-descent loss** in base $4$ at $\ell^* = 2$, and base-$2^s$ simple nonnormality whenever $sC/k < 1 - 2^{1-s}$ (§2–3) | Paper proof; Finite certificate | **None** | Obj. 2, Obj. 3 |
| **I.B1** | **$E_+(2^k)$ Independent Re-Certification, Multi-Radix Bounds & $k \ge 4$ Simple Nonnormality:** Independent pure `int`/`Fraction` re-certification of Phase 24 `GF-40` Thm. 3.1(a) ($W_+ \in [0.907252, 0.912845]$) and Phase 24 `GF-36` Thm. 7.2 ($W_+ \in [0.908174, 0.908184]$). Independently recovers Phase 25 Track D Thm. 2.5's $D^-(E_+(8); 2) \ge \frac{17431}{300000}$ ($> 247{,}942\times$ `GF-40`) / $\ge \frac{11477}{187500} \approx 0.0612106$ ($> 261{,}201\times$ `GF-40`, $> 2{,}588\times$ Track B) and binary order-4 nonnormality of $E_+(8)$; **unique to I.B1** are the zero-descent-loss base-4 bound $D^-(E_+(8); 4) \ge \frac{11477}{187500}$, **base-4 order-2 nonnormality of $E_+(8)$**, lowering **base-4 and base-8 simple nonnormality of $E_+(2^k)$ to $k \ge 4$**, and sharper $\ell \ge 3$ bounds on $E_+(2^k)$ for $k \ge 6$ (§2–3) | Paper proof; Finite certificate (independent re-certification of `GF-40` Thm. 3.1(a) & `GF-36` Thm. 7.2) | **None** | Obj. 2 (base-4/8 simple & base-4 order-2), Obj. 3 |
| **I.B2** | **DP-Free Lean-Ready Majorants ($< 93/100$; unique to Track I):** Proves no purely multiplicative majorant of $w_\pm(a_+)$ can beat $W_+^{\rm maj} \in [0.936414, 0.936415]$ (independent re-certification of Phase 24 `GF-36` Thm. 7.2, which already clears $\frac{15}{16}$ for order-4 nonnormality), and certifies elementary DP-free squarefull coupled majorants $G_{\{2,3\}} \le 0.929153 < \frac{93}{100}$ (45 primes) and $G_{\{2,3,5\}} \le 0.924468 < \frac{93}{100}$ (12 primes), giving Lean-ready $D^-(E_+(8); 2) \ge \frac{7}{150}$ and order-4 nonnormality with zero DP table (§2–3, §7) | Paper proof; Finite certificate | **None** | Obj. 2, Obj. 3 (formalization readiness) |
| **I.B3** | **Independent NAF-Language Re-Derivation of $m_1, \dots, m_4$ & Order-3 Barrier (complements Phase 25 Track D Thm. 1.7):** Phase 25 Track D Thm. 1.7 already proves $m_L \ge \bar{g}_L = \frac{1}{3}(1 - 4^{-\lfloor L/2 \rfloor})$ for all $L$, attainment for $L \le 10$ (including the identical witness $B_m = (\mathtt{0001})^m(\mathtt{1110})^m$ for $L \in \{2, 3\}$), and the sharp order-3 barrier (§2.6). Theorem B.3 independently re-derives $m_1 = 0$, $m_2 = m_3 = \frac{1}{4}$, $m_4 = \frac{5}{16}$ directly in canonical NAF form ($w_\pm(\lfloor 2^{S_M} x_* \rfloor) = S_M/4$ exactly, $x_4 = \frac{2479}{65535}$) with an exact rational carry-automaton LP confirmation (§2–3) | Paper proof; Finite certificate (exact LP + NAF witnesses) | **None** | Obj. 4 (sharp limitation theorem) |
| **I.C1** | **Elementary Twisted Convolution Lemma & Cubic $L_-(4), L_+(8), L_-(8)$ Classification:** Proves the $\frac{2}{3}$ phase factor for $w_\pm(c_-)$ **with zero external inputs** (eliminating Selberg–Delange / Halász via bounded partial sums of $\chi$; **unique to Track I**). Gives the **first proof of nonnormality ($D^- > 0$) of $L_-(4)$ ($k = 2$, mod $7, 9, 13, 19, 37$)** — unreachable without the $\frac{2}{3}$ factor: $D^-(L_-(4); 2), D^-(L_-(4); 4) \ge 0.162063$ (mod 7, $> 2/15$), $\ge 0.130323$ (mod 9, $> 8/75$), $\ge 0.140457$ (mod 13, $> 8/75$), NOT 4-normal (b=2), NOT 2-normal (b=4) (base-4 simple normality of $L_-(4)$ remains Open). Independently recovers Phase 25 Track D Thm. 2.5 for $L_+(8)$ (mod $7, 9, 13$, adding $W_{\rm true}$, base-4 order-2, base-8 bounds, and mod $19, 37$) and sharpens Track D's Selberg–Delange-free $L_-(8)$ bounds to $D^-(\cdot; 2), D^-(\cdot; 4) \ge 0.330264, 0.309104, 0.315860$ with **zero-external-input base-2 order-2 nonnormality and base-4 / base-8 simple nonnormality** (§2–3) | Paper proof; Finite certificate (re-certifies `GF-36` Prop. 8.1 + new $C_{\rm odd}, W_{\rm true}$, mod $19, 37$) | **None** | Obj. 2, Obj. 3 |
| **I.C2** | **Additional Dense Signed Families Below $1/3$ (unique to Track I):** Exact mean $\frac{3}{4}$ classifies $E_+^*(8) = \sum \mu^2(m)/(8^m+1)$ and $E_{\rm alt,+}^*(8)$ ($D^-(\cdot; 2), D^-(\cdot; 4) \ge \frac{1}{6}$, $D^-(\cdot; 8) \ge \frac{1}{12}$, NOT 4-normal); classifies $E_{+, \rm odd}(16)$ ($k = 4$, $D^- \ge 0.087720$, NOT 4-normal); certifies $F_{2^k, +}(\tau_r)$ at $k \ge 4, 6, 8$ for $r = 4, 8, 16$ (compared with $k \ge 5, 8, 10$ that the `GF-36` Thm. 7.1 criterion $\rho < 1/4$ would require with these majorants) (§2–3) | Paper proof; Finite certificate | **None** | Obj. 2, Obj. 3 |

---

## 1. Exact Definitions and Conventions

Fix an integer radix $b \ge 2$. Every real $x \in \mathbb{R}$ admits a unique canonical base-$b$ expansion not ending in $(b-1)^\infty$,

```math
x = \lfloor x \rfloor + \sum_{j \ge 1} d_j(x; b)\, b^{-j}, \qquad d_j(x; b) \in \{0, 1, \ldots, b - 1\},
```

with fractional part $\{t\} = t - \lfloor t \rfloor \in [0, 1)$. For $N \ge 1$ and any subset $S \subseteq [0, 1)$, write the empirical orbit frequency and extreme interval discrepancy as

```math
F_N(S; x, b) := \frac{1}{N} \#\bigl\{0 \le j < N : \{b^j x\} \in S\bigr\}, \qquad
D_N(x; b) := \sup_{0 \le u < v \le 1} \bigl|F_N([u, v); x, b) - (v - u)\bigr|,
```

with $D^-(x; b) := \liminf_{N \to \infty} D_N(x; b)$ and $D^+(x; b) := \limsup_{N \to \infty} D_N(x; b)$ (matching `radixDiscrepancy` in `NormalityChecker/BinaryDiscrepancy.lean`, l. 11). For $L \ge 1$ and $v \in \{0, \ldots, b^L - 1\}$, the base-$b$ word $v$ of length $L$ occurs at position $j$ iff $\{b^j x\} \in [v b^{-L}, (v+1) b^{-L})$; $x$ is **$L$-normal in base $b$** (`OrderNormal b L x` in `NormalityChecker/HigherOrderTower.lean`) if $\lim_{N \to \infty} F_N([v b^{-L}, (v+1) b^{-L}); x, b) = b^{-L}$ for every $0 \le v < b^L$, **simply normal** if $1$-normal, and **normal** if $L$-normal for every $L \ge 1$ (equivalently $D_N(x; b) \to 0$).

**Signed binary representations and Non-Adjacent Form (NAF).**
For any integer $A \in \mathbb{Z}$, we consider three a priori distinct weight functionals (proven identically equal in Lemma A.1):
1. **Minimal signed-digit weight** $w_{\min}(A)$: the smallest $r \ge 0$ such that $A = \sum_{i=1}^r \varepsilon_i 2^{m_i}$ for some $\varepsilon_i \in \{-1, 1\}$ and $m_i \in \mathbb{Z}_{\ge 0}$ (repeated exponents allowed).
2. **Recursive signed weight** $w_{\rm rec}(n)$ (`signedWeight` in `NormalityChecker/DigitMassTransfer.lean`): defined on $\mathbb{N}$ by
   ```math
   w_{\rm rec}(0) = 0, \qquad w_{\rm rec}(1) = 1, \qquad
   w_{\rm rec}(2m) = w_{\rm rec}(m), \qquad
   w_{\rm rec}(2m + 1) = 1 + \min\bigl(w_{\rm rec}(m),\, w_{\rm rec}(m + 1)\bigr).
   ```
3. **Non-Adjacent Form (NAF) and NAF weight** $w_{\rm NAF}(A)$: a finitely supported sequence $e : \mathbb{Z}_{\ge 0} \to \{-1, 0, 1\}$ is a **NAF representation** of $A$ if $A = \sum_{r \ge 0} e_r 2^r$ and $e_r e_{r+1} = 0$ for every $r \ge 0$. Its weight is $W(e) := \sum_{r \ge 0} |e_r| = \#\{r \ge 0 : e_r \ne 0\}$, and $w_{\rm NAF}(A) := W(\mathrm{naf}(A))$ is the weight of the unique canonical NAF of $A$.

Once Lemma A.1 proves $w_{\rm rec}(|A|) = w_{\min}(A) = w_{\rm NAF}(A)$ for every $A \in \mathbb{Z}$, we denote their common value by $w_\pm(A)$. For any real $x \in \mathbb{R}$, define its **upper prefix NAF density** by

```math
\bar{w}_\pm(x) := \limsup_{M \to \infty} \frac{w_\pm\bigl(\lfloor 2^M x \rfloor\bigr)}{M}.
```

Write $s_2(n)$ for the ordinary binary digit sum (popcount) of $n \ge 0$, $v_2(n) = \max\{e \ge 0 : 2^e \mid n\}$, and $\operatorname{odd}(n) = |n|/2^{v_2(|n|)}$ for $n \ne 0$ ($\operatorname{odd}(0) = 0$).

**Signed Lambert and cubic-character series.**
For $a : \mathbb{N} \to \mathbb{Z}$ with $\sum_{n \ge 1} |a(n)| 2^{-kn} < \infty$, put $F_{2^k}(a) = \sum_{n \ge 1} a(n) 2^{-kn}$. Our main families are:
- Alternating Erdős–Borwein series (`GF-28`, `GF-36`, `GF-40`):
  ```math
  E_+(2^k) = \sum_{m \ge 1} \frac{1}{2^{km} + 1} = \sum_{n \ge 1} a_+(n)\, 2^{-kn}, \qquad
  a_+(n) = \sum_{d \mid n} (-1)^{d - 1} = (1 - v_2(n))\,\tau_{\rm odd}(n).
  ```
- Cubic-character Lambert projections (`GF-31`, `GF-36` §8): for a primitive cubic Dirichlet character $\chi$ modulo $M$ with values in $\{0, 1, \omega, \omega^2\}$ ($\omega = e^{2\pi i/3}$), put $c(n) = (1 * \chi)(n) = x(n) + y(n)\omega \in \mathbb{Z}[\omega]$,
  ```math
  c_+(n) = 2 x(n) - y(n) = 2\Re\bigl(c(n)\bigr), \qquad
  c_-(n) = y(n) = \frac{2}{\sqrt{3}} \Im\bigl(c(n)\bigr), \qquad
  L_\pm(2^k) = \sum_{n \ge 1} c_\pm(n)\, 2^{-kn}.
  ```
  Explicitly, for $M = 7$ we take $\chi(3) = \omega$ ($\chi(a) = 1 \iff a \equiv \pm 1 \pmod 7$); for $M = 9$ we take $\chi(2) = \omega$ ($\chi(a) = 1 \iff a \equiv \pm 1 \pmod 9$); for $M = 13$ we take $\chi(2) = \omega$ ($\chi(a) = 1 \iff a \equiv \pm 1, \pm 5 \pmod{13}$). Replacing $\chi$ by $\bar\chi$ fixes $c_+$ and negates $c_-$, leaving all weights, discrepancies, and normality orders invariant.
- Additional signed Lambert families:
  ```math
  E_+^*(2^k) = \sum_{m \ge 1} \frac{\mu^2(m)}{2^{km} + 1}, \qquad
  E_{\rm alt, +}^*(2^k) = \sum_{m \ge 1} \frac{(-1)^{m-1} \mu^2(m)}{2^{km} + 1}, \qquad
  E_{+, \rm odd}(2^k) = \sum_{m \ge 1\text{ odd}} \frac{1}{2^{km} + 1},
  ```
  and $F_{2^k, +}(\tau_r) = \sum_{m \ge 1} \tau_{r-1}(m)/(2^{km} + 1)$ for $r = 2^t$ ($t \ge 2$).

---

## 2. Theorem Statements

### 2.1 General and Multi-Radix Non-Adjacent Signed-Digit Geometric Transfer

**Lemma A.1 (Exact Equivalence of Minimal Signed Weight, `signedWeight`, and Canonical NAF — Paper proof; zero external inputs).**
Every integer $A \in \mathbb{Z}$ possesses a **unique** NAF representation $\mathrm{naf}(A) = (e_r)_{r \ge 0}$ satisfying $e_r \in \{-1, 0, 1\}$, $e_r e_{r+1} = 0$ for all $r \ge 0$, $\sum_{r \ge 0} e_r 2^r = A$, and $\mathrm{naf}(-A) = -\mathrm{naf}(A)$. Moreover, for every $A \in \mathbb{Z}$,

```math
w_{\rm rec}(|A|) = w_{\min}(A) = w_{\rm NAF}(A) =: w_\pm(A).
```

**Theorem A.2 (General & Multi-Radix $2^s$ NAF Geometric Transfer — Paper proof; zero external inputs).**
1. *(Finite dyadic NAF bound.)* Let $A \in \mathbb{Z}$ (of either sign), $M \ge 1$, $y = A \cdot 2^{-M}$, and $\ell \ge 1$. For every $0 \le j < M$, if the $\ell$ NAF digits $e_{M-j-1}, \ldots, e_{M-j-\ell}$ of $A$ all vanish (setting $e_r := 0$ for $r < 0$), then the fractional remainder $S_j := \sum_{t=1}^{M-j} e_{M-j-t} 2^{-t}$ satisfies the **strict** inequality $|S_j| < \frac{2}{3} 2^{-\ell}$ and consequently $\{2^j y\} \notin \bigl[\frac{2}{3} 2^{-\ell},\, 1 - \frac{2}{3} 2^{-\ell}\bigr]$. Therefore, for every $s \ge 1$, $r \ge 1$ ($\ell = sr$), and $N \ge 1$ with $s N \le M$,
   ```math
   \#\left\{0 \le m < N : \{2^{sm} y\} \in \left[\frac{2}{3} 2^{-sr},\; 1 - \frac{2}{3} 2^{-sr}\right]\right\} \le r\, w_\pm(A).
   ```
2. *(Universal real-number transfer.)* For **every** real $x \in \mathbb{R}$, every $s \ge 1$, $r \ge 1$, $R \ge 2$, and $N \ge 1$, putting $I_{sr, R} := \bigl[\frac{2}{3} 2^{-sr} + 2^{-R},\, 1 - \frac{2}{3} 2^{-sr}\bigr)$ (and symmetrically for $I_{sr, R}^{\rm sym} = \bigl[\frac{2}{3} 2^{-sr} + 2^{-R},\, 1 - \frac{2}{3} 2^{-sr} - 2^{-R}\bigr)$, $R \ge 3$),
   ```math
   F_N\bigl(I_{sr, R}; x, 2^s\bigr) \le \frac{r\, w_\pm\bigl(\lfloor 2^{sN + R} x \rfloor\bigr)}{N}, \qquad
   D_N(x; 2^s) \ge 1 - \frac{4}{3} 2^{-sr} - 2^{-R} - \frac{r\, w_\pm\bigl(\lfloor 2^{sN + R} x \rfloor\bigr)}{N}.
   ```
   Consequently, for every half-open subinterval $[u, v) \subseteq \bigl(\frac{2}{3} 2^{-sr},\, 1 - \frac{2}{3} 2^{-sr}\bigr]$ with $u > \frac{2}{3} 2^{-sr}$,
   ```math
   \limsup_{N \to \infty} F_N\bigl([u, v); x, 2^s\bigr) \le r s\, \bar{w}_\pm(x), \qquad
   D^-(x; 2^s) \ge \max\left\{0,\; \sup_{r \ge 1}\left(1 - \frac{4}{3} 2^{-sr} - r s\, \bar{w}_\pm(x)\right)\right\}.
   ```
3. *(Infinite signed series transfer.)* Let $k \ge 1$ and $a : \mathbb{N} \to \mathbb{Z}$ satisfy $\log(1 + |a(n)|) = o(n)$ (or more generally $\log(1 + \Theta_Q) = o(Q)$, hypothesis **(H)** of `GF-36`) and $\limsup_{X \to \infty} \frac{1}{X} \sum_{n=1}^X w_\pm(a(n)) \le C$. Then $x = \sum_{n \ge 1} a(n) 2^{-kn}$ converges absolutely and satisfies $\bar{w}_\pm(x) \le C/k$. Hence, in base $2$ ($s = 1$),
   ```math
   D^-(x; 2) \ge \max\left\{0,\; \sup_{\ell \ge 1}\left(1 - \frac{4}{3} 2^{-\ell} - \frac{\ell C}{k}\right)\right\},
   ```
   and in every base $2^s$ ($s \ge 1$),
   ```math
   D^-(x; 2^s) \ge \max\left\{0,\; \sup_{r \ge 1}\left(1 - \frac{4}{3} 2^{-sr} - \frac{r s C}{k}\right)\right\}.
   ```
4. *(Unimodality, $\ell$-comparison, and dominance over `GF-36`.)* Put $\rho := C/k \ge 0$ and $g_\ell(\rho) := 1 - \frac{4}{3} 2^{-\ell} - \ell \rho$. Then:
   - $g_2(\rho) = \frac{2}{3} - 2\rho = 2\bigl(\frac{1}{3} - \rho\bigr) = 2 g_1(\rho)$, strictly dominating $\ell = 1$ for every $\rho < \frac{1}{3}$;
   - $g_{\ell+1}(\rho) - g_\ell(\rho) = \frac{2}{3} 2^{-\ell} - \rho$, so $g_\ell(\rho)$ is unimodal in $\ell$ with exact maximizer $\ell^* = 2$ on $[\frac{1}{6}, \frac{1}{3})$, $\ell^* = 3$ ($g_3 = \frac{5}{6} - 3\rho$) on $[\frac{1}{12}, \frac{1}{6})$, and in general $\ell^* = m$ on $[\frac{2}{3} 2^{-m}, \frac{2}{3} 2^{-(m-1)})$ ($m \ge 2$);
   - As $\rho \to 0^+$, $1 - \sup_{\ell \ge 1} g_\ell(\rho) \le \rho \log_2\!\bigl(\frac{16}{3\rho}\bigr) \to 0$;
   - For every $m \ge 2$ and $\rho \in (0, \frac{1}{3})$, $g_{2(m-1)}(\rho)$ strictly exceeds the `GF-36` Theorem 7.1 window-$m$ bound $1 - 2^{1-m} - 2(m-1)\rho$ at the identical slope.

   *(Relation to Phase 25 Track D: At $s = 1, \ell = 2$, the bound $D^-(x; 2) \ge 2(\frac{1}{3} - \rho)$ independently recovers [Phase 25 Track D](digit-complexity-and-lp-witnesses.md) Theorem 2.3 and Lemma 2.4, where Track D Theorem 1.2 proved the two-sided exact middle-interval formula $-2 \le 2\sigma_1(x; N) - K_{[1/6, 5/6)}(x; N) \le 1$ and extended the threshold from $\frac{1}{4}$ to $\frac{1}{3}$. Theorem A.2 contributes an automaton-free finite-NAF geometric tail proof, the general-$\ell$ ($\ell \ge 3$) bounds strictly beating $2(\frac{1}{3} - \rho)$ for $\rho < \frac{1}{6}$, and direct multi-radix $2^s$ transfer for all $s \ge 2$.)*

### 2.2 Applications to $E_+(2^k)$ ($k \ge 3$), Multi-Radix Bounds, DP-Free Majorants, and Independent NAF Derivation of the Order-3 Barrier

**Theorem B.1 ($E_+(2^k)$ Independent Re-Certification, Quantitative Nonnormality & Multi-Radix Extensions — Paper proof + Finite certificate; zero external inputs).**
The limiting signed-weight mean $W_+ = \lim_{X \to \infty} \frac{1}{X} \sum_{n=1}^X w_\pm(a_+(n))$ satisfies two independent pure-`int`/`Fraction` re-certifications of Phase 24 enclosures:
- *(Independent re-certification of Phase 24 `GF-40` Thm. 3.1(a), [`classical-constants-and-joint-numerators.md`](../phase24/classical-constants-and-joint-numerators.md), pure `Fraction`, $P = 600$)* $W_+ \in [0.907252,\, 0.912845]$;
- *(Independent re-certification of Phase 24 `GF-36` Thm. 7.2, [`dense-digit-mass-and-lambert.md`](../phase24/dense-digit-mass-and-lambert.md), scale-$2^{-192}$ `int` DP, $Y = 200{,}000, y = 20{,}000$)* $W_+ \in [0.908174,\, 0.908184]$.

Consequently:
1. *(Quantitative discrepancy bounds for $E_+(8)$; base-2 bounds independently recover Phase 25 Track D Thm. 2.5, with zero-descent-loss base-4 extension.)*
   - From $W_+ \le \frac{912845}{10^6}$: $D^-(E_+(8); 2),\; D^-(E_+(8); 4) \ge \frac{17431}{300000} = 0.0581033\ldots$ ($> 247{,}942\times$ `GF-40`'s exact rational $A_{16}$ bound $2.3434\ldots \times 10^{-7}$; base-2 bound first obtained in Phase 25 Track D Thm. 2.5).
   - From $W_+ \le \frac{908184}{10^6}$: $D^-(E_+(8); 2),\; D^-(E_+(8); 4) \ge \frac{11477}{187500} = 0.0612106\ldots$ (and $\ge 0.0612111$ from the unrounded upper endpoint; $> 261{,}201\times$ `GF-40` and $> 2{,}588\times$ Phase 25 Track B's 7-state asymmetric transducer bound $2.3643 \times 10^{-5}$; base-2 bound $\ge 0.061210$ first obtained in Phase 25 Track D Thm. 2.5), and by radix descent $D^-(E_+(8); 8) \ge \frac{3}{7} \cdot \frac{11477}{187500} = \frac{11477}{437500} \ge 0.026233$.
2. *(Binary order-4 and base-4 order-2 nonnormality of $E_+(8)$.)* Applying Theorem A.2 at $\ell = 2$ to the exact union of $10$ binary length-$4$ cylinders (equivalently $10$ base-$4$ length-$2$ cylinders) $\bigl[\frac{3}{16}, \frac{13}{16}\bigr) \subset \bigl(\frac{1}{6}, \frac{5}{6}\bigr)$ gives
   ```math
   \limsup_{N \to \infty} F_N\!\left(\left[\frac{3}{16}, \frac{13}{16}\right); E_+(8), 2\right) \le \frac{2 W_+}{3} \le 0.605456 < 0.625 = \frac{10}{16},
   ```
   and identically for $F_N([\frac{3}{16}, \frac{13}{16}); E_+(8), 4)$. Hence $E_+(8)$ is **NOT $4$-normal in base $2$** (`¬ OrderNormal 2 4 (E_+(8))`, independently recovering Phase 25 Track D Thm. 2.5) and **NOT $2$-normal in base $4$** (`¬ OrderNormal 4 2 (E_+(8))`, new via multi-radix Theorem A.2).
3. *(Sharpened $E_+(2^k)$ tower for $k \ge 4$; new base-4/base-8 thresholds.)* For every $k \ge 4$, $2 W_+ / k \le 0.454092 < \frac{1}{2}$ and $3 W_+ / k \le 0.681138 < \frac{3}{4}$, so **$E_+(2^k)$ is NOT $2$-normal in base $2$ and IS simply nonnormal in BOTH base $4$ and base $8$** (lowering Track B's thresholds from $k \ge 8$ in base $4$ and $k \ge 5$ in base $8$ to $k \ge 4$), and is simply nonnormal in its construction radix $2^k$ for every $k \ge 5$ directly via Theorem A.2 ($W_+ < 1 - 2^{1-k}$). Base-2 simple normality of $E_+(8)$ remains **Open**.

**Theorem B.2 (Elementary DP-Free Squarefull Majorants for Lean 4 — Paper proof + Finite certificate; zero external inputs).**
1. *(Sharp floor for purely multiplicative majorants.)* Every multiplicative function $G \ge 0$ satisfying $w_\pm(a_+(n)) \le G(n)$ for all $n \ge 1$ obeys $G(n) \ge G_0(n) := w_\pm(|1 - v_2(n)|) \prod_{p > 2} w_\pm(v_p(n) + 1)$, whose exact mean is $W_+^{\rm maj} \in [0.936414,\, 0.936415]$ (an independent re-certification of Phase 24 `GF-36` Thm. 7.2). Thus no purely multiplicative majorant achieves mean $< \frac{93}{100}$; nevertheless, $W_+^{\rm maj} < \frac{15}{16} = 0.9375$ ALREADY certifies $D^-(E_+(8); 2) \ge \frac{1}{24}$ and binary order-4 nonnormality of $E_+(8)$ without any DP.
2. *(DP-free $\{2, 3\}$- and $\{2, 3, 5\}$-coupled squarefull majorants $< \frac{93}{100}$.)* Define the elementary non-DP squarefull-kernel majorants
   ```math
   G_{\{2,3\}}(2^{e_2} 3^{e_3} m) := w_\pm\bigl(|1 - e_2|(e_3 + 1)\bigr) \prod_{p \ge 5} s_2(v_p(m) + 1) \qquad (\gcd(m, 6) = 1),
   ```
   ```math
   G_{\{2,3,5\}}(2^{e_2} 3^{e_3} 5^{e_5} m') := w_\pm\bigl(|1 - e_2|(e_3 + 1)(e_5 + 1)\bigr) \prod_{p \ge 7} s_2(v_p(m') + 1) \qquad (\gcd(m', 30) = 1).
   ```
   Both dominate $w_\pm(a_+(n))$ pointwise for all $n \ge 1$, have absolutely summable Möbius kernels $\sum_n |(G * \mu)(n)|/n < \infty$ (falling directly under `tendsto_average_of_summable_conv_mobius` in `DigitMassTransfer.lean`, which requires no multiplicativity), reuse `DigitMassTransfer.lean`'s exact local bound $B(p) = (1 - p^{-2})^{-1} - p^{-3} - 2p^{-7}$, and satisfy the certified exact rational upper bounds:
   - $M_{\{2,3\}} \le 0.929153 < \frac{93}{100}$ (**45 primes** $5 \le p \le 211$ with elementary $\pm 1 \pmod 6$ tail; or $0.929681 < \frac{93}{100}$ with 107 primes $p < 601$ and the trivial `sum_Ico_inv_sq_le` tail);
   - $M_{\{2,3,5\}} \le 0.924468 < \frac{93}{100}$ (**12 primes** $7 \le p \le 47$ with $\pm 1 \pmod 6$ tail; or $0.928395 < \frac{93}{100}$ with **26 primes** $7 \le p \le 109$ and the trivial tail).

   Consequently, without any DP table, $C = \frac{93}{100}$ gives
   ```math
   D^-(E_+(8); 2),\; D^-(E_+(8); 4) \ge \frac{2}{3} - \frac{2}{3} \cdot \frac{93}{100} = \frac{7}{150}, \qquad
   \limsup_{N \to \infty} F_N\!\left(\left[\frac{3}{16}, \frac{13}{16}\right); E_+(8), 2\right) \le \frac{62}{100} < \frac{5}{8},
   ```
   certifying BOTH $D^-(E_+(8); 2) \ge \frac{7}{150}$ AND binary order-4 (and base-4 order-2) nonnormality of $E_+(8)$ in Lean-ready elementary form.

**Theorem B.3 (Independent NAF Re-Derivation of $m_1, \dots, m_4$ and the Sharp Order-3 Barrier — complements Phase 25 Track D Thm. 1.7; Paper proof + Finite certificate; Objective 4; zero external inputs).**
*(Attribution: [Phase 25 Track D](digit-complexity-and-lp-witnesses.md) Theorem 1.7 already proves the general lower bound $\bar{g}_L = \frac{1}{3}(1 - 4^{-\lfloor L/2 \rfloor}) \le \liminf \sigma_1/N$ for every $L$-normal real and every $L \ge 1$, certifies attainment for $L \le 10$ — including the identical block witness $B_m = (\mathtt{0001})^m(\mathtt{1110})^m$ for $L \in \{2, 3\}$ — and states the resulting order-3 limitation in Track D §2.6. Because $\sigma_1(x; N)$ and $w_\pm(\lfloor 2^N x \rfloor)$ differ by $O(1)$, $m_L = \bar{g}_L$ for $L \le 10$. Below we record an independent closed-form canonical NAF derivation for $L \le 4$ together with exact carry-automaton LP confirmation.)*

For each integer $L \ge 1$, let $m_L := \inf\{\bar{w}_\pm(x) : x \in \mathbb{R} \text{ is } L\text{-normal in base } 2\}$. Then:

```math
m_1 = 0, \qquad m_2 = \frac{1}{4}, \qquad m_3 = \frac{1}{4}, \qquad m_4 = \frac{5}{16}.
```

Specifically:
1. *(Lower bounds and LP relaxation.)* Every $2$-normal (hence every $3$-normal) real satisfies $\bar{w}_\pm(x) \ge \frac{1}{4}$ (from Theorem A.2 at $\ell = 2$ on $[\frac{1}{4}, \frac{3}{4})$); every $4$-normal real satisfies $\bar{w}_\pm(x) \ge \frac{5}{16}$ (from Theorem A.2 at $\ell = 2$ on $[\frac{3}{16}, \frac{13}{16})$). Moreover, because canonical NAF conversion operates with carries in $\{-1, 0\} \subset \{-1, 0, 1\}$ and every subsequential weak limit of the empirical transition measures along prefixes of an $L$-normal real is a shift-invariant flow on the carry-augmented de Bruijn graph with uniform $L$-word marginals, minimizing edge cost over such flows yields a valid lower relaxation $\mathrm{LP}^*_L \le \liminf_{N \to \infty} w_\pm(\lfloor 2^N x \rfloor)/N$; exact rational LP minimization confirms $\mathrm{LP}^*_L = 0, \frac{1}{4}, \frac{1}{4}, \frac{5}{16}$ for $L = 1, 2, 3, 4$.
2. *(Explicit irrational $3$-normal witness attaining $m_3 = \frac{1}{4}$; same block family as Track D Thm. 1.7(4).)* Let $x_* \in (0, 1)$ have binary expansion formed by concatenating the blocks $B_m := (\mathtt{0001})^m (\mathtt{1110})^m$ of length $8m$ for $m = 1, 2, 3, \ldots$, with cumulative lengths $S_M = \sum_{m=1}^M 8m = 4 M(M+1)$. Then $x_*$ is irrational, **$3$-normal in base $2$** ($f_N(w; x_*, 2) = \frac{1}{8} + O(N^{-1/2})$ for every $w \in \{0, 1\}^3$), and satisfies the **exact zero-overhead canonical NAF identity**
   ```math
   w_\pm\bigl(\lfloor 2^{S_M} x_* \rfloor\bigr) = \frac{S_M}{4} = M(M + 1) \quad (\forall M \ge 1), \qquad
   \lim_{N \to \infty} \frac{w_\pm(\lfloor 2^N x_* \rfloor)}{N} = \frac{1}{4}.
   ```
3. *(Explicit $4$-normal witness attaining $m_4 = \frac{5}{16}$.)* The order-$4$ de Bruijn rational $x_4 := \frac{2479}{65535} = 0.\overline{\mathtt{0000100110101111}}_2$ (where $2479 = 2^{11} + 2^9 - 2^6 - 2^4 - 1$) is **$4$-normal in base $2$** and satisfies $w_\pm(\lfloor 2^{16m} x_4 \rfloor) = 5m$ for all $m \ge 1$, hence $\lim_{N \to \infty} w_\pm(\lfloor 2^N x_4 \rfloor)/N = \frac{5}{16}$ (and adding $\sum_{r \ge 1} 2^{-2^{r^2}}$ yields an irrational $4$-normal witness with the same limit).
4. *(Sharp Order-3 Limitation Corollary; matching Track D §2.6.)* **No method using only an upper bound $\bar{w}_\pm(x) \le \alpha$ with $\alpha \ge \frac{1}{4}$** — regardless of dyadic interval, transducer, or linear functional on length-$3$ word frequencies — **can prove that $x$ is not $3$-normal in base $2$.** Because $W_+/3 \approx 0.302728 > \frac{1}{4}$, Order $4$ is the sharp, unimprovable limit of NAF-weight transfer for $E_+(8)$ (and likewise for $L_+(8)$, $L_-(4)$ mod $7, 9, 13, 19, 37$, and $E_+^*(8)$).

### 2.3 Cubic-Character Classifications ($L_-(4)$, $L_+(8)$, $L_-(8)$) and Additional Dense Signed Families

**Lemma C.1 (Elementary Twisted Squarefull Convolution — Paper proof; zero external inputs).**
Let $\chi$ be any nonprincipal Dirichlet character modulo $M \ge 2$, and set $\chi^\circ(n) := \chi\bigl(n / \prod_{p \mid M} p^{v_p(n)}\bigr)$ (a completely multiplicative function). Let $G : \mathbb{N} \to \mathbb{C}$ have Möbius convolution $H = G * \mu$ satisfying $\sum_{d \ge 1} |H(d)| d^{-\sigma} < \infty$ for some $\sigma \in (0, 1)$. Then

```math
\left|\frac{1}{X} \sum_{n=1}^{X} \chi^\circ(n)\, G(n)\right|
  \le M \Bigl(\sum_{d \ge 1} \frac{|H(d)|}{d^\sigma}\Bigr) X^{\sigma - 1} (\log_2 X + 1)^{\omega(M)}
  \longrightarrow 0 \qquad (X \to \infty).
```

Consequently, for any primitive cubic character $\chi \bmod M$ with multiplicative NAF majorant $G_\chi$ (`GF-36` Prop. 8.1, mean $W_\chi$), odd-part majorant $U_\chi(n) = \mathbf{1}_{c(n) \ne 0} \operatorname{odd}(A(n))$ (mean $C_{\rm odd}$), and exact true mean $W_{\chi, \rm true} = \lim_{X \to \infty} \frac{1}{X} \sum_{n \le X} w_\pm(c_+(n))$, we have **with zero external inputs** (bypassing Selberg–Delange and Halász):

```math
\lim_{X \to \infty} \frac{1}{X} \sum_{n=1}^{X} w_\pm(c_-(n)) = \frac{2}{3} W_{\chi, \rm true} \le \frac{2}{3} W_\chi \le \frac{2}{3} C_{\rm odd}.
```

**Theorem C.2 (Cubic-Character Classifications: First Proof of Nonnormality for $L_-(4)$, Sharpened Zero-External-Input $L_-(8)$, and Multi-Radix $L_+(8)$ — Paper proof + Finite certificate; zero external inputs).**
For the primitive cubic Dirichlet characters modulo $M \in \{7, 9, 13\}$ (with $\delta = \prod_{\chi(p) \in \{\omega, \bar\omega\}} (1 - (p^2+p+1)^{-1})$):
1. *(Certified enclosures; $W_\chi$ independently re-certifies Phase 24 `GF-36` Prop. 8.1.)* Pure `int`/`Fraction` arithmetic certifies:
   - $M = 7$: $C_{\rm odd} \in [0.763564, 0.763566] < \frac{4}{5}$, $W_\chi \in [0.756903, 0.756905]$, $W_{\chi, \rm true} \in [0.756860, 0.756872]$;
   - $M = 9$: $C_{\rm odd} \in [0.811036, 0.811039] < \frac{21}{25}$, $W_\chi \in [0.804514, 0.804516]$, $W_{\chi, \rm true} \in [0.804466, 0.804479]$;
   - $M = 13$: $C_{\rm odd} \in [0.819446, 0.819449] < \frac{21}{25}$, $W_\chi \in [0.789313, 0.789314]$, $W_{\chi, \rm true} \in [0.789150, 0.789162]$.
   *(All 6-digit discrepancy lower bounds in parts (2)–(5) below are computed from the unrounded certified upper endpoints and rounded down.)*
2. **($L_-(4)$ at $k = 2$ — First proof of nonnormality $D^- > 0$; unique to Track I.)** By Lemma C.1 and Theorem A.2 (optimal $\ell^* = 2$ in base $2$, $r^* = 1$ in base $4$, effective NAF density $\rho = \frac{2}{3} W_\chi / 2 = W_\chi / 3$; without Lemma C.1's $\frac{2}{3}$ factor, Track D's route gives $\rho = W_\chi / 2 > \frac{1}{3}$ and cannot reach $k = 2$):
   - Already from the `GF-31` odd-part bounds $C_{\rm odd} < \frac{4}{5}$ ($M = 7$) and $C_{\rm odd} < \frac{21}{25}$ ($M = 9, 13$),
     ```math
     D^-(L_-(4); 2),\; D^-(L_-(4); 4) \ge \frac{2}{15} \quad (M = 7), \qquad
     D^-(L_-(4); 2),\; D^-(L_-(4); 4) \ge \frac{8}{75} \quad (M = 9, 13).
     ```
   - Using the unrounded certified upper endpoints of $W_\chi$ (and $W_{\chi, \rm true}$),
     ```math
     D^-(L_-(4); 2),\; D^-(L_-(4); 4) \ge
     \begin{cases}
       0.162063 \;\; (0.162085 \text{ via } W_{\rm true}) & M = 7, \\
       0.130323 \;\; (0.130347 \text{ via } W_{\rm true}) & M = 9, \\
       0.140457 \;\; (0.140559 \text{ via } W_{\rm true}) & M = 13,
     \end{cases}
     ```
     and uniformly taking $\max(\text{direct base-}8,\, \text{radix descent})$ gives $D^-(L_-(4); 8) \ge 0.076428$ ($0.076461$ via $W_{\rm true}$) for $M = 7$, $\ge 0.055852$ ($0.055863$ via $W_{\rm true}$) for $M = 9$, and $\ge 0.060196$ ($0.060239$ via $W_{\rm true}$) for $M = 13$.
   - Hence **$L_-(4)$ (mod $7, 9, 13$) is nonnormal in base $2$, base $4$, and every base $2^j$ ($j \ge 1$)**, and specifically is **NOT $4$-normal in base $2$** and **NOT $2$-normal in base $4$** (with Order $4$ sharp for NAF weight by Theorem B.3; base-4 simple normality of $L_-(4)$, listed as open in `GF-31`, remains **Open** — see OQ2).
3. **($L_+(8)$ at $k = 3$ — Independently recovers Phase 25 Track D Thm. 2.5 + base-4 / base-8 / $W_{\rm true}$ extensions.)** Because $L_+(8)$ has the identical effective NAF density $\rho = W_\chi / 3$, it satisfies the **exact same** base-$2$, base-$4$, and base-$8$ lower discrepancy bounds ($D^-(\cdot; 2), D^-(\cdot; 4) \ge 0.162063, 0.130323, 0.140457$ via $W_\chi$ and $0.162085, 0.130347, 0.140559$ via $W_{\rm true}$; $D^-(\cdot; 8) \ge 0.076428, 0.055852, 0.060196$ via $W_\chi$ and $0.076461, 0.055863, 0.060239$ via $W_{\rm true}$), is **NOT $4$-normal in base $2$** (first proved for $M = 7, 9, 13$ in Phase 25 Track D Thm. 2.5 with $D^-(\cdot; 2) \ge 0.1620, 0.1303, 0.1404$), and is **NOT $2$-normal in base $4$** (new via multi-radix Theorem A.2).
4. **($L_-(8)$ at $k = 3$ — Sharpened via Lemma C.1 with zero external inputs.)** Phase 25 Track D Thm. 2.5 already gave a Selberg–Delange-free proof of base-2 nonnormality ($D^- \ge 0.1620, 0.1303, 0.1404$) and binary order-4 nonnormality of $L_-(8)$. Combining Lemma C.1's elementary $\frac{2}{3}$ factor with Theorem A.2 lowers the density to $\rho = \frac{2}{9} W_\chi < \frac{1}{4}$ (optimal $\ell^* = 2$ in base $2$, $r^* = 1$ in bases $4, 8$) and yields (still with zero external inputs):
   - Mod $7$: $D^-(\cdot; 2), D^-(\cdot; 4) \ge 0.330264$ ($0.330279$ via $W_{\rm true}$), $D^-(\cdot; 8) \ge 0.328730$ ($0.328752$ via $W_{\rm true}$);
   - Mod $9$: $D^-(\cdot; 2), D^-(\cdot; 4) \ge 0.309104$ ($0.309120$ via $W_{\rm true}$), $D^-(\cdot; 8) \ge 0.296989$ ($0.297014$ via $W_{\rm true}$);
   - Mod $13$: $D^-(\cdot; 2), D^-(\cdot; 4) \ge 0.315860$ ($0.315928$ via $W_{\rm true}$), $D^-(\cdot; 8) \ge 0.307124$ ($0.307225$ via $W_{\rm true}$).
   - For all three moduli, **$L_-(8)$ is NOT $2$-normal in base $2$** and **IS simply nonnormal in base $4$ and base $8$** (recovering `GF-31` Thm. 4A's base-8 simple nonnormality with zero external inputs and adding base-4 simple nonnormality).
5. *(Higher cubic prime moduli; unique to Track I.)* The identical zero-external-input certificate establishes nonnormality ($D^- > 0$, **NOT $4$-normal in base $2$**, **NOT $2$-normal in base $4$**) for **$L_-(4)$ and $L_+(8)$ modulo $19$** ($W_{\chi_{19}} \in [0.774595, 0.774599] \implies D^-(\cdot; 2), D^-(\cdot; 4) \ge 0.150267$, $D^-(\cdot; 8) \ge 0.064400$) and **modulo $37$** ($W_{\chi_{37}} \in [0.751168, 0.751172] \implies D^-(\cdot; 2), D^-(\cdot; 4) \ge 0.165885$, $D^-(\cdot; 8) \ge 0.082161$), while moduli $31$ ($W_{\chi_{31}} \in [1.019735, 1.019740]$) and $43$ ($W_{\chi_{43}} \in [1.029814, 1.029819]$) exceed $W_\chi = 1$ and leave $L_-(4), L_+(8)$ Open. Likewise, $L_+(4)$ (mod $7, 9, 13$) has $W_{\chi, \rm true}/2 > \frac{1}{3}$ and remains **Open**.

**Theorem C.3 (Additional Dense Signed Lambert Families Below $C/k < 1/3$ — unique to Track I; Paper proof + Finite certificate; zero external inputs).**
1. *(Signed unitary Lambert series $E_+^*(2^k)$ and $E_{\rm alt, +}^*(2^k)$ — exact rational mean $\frac{3}{4}$, zero DP.)* Write $n = 2^e m$ ($m$ odd). Then
   ```math
   a_+^*(n) = \sum_{d \mid n} \mu^2(d)(-1)^{n/d - 1} =
   \begin{cases} 2^{\omega(m)} & e = 0, \\ 0 & e = 1, \\ -2^{\omega(m)+1} & e \ge 2, \end{cases}
   \qquad
   a_{\rm alt, +}^*(n) = \sum_{d \mid n} (-1)^{d-1}\mu^2(d)(-1)^{n/d - 1} =
   \begin{cases} 2^{\omega(m)} & e = 0, \\ -2^{\omega(m)+1} & e = 1, \\ 0 & e \ge 2. \end{cases}
   ```
   Both satisfy $\lim_{X \to \infty} \frac{1}{X} \sum_{n=1}^X w_\pm(a(n)) = \frac{3}{4}$ **exactly**. At $k = 3$ (where the `GF-36` Thm. 7.1 criterion $2W/k < \frac{1}{2}$ fails since $2(\frac{3}{4})/3 = \frac{1}{2}$), Theorem A.2 yields **$D^-(E_+^*(8); 2), D^-(E_+^*(8); 4) \ge \frac{1}{6}$**, **$D^-(E_+^*(8); 8) \ge \frac{1}{12}$**, binary order-4 and base-4 order-2 nonnormality (and identically for $E_{\rm alt, +}^*(8)$); at $k = 4$, $D^-(E_+^*(16); 2) \ge \frac{7}{24}$, NOT $2$-normal in base $2$, simply nonnormal in base $4$ and base $8$.
2. *(Signed odd-divisor series $E_{+, \rm odd}(2^k)$ at $k = 4$.)* We have $E_{+, \rm odd}(2^k) = \sum_{n \ge 1} (-1)^{n-1} \tau_{\rm odd}(n) 2^{-kn}$, with certified $W_{\rm odd}^{\rm maj} \in [1.176328, 1.176330]$ and $\mu_{\rm NAF}(\tau_{\rm odd}) \in [1.157843, 1.157894]$. Whereas the `GF-36` Thm. 7.1 criterion ($\rho < \frac{1}{4}$) with these majorants would require $k \ge 5$ (`GF-36` Thm. 6.1 treated only the unsigned $E_{\rm odd}$ series), Theorem A.2 certifies **$E_{+, \rm odd}(16)$ ($k = 4$)**: $D^-(E_{+, \rm odd}(16); 2), D^-(E_{+, \rm odd}(16); 4) \ge 0.078501$ (majorant) / $0.087720$ (true), **NOT $4$-normal in base $2$** and **NOT $2$-normal in base $4$**.
3. *(Signed higher-divisor series $F_{2^k, +}(\tau_r) = \sum_{m \ge 1} \tau_{r-1}(m)/(2^{km}+1)$, $r = 4, 8, 16$.)* The coefficient is multiplicative with $a(p^e) = \binom{e+r-1}{r-1}$ for odd $p$ and $a(2^e) = \binom{e+r-2}{r-2} - \mathbf{1}_{e \ge 1}\binom{e+r-2}{r-1}$. Certified majorants $W_{\tau_4, +}^{\rm maj} \in [1.236184, 1.236188]$, $W_{\tau_8, +}^{\rm maj} \in [1.958856, 1.958861]$, and $W_{\tau_{16}, +}^{\rm maj} \in [2.364703, 2.364709]$ classify **$k \ge 4$** ($F_{16, +}(\tau_4)$: $D^- \ge 0.048572$, NOT 4-normal), **$k \ge 6$** ($F_{64, +}(\tau_8)$: $D^- \ge 0.013713$, NOT 6-normal), and **$k \ge 8$** ($F_{256, +}(\tau_{16})$: $D^- \ge 0.075489$, NOT 4-normal), improving on the thresholds $k \ge 5, 8, 10$ that the `GF-36` Thm. 7.1 criterion ($\rho < \frac{1}{4}$) would require with these majorants (`GF-36` Thm. 6.2 treated only the unsigned $\tau_r$ series).

---

## 3. Complete Proofs

### 3.1 Proof of Lemma A.1 (NAF Existence, Uniqueness, and Exact Equivalence with `signedWeight`)

**Step 1 (Existence, termination, and symmetry of canonical NAF).** Define $\mathrm{naf} : \mathbb{Z} \to \mathrm{List}\{-1, 0, 1\}$ recursively by: $\mathrm{naf}(0) = []$; if $A \ne 0$ is even, $\mathrm{naf}(A) = 0 :: \mathrm{naf}(A/2)$; if $A$ is odd, let $\varepsilon = +1$ if $A \equiv 1 \pmod 4$ and $\varepsilon = -1$ if $A \equiv 3 \pmod 4$, and set $\mathrm{naf}(A) = \varepsilon :: \mathrm{naf}((A - \varepsilon)/2)$.
- *Termination:* If $A \ne 0$ is even, $|A/2| < |A|$. If $|A| = 1$, $A = \varepsilon$ so $(A - \varepsilon)/2 = 0 < 1$. If $|A| \ge 3$ is odd, $|(A - \varepsilon)/2| \le (|A| + 1)/2 < |A|$. Thus strong induction on $|A|$ proves termination.
- *Representation:* $2 \cdot \frac{A - \varepsilon}{2} + \varepsilon = A$, so inductively $\sum_{r \ge 0} \mathrm{naf}(A)_r 2^r = A$.
- *Non-adjacency:* Whenever $A$ is odd, $A \equiv \varepsilon \pmod 4$ implies $4 \mid (A - \varepsilon)$, so $(A - \varepsilon)/2$ is **even**. Therefore $\mathrm{naf}((A - \varepsilon)/2)$ either is empty or begins with $0$, ensuring $\mathrm{naf}(A)_0 \cdot \mathrm{naf}(A)_1 = 0$; induction gives $e_r e_{r+1} = 0$ for all $r \ge 0$.
- *Symmetry:* Replacing $A$ by $-A$ flips $1 \pmod 4 \leftrightarrow 3 \pmod 4$, hence flips $\varepsilon \mapsto -\varepsilon$ and $(A - \varepsilon)/2 \mapsto -(A - \varepsilon)/2$. Inductively $\mathrm{naf}(-A) = -\mathrm{naf}(A)$, so $w_{\rm NAF}(-A) = w_{\rm NAF}(A)$.

**Step 2 (Uniqueness of NAF).** Suppose $e, e' : \mathbb{Z}_{\ge 0} \to \{-1, 0, 1\}$ are two finitely supported NAF representations of the same integer $A$. We prove $e = e'$ by induction on $K = \max(\{r + 1 : e_r \ne 0 \text{ or } e'_r \ne 0\} \cup \{0\})$. If $K = 0$, $e = e' = 0$. For $K \ge 1$: reducing $A = \sum e_r 2^r = \sum e'_r 2^r$ modulo $2$ gives $e_0 \equiv e'_0 \pmod 2$.
- If $A$ is even, then $e_0 = e'_0 = 0$, and the shifted sequences $(e_{r+1}), (e'_{r+1})$ are NAF representations of $A/2$ with support bound $\le K - 1$, hence equal by induction.
- If $A$ is odd, then $e_0, e'_0 \in \{-1, 1\}$ are both nonzero; non-adjacency forces $e_1 = e'_1 = 0$. Reducing modulo $4$ yields $e_0 \equiv A \equiv e'_0 \pmod 4$, forcing $e_0 = e'_0$ (since $1 \not\equiv -1 \pmod 4$). The shifted sequences represent $(A - e_0)/2$ with support bound $\le K - 1$, hence equal by induction.

**Step 3 (Cyclic equality $w_{\rm NAF}(A) \le w_{\rm rec}(|A|) \le w_{\min}(A) \le w_{\rm NAF}(A)$).**
1. *$w_{\min}(A) \le w_{\rm NAF}(A)$:* Immediate, as $\mathrm{naf}(A)$ is a signed power-of-$2$ representation of $A$ with $w_{\rm NAF}(A)$ terms.
2. *$w_{\rm rec}(|A|) \le w_{\min}(A)$ (using kernel-verified repository Lean input):* By the kernel-verified repository lemmas `signedWeight_add_le` and `signedWeight_sub_le` in `NormalityChecker/DigitMassTransfer.lean` (lines 538–545, proved there by strong induction on $a + c$), the recursive function `signedWeight` ($= w_{\rm rec}$) satisfies $w_{\rm rec}(0) = 0$, $w_{\rm rec}(2^m) = 1$, and $w_{\rm rec}(|u + v|) \le w_{\rm rec}(|u|) + w_{\rm rec}(|v|)$ for all $u, v \in \mathbb{Z}$ (checking the four sign combinations of $u, v$). Therefore, for ANY representation $A = \sum_{i=1}^r \varepsilon_i 2^{m_i}$, induction on $r$ gives $w_{\rm rec}(|A|) \le \sum_{i=1}^r w_{\rm rec}(2^{m_i}) = r$. Taking the minimum over all representations yields $w_{\rm rec}(|A|) \le w_{\min}(A)$.
3. *$w_{\rm NAF}(n) \le w_{\rm rec}(n)$ for all $n \in \mathbb{N}$ (hence for all $A \in \mathbb{Z}$ by Step 1 symmetry):* We first prove by strong induction on $k \ge 0$ the neighbor inequality $|w_{\rm rec}(k+1) - w_{\rm rec}(k)| \le 1$ (matching the private helper `signedWeight_succ_le` in `DigitMassTransfer.lean`, l. 478) together with the **parity monotonicity inequalities**:
   - Base $k = 0$: $w_{\rm rec}(0) = 0$, $w_{\rm rec}(1) = 1$, so $0 \le w_{\rm rec}(1) - w_{\rm rec}(0) = 1 \le 1$.
   - Even $k = 2j$ ($j \ge 1$): since $j < 2j$, the induction hypothesis gives $|w_{\rm rec}(j+1) - w_{\rm rec}(j)| \le 1$, hence $w_{\rm rec}(j) - 1 \le \min(w_{\rm rec}(j), w_{\rm rec}(j+1)) \le w_{\rm rec}(j)$. Adding $1$ yields
     ```math
     w_{\rm rec}(2j) = w_{\rm rec}(j) \le 1 + \min\bigl(w_{\rm rec}(j), w_{\rm rec}(j+1)\bigr) = w_{\rm rec}(2j + 1) \le w_{\rm rec}(2j) + 1,
     ```
     so $0 \le w_{\rm rec}(2j+1) - w_{\rm rec}(2j) \le 1$.
   - Odd $k = 2j + 1$ ($j \ge 0$): since $j < 2j + 1$, the induction hypothesis gives $|w_{\rm rec}(j+1) - w_{\rm rec}(j)| \le 1$, hence $w_{\rm rec}(j+1) - 1 \le \min(w_{\rm rec}(j), w_{\rm rec}(j+1)) \le w_{\rm rec}(j+1)$. Adding $1$ yields
     ```math
     w_{\rm rec}(2j + 2) = w_{\rm rec}(j + 1) \le 1 + \min\bigl(w_{\rm rec}(j), w_{\rm rec}(j+1)\bigr) = w_{\rm rec}(2j + 1) \le w_{\rm rec}(2j + 2) + 1,
     ```
     so $-1 \le w_{\rm rec}(2j+2) - w_{\rm rec}(2j+1) \le 0$.

   In particular, for every $q \ge 0$, $w_{\rm rec}(2q) \le w_{\rm rec}(2q+1)$ and $w_{\rm rec}(2q+2) \le w_{\rm rec}(2q+1)$. Now proceed by strong induction on $n \in \mathbb{N}$. Base cases $n = 0, 1$ are immediate. If $n = 2m$ ($m \ge 1$), $w_{\rm NAF}(2m) = w_{\rm NAF}(m) \le w_{\rm rec}(m) = w_{\rm rec}(2m)$. If $n = 2m + 1$ ($m \ge 1$):
   - If $m = 2q$ is even ($n \equiv 1 \pmod 4$), parity monotonicity gives $w_{\rm rec}(m) \le w_{\rm rec}(m+1)$, so $\min(w_{\rm rec}(m), w_{\rm rec}(m+1)) = w_{\rm rec}(m)$. Hence $w_{\rm NAF}(2m+1) = 1 + w_{\rm NAF}(m) \le 1 + w_{\rm rec}(m) = w_{\rm rec}(2m+1)$.
   - If $m = 2q + 1$ is odd ($n \equiv 3 \pmod 4$), parity monotonicity gives $w_{\rm rec}(m+1) \le w_{\rm rec}(m)$, so $\min(w_{\rm rec}(m), w_{\rm rec}(m+1)) = w_{\rm rec}(m+1)$. Since $m \ge 1$ implies $m + 1 < 2m + 1$, strong induction gives $w_{\rm NAF}(2m+1) = 1 + w_{\rm NAF}(m+1) \le 1 + w_{\rm rec}(m+1) = w_{\rm rec}(2m+1)$.

Closing the cycle proves $w_{\rm rec}(|A|) = w_{\min}(A) = w_{\rm NAF}(A)$ for every $A \in \mathbb{Z}$. $\square$

---

### 3.2 Proof of Theorem A.2 (General & Multi-Radix $2^s$ NAF Geometric Transfer)

**Part (1): Finite dyadic NAF tail and counting bound.**
Let $A \in \mathbb{Z}$ (arbitrary sign, arbitrary magnitude), $M \ge 1$, and $y = A \cdot 2^{-M}$. Let $e = \mathrm{naf}(A)$ with $e_r = 0$ for all $r < 0$ and all sufficiently large $r$. By Lemma A.1, $A = \sum_{r \ge 0} e_r 2^r$, $e_r e_{r+1} = 0$, and $\sum_{r \ge 0} |e_r| = w_\pm(A)$.

For any $0 \le j < M$, split $2^j y = A \cdot 2^{j - M}$ at $r = M - j$:

```math
2^j y = \underbrace{\sum_{r \ge M - j} e_r 2^{r + j - M}}_{\in \mathbb{Z}} + \underbrace{\sum_{t = 1}^{M - j} e_{M - j - t} 2^{-t}}_{=: S_j}.
```

Because the first sum is an exact integer (regardless of the sign of $A$ or whether $|A| \ge 2^M$), we have $\{2^j y\} = \{S_j\}$. Now suppose that for a given $\ell \ge 1$, the $\ell$ positions $e_{M-j-1}, \ldots, e_{M-j-\ell}$ all vanish. Then $S_j = \sum_{t = \ell + 1}^{M - j} e_{M - j - t} 2^{-t}$ (an empty sum $0$ if $M - j \le \ell$). Pair the indices beyond $\ell$ as $(\ell + 1 + 2i,\; \ell + 2 + 2i)$ for $i \ge 0$. By non-adjacency, for each $i \ge 0$ at most one of $e_{M-j-(\ell+1+2i)}$ and $e_{M-j-(\ell+2+2i)}$ is nonzero, so

```math
\bigl|e_{M-j-(\ell+1+2i)}\bigr|\, 2^{-(\ell+1+2i)} + \bigl|e_{M-j-(\ell+2+2i)}\bigr|\, 2^{-(\ell+2+2i)} \le 2^{-(\ell+1+2i)},
```

with **strict** inequality ($0 < 2^{-(\ell+1+2i)}$) for every $i$ satisfying $\ell + 1 + 2i > M - j$. Summing over $i \ge 0$ yields the strict bound

```math
|S_j| < \sum_{i = 0}^{\infty} 2^{-(\ell + 1 + 2i)} = \frac{2^{-(\ell + 1)}}{1 - 1/4} = \frac{2}{3}\, 2^{-\ell} \le \frac{1}{3} < \frac{1}{2}.
```

Inspecting the sign of $S_j$ handles carry wraparound at $0$ and $1$:
- If $S_j \ge 0$, then $\{2^j y\} = \{S_j\} = S_j \in \bigl[0,\, \frac{2}{3} 2^{-\ell}\bigr)$.
- If $S_j < 0$, then $-\frac{2}{3} 2^{-\ell} < S_j < 0$, so $\lfloor S_j \rfloor = -1$ and $\{2^j y\} = \{S_j\} = 1 + S_j \in \bigl(1 - \frac{2}{3} 2^{-\ell},\, 1\bigr)$.

In both cases, $\{2^j y\} \notin \bigl[\frac{2}{3} 2^{-\ell},\, 1 - \frac{2}{3} 2^{-\ell}\bigr]$. Taking the contrapositive: whenever $\{2^j y\} \in \bigl[\frac{2}{3} 2^{-\ell},\, 1 - \frac{2}{3} 2^{-\ell}\bigr]$, there exists $u \in \mathcal{S} := \{0 \le u < M : e_u \ne 0\}$ satisfying $M - j - \ell \le u \le M - j - 1$, equivalently $M - u - \ell \le j \le M - u - 1$.

Now let $s \ge 1$, $r \ge 1$, $\ell = sr$, and $s N \le M$, and consider $j = s m$ for $0 \le m < N$. For each fixed $u \in \mathcal{S}$, the interval $[M - u - sr,\, M - u - 1]$ consists of exactly $sr$ consecutive integers and therefore contains **exactly $r$** multiples of $s$. Double counting over $(m, u)$ gives

```math
\#\left\{0 \le m < N : \{2^{sm} y\} \in \left[\frac{2}{3} 2^{-sr},\; 1 - \frac{2}{3} 2^{-sr}\right]\right\}
  \le \sum_{u \in \mathcal{S}} r = r\, |\mathcal{S}| \le r\, w_\pm(A).
```

(Notice that integer-part NAF digits $e_u$ with $u \ge M$ never appear in $\mathcal{S}$, and negative $A$ is handled identically.)

**Part (2): Universal real-number shadowing.**
Let $x \in \mathbb{R}$ (arbitrary sign), $s \ge 1$, $r \ge 1$, $R \ge 2$, $N \ge 1$, and put $M = s N + R$, $A_M^* = \lfloor 2^M x \rfloor \in \mathbb{Z}$, and $y_M = 2^{-M} A_M^*$. By definition of the floor function on all of $\mathbb{R}$, $0 \le x - y_M < 2^{-M}$. Hence for every $0 \le m < N$, since $sm \le s(N - 1) = M - R - s \le M - R - 1$,

```math
0 \le \delta_m := 2^{sm} x - 2^{sm} y_M < 2^{sm - M} \le 2^{-(R + 1)} < 2^{-R}.
```

Because $R \ge 2$ and $sr \ge 1$, $\frac{2}{3} 2^{-sr} + 2^{-R} \le \frac{1}{3} + \frac{1}{4} = \frac{7}{12} < \frac{2}{3} \le 1 - \frac{2}{3} 2^{-sr}$, so $I_{sr, R} = \bigl[\frac{2}{3} 2^{-sr} + 2^{-R},\, 1 - \frac{2}{3} 2^{-sr}\bigr)$ is a well-defined nonempty subinterval of $[0, 1)$ of length $1 - \frac{4}{3} 2^{-sr} - 2^{-R}$. Write $2^{sm} x = q + \{2^{sm} x\}$ with $q = \lfloor 2^{sm} x \rfloor \in \mathbb{Z}$. Whenever $\{2^{sm} x\} \in I_{sr, R}$, we have

```math
\frac{2}{3} 2^{-sr} < \{2^{sm} x\} - \delta_m < 1 - \frac{2}{3} 2^{-sr} < 1,
```

so $2^{sm} y_M = q + (\{2^{sm} x\} - \delta_m)$ has **zero integer wraparound** and satisfies $\{2^{sm} y_M\} = \{2^{sm} x\} - \delta_m \in \bigl(\frac{2}{3} 2^{-sr},\, 1 - \frac{2}{3} 2^{-sr}\bigr)$. Applying Part (1) to $y_M = A_M^* 2^{-M}$ yields

```math
F_N\bigl(I_{sr, R}; x, 2^s\bigr) \le \frac{r\, w_\pm(\lfloor 2^{sN + R} x \rfloor)}{N}, \qquad
D_N(x; 2^s) \ge |I_{sr, R}| - F_N(I_{sr, R}; x, 2^s) \ge 1 - \frac{4}{3} 2^{-sr} - 2^{-R} - \frac{r\, w_\pm(\lfloor 2^{sN + R} x \rfloor)}{N}.
```

Taking $\liminf_{N \to \infty}$ with $R$ fixed (or equivalently choosing $R = R(N) \to \infty$ with $R(N) = o(N)$, e.g. $R(N) = \lfloor \sqrt{N} \rfloor + 2$, so $(sN + R(N))/N \to s$ and $2^{-R(N)} \to 0$) gives

```math
D^-(x; 2^s) \ge 1 - \frac{4}{3} 2^{-sr} - 2^{-R} - r s\, \bar{w}_\pm(x) \qquad (\forall R \ge 2),
```

and letting $R \to \infty$ yields $D^-(x; 2^s) \ge 1 - \frac{4}{3} 2^{-sr} - rs\,\bar{w}_\pm(x)$. Likewise, for any $[u, v) \subseteq (\frac{2}{3} 2^{-sr},\, 1 - \frac{2}{3} 2^{-sr}]$ with $u > \frac{2}{3} 2^{-sr}$, choosing $R \ge 2$ with $2^{-R} \le u - \frac{2}{3} 2^{-sr}$ ensures $[u, v) \subseteq I_{sr, R}$, so $\limsup_{N \to \infty} F_N([u, v); x, 2^s) \le rs\,\bar{w}_\pm(x)$.

**Part (3): Infinite signed series transfer.**
Assume $\log(1 + |a(n)|) = o(n)$. Fix any $\varepsilon \in (0, 1/2]$ and pick $n_0(\varepsilon)$ such that $\log_2(1 + |a(n)|) \le \varepsilon n$ for all $n \ge n_0(\varepsilon)$. Then $|a(n)| 2^{-kn} < 2^{-(k-\varepsilon)n} \le 2^{-n/2}$ for $n \ge n_0(\varepsilon)$, so $x = \sum_{n \ge 1} a(n) 2^{-kn}$ converges absolutely; moreover, for all $Q \ge n_0(\varepsilon)$,

```math
\Theta_Q := \sum_{m \ge 1} |a(Q + m)|\, 2^{-km} \le \frac{2^{\varepsilon Q}}{2^{k - \varepsilon} - 1} \le \frac{2^{\varepsilon Q}}{\sqrt{2} - 1} < 3 \cdot 2^{\varepsilon Q},
```

so $\log_2(1 + \Theta_Q) \le 2 + \varepsilon Q$. Since $\varepsilon > 0$ was arbitrary, $\log_2(1 + \Theta_Q) = o(Q)$.

For any $M \ge 1$, put $Q = \lfloor M/k \rfloor$. By exact prefix decomposition (`GF-36` Theorem 2.1, Lean `floor_pow_mul_eq_head_add_floor_tail`), $2^M x = A_M + \tau_M$ with $A_M = \sum_{n=1}^Q a(n) 2^{M - kn} \in \mathbb{Z}$ and $|\tau_M| \le 2^{k-1} \Theta_Q$, so $\lfloor 2^M x \rfloor = A_M + \lfloor \tau_M \rfloor$ (valid for all signs of $x, A_M, \tau_M$). Subadditivity and $2$-shift invariance of $w_\pm$ give

```math
w_\pm\bigl(\lfloor 2^M x \rfloor\bigr) \le \sum_{n=1}^{Q} w_\pm(a(n)) + w_\pm\bigl(\lfloor \tau_M \rfloor\bigr).
```

For every integer $T \in \mathbb{Z}$, $w_\pm(T) \le s_2(|T|) \le \log_2(|T| + 1)$ (since $|T| \ge \sum_{i=0}^{s_2(|T|)-1} 2^i = 2^{s_2(|T|)} - 1$). Since $|\lfloor \tau_M \rfloor| \le |\tau_M| + 1$ for all real $\tau_M$ (positive or negative),

```math
w_\pm\bigl(\lfloor \tau_M \rfloor\bigr) \le \log_2\bigl(|\tau_M| + 2\bigr) \le k + \log_2(1 + \Theta_Q) = o(M).
```

Dividing by $M$ and using $Q/M \le 1/k$ yields $\bar{w}_\pm(x) = \limsup_{M \to \infty} w_\pm(\lfloor 2^M x \rfloor)/M \le C/k$. Substituting into Part (2) completes the proof.

**Part (4): Unimodality and `GF-36` comparison.**
Direct algebra gives $g_1(\rho) = \frac{1}{3} - \rho$, $g_2(\rho) = \frac{2}{3} - 2\rho = 2 g_1(\rho)$, and $g_{\ell+1}(\rho) - g_\ell(\rho) = \frac{4}{3}(2^{-\ell} - 2^{-\ell-1}) - \rho = \frac{2}{3} 2^{-\ell} - \rho$, which decreases strictly in $\ell$ and changes sign at $\rho = \frac{2}{3} 2^{-\ell}$. For $0 < \rho < \frac{1}{3}$, choosing $\ell = \lceil \log_2(2/(3\rho)) \rceil \ge 2$ satisfies $\frac{4}{3} 2^{-\ell} \le 2\rho$ and $\ell < \log_2(4/(3\rho))$, giving $1 - g_\ell(\rho) \le \rho(2 + \log_2(4/(3\rho))) = \rho \log_2(16/(3\rho)) \to 0$. Finally, for every $m \ge 2$, setting $\ell = 2(m-1)$ gives slope $-2(m-1)\rho$ and intercept $1 - \frac{4}{3} 2^{-2(m-1)} = 1 - \frac{1}{3} 2^{4-2m} > 1 - 2^{1-m}$ (since $2^{4-2m}/3 < 2^{1-m} \iff 8 < 3 \cdot 2^m$, true for all $m \ge 2$). $\square$

---

### 3.3 Proof of Theorems B.1 and B.2 ($E_+(2^k)$, Order-4 Nonnormality, and DP-Free Majorants)

**Proof of Theorem B.1.**
Since $a_+(n) = (1 - v_2(n)) \tau_{\rm odd}(n)$ satisfies $|a_+(n)| \le \tau(n) \le 2\sqrt{n}$, we have $\log(1 + |a_+(n)|) = o(n)$ and $w_\pm(a_+(n)) = w_\pm\bigl(\mathbf{1}_{v_2(n) \ne 1} \operatorname{odd}(|1 - v_2(n)|) \prod_{p > 2} \operatorname{odd}(v_p(n)+1)\bigr)$. By the independent-exponent model (`GF-36` Lemma 3.2, proved elementarily from Wintner's squarefull convolution lemma without external inputs), the exact limit $W_+ = \lim_{X \to \infty} \frac{1}{X} \sum_{n \le X} w_\pm(a_+(n))$ exists. Two completely independent pure-`int`/`Fraction` certificates in `scripts/phase25_naf_transfer.py` (§2) re-certify the Phase 24 enclosures $W_+ \in [0.907252, 0.912845]$ (re-certification of Phase 24 `GF-40` Thm. 3.1(a), pure-`Fraction` truncation at $P = 600, U_{\rm cap} = 512, K_2 = 24$) and $W_+ \in [0.908174, 0.908184]$ (re-certification of Phase 24 `GF-36` Thm. 7.2, scale-$2^{-192}$ integer DP at $Y = 200{,}000, y = 20{,}000$). For the `GF-40` Thm. 3.1(a) re-certification, writing $V := \prod_{p > 600} \operatorname{odd}(e_p + 1)$ with independent $e_p \sim \mathrm{Geom}(1/p)$, the three tail constants used in `scripts/phase25_naf_transfer.py` (§2a) are verified elementarily and asserted explicitly:
1. telescoping over odd integers $n = 2m + 1 \ge 601$ ($n^{-2} < \frac{1}{2}((n-1)^{-1} - (n+1)^{-1})$) gives $\Pr(V \ne 1) \le \sum_{p > 600} p^{-2} < \frac{1}{2 \cdot 600} = \frac{1}{1200}$;
2. for every prime $p \ge 601$, $\operatorname{odd}(e+1) - 1 \le e$ for all $e \ge 2$, so $\ell_{\rm odd}(p) - 1 = (1 - p^{-1})\sum_{e \ge 2}(\operatorname{odd}(e+1) - 1)p^{-e} \le (1 - p^{-1})\sum_{e \ge 2} e p^{-e} = (2 + \frac{1}{p-1})p^{-2} \le \frac{1201}{600} p^{-2}$, whence $S_V := \sum_{p > 600}(\ell_{\rm odd}(p) - 1) < \frac{1201}{720000}$ and $\mathbb{E}[V] = \prod_{p > 600}\ell_{\rm odd}(p) \le (1 - S_V)^{-1} = \frac{720000}{718799} < 1 + \frac{2}{600}$;
3. $\mathbb{E}[V \mathbf{1}_{V \ne 1}] = (\mathbb{E}[V] - 1) + \Pr(V \ne 1) < \frac{1201}{718799} + \frac{1}{1200} < \frac{5}{1200}$.

Applying Theorem A.2(3) with $C = W_+$:
1. At $k = 3$ ($E_+(8)$), $\rho = W_+/3 \in [\frac{1}{6}, \frac{1}{3})$, so the optimal parameters are $\ell^* = 2$ in base $2$ and $r^* = 1$ in base $4$, yielding $D^-(E_+(8); 2), D^-(E_+(8); 4) \ge \frac{2}{3} - \frac{2}{3} W_+$. Substituting $W_+ \le \frac{912845}{10^6}$ and $W_+ \le \frac{908184}{10^6}$ yields exact $\frac{17431}{300000}$ and $\frac{11477}{187500}$ respectively; radix descent (`GF-36` Prop. 2.4(5), Lean `radixDiscrepancy_descent`) yields $D^-(E_+(8); 8) \ge \frac{3}{7} D^-(E_+(8); 2) \ge \frac{11477}{437500}$.
2. Because $\frac{3}{16} = \frac{1}{6} + \frac{1}{48} > \frac{1}{6} + 2^{-6}$ and $\frac{13}{16} = \frac{5}{6} - \frac{1}{48} < \frac{5}{6}$, Theorem A.2(2)–(3) at $(s, r) = (1, 2)$ and $(2, 1)$ gives $\limsup_N F_N([\frac{3}{16}, \frac{13}{16}); E_+(8), b) \le \frac{2 W_+}{3} \le 0.605456 < \frac{10}{16} = 0.625$ for $b \in \{2, 4\}$. Since $[\frac{3}{16}, \frac{13}{16}) = \bigsqcup_{v=3}^{12} [\frac{v}{16}, \frac{v+1}{16})$ is the disjoint union of $10$ length-$4$ binary cylinders (and $10$ length-$2$ base-$4$ cylinders), $E_+(8)$ cannot be $4$-normal in base $2$ or $2$-normal in base $4$.
3. For $k \ge 4$, $[1/4, 3/4) \subset (1/6, 5/6)$ (two base-$4$ digits $\{1, 2\}$, length $\frac{1}{2}$) and $[1/8, 7/8) \subset (1/12, 11/12)$ (six base-$8$ digits $\{1, \dots, 6\}$, length $\frac{3}{4}$) give via Theorem A.2(2)–(3) $\limsup F_N([\frac{1}{4}, \frac{3}{4}); E_+(2^k), 4) \le \frac{2 W_+}{k} \le 0.454092 < \frac{1}{2}$ (also excluding $2$-normality in base $2$) and $\limsup F_N([\frac{1}{8}, \frac{7}{8}); E_+(2^k), 8) \le \frac{3 W_+}{k} \le 0.681138 < \frac{3}{4}$. For $k \ge 5$ in base $2^k$ ($s = k, r = 1$), $[2^{-k}, 1 - 2^{-k}) \subset (\frac{2}{3} 2^{-k}, 1 - \frac{2}{3} 2^{-k})$ has length $1 - 2^{1-k} \ge \frac{15}{16} = 0.9375 > W_+ = k \cdot (W_+/k)$, proving simple nonnormality in base $2^k$. $\square$

**Proof of Theorem B.2.**
1. For any multiplicative $G \ge 0$ with $G(n) \ge w_\pm(a_+(n))$ for all $n \ge 1$, evaluating at prime powers $2^e$ ($a_+(2^e) = 1 - e$) and $p^e$ ($p > 2$, $a_+(p^e) = e + 1$) forces $G(2^e) \ge w_\pm(|1 - e|)$ and $G(p^e) \ge w_\pm(e + 1)$, hence $G(n) \ge G_0(n)$ pointwise. The Euler product mean of $G_0$ is independently re-certified in `scripts/phase25_naf_transfer.py` (§2) as $W_+^{\rm maj} \in [0.936414, 0.936415] < \frac{15}{16}$ (matching Phase 24 `GF-36` Thm. 7.2).
2. For $G_{\{2,3\}}$: writing $n = 2^{e_2} 3^{e_3} m$ with $\gcd(m, 6) = 1$, $a_+(n) = (1 - e_2)(e_3 + 1) \tau_{\rm odd}(m)$, so submultiplicativity of $w_\pm$ and $w_\pm \le s_2$ give $w_\pm(a_+(n)) \le w_\pm(|1 - e_2|(e_3 + 1)) \prod_{p \ge 5} s_2(v_p(m) + 1) = G_{\{2,3\}}(n)$. Its Möbius convolution $h_{\{2,3\}} = G_{\{2,3\}} * \mu$ factors as $h_{2,3}(2^{e_2} 3^{e_3}) h_{\ge 5}(m)$, where $h_{2,3}(2^{e_2} 3^{e_3}) = \Delta_{e_2} \Delta_{e_3} w_\pm(|1 - e_2|(e_3 + 1))$ satisfies $|h_{2,3}(2^{e_2} 3^{e_3})| \le 4(e_2 + 1)(e_3 + 1)$ and $h_{\ge 5}(p^e) = 1 - v_2(e+1)$ is supported on squarefull $m$ coprime to $6$. Thus $\sum_{n \ge 1} |h_{\{2,3\}}(n)| / n < \infty$, and `tendsto_average_of_summable_conv_mobius` gives
   ```math
   \lim_{X \to \infty} \frac{1}{X} \sum_{n=1}^X G_{\{2,3\}}(n)
     = \underbrace{\left(\sum_{e_2 \ge 0} \sum_{e_3 \ge 0} \frac{w_\pm(|1 - e_2|(e_3 + 1))}{2^{e_2 + 1}} \cdot \frac{2}{3^{e_3 + 1}}\right)}_{=: L_{\{2,3\}}}
       \cdot \prod_{p \ge 5} \left(1 - \frac{1}{p}\right) \sum_{e \ge 0} \frac{s_2(e + 1)}{p^e}.
   ```
   Using $w_\pm(|1-e_2|(e_3+1)) \le |1-e_2|(e_3+1)$, $\sum_{e_2 \ge 0} |1-e_2| 2^{-(e_2+1)} = 1$, $\sum_{e_2 \ge E_2} (e_2-1) 2^{-(e_2+1)} = E_2 2^{-E_2}$, and $\sum_{e_3 \ge E_3} (e_3+1)\frac{2}{3} 3^{-e_3} = 3^{-E_3}(E_3 + \frac{3}{2})$ bounds $L_{\{2,3\}}$ rigorously from its finite $(E_2, E_3) = (18, 14)$ sum. For each prime $p \ge 5$, the local kernel inequality (`local_kernel_le`, private in `DigitMassTransfer.lean`) gives local factor $\le B(p) = (1 - p^{-2})^{-1} - p^{-3} - 2p^{-7} \le 1 + p^{-2}$. For $p > P_{\rm cut}$, either the trivial tail $\sum_{n > P_{\rm cut}} n^{-2} \le 1/P_{\rm cut}$ (`sum_Ico_inv_sq_le`) or the elementary $\pm 1 \pmod 6$ telescoping tail
   ```math
   \sum_{p \ge 6M - 1} \frac{1}{p^2} \le \sum_{m \ge M} \left(\frac{1}{(6m-1)^2} + \frac{1}{(6m+1)^2}\right)
     < \frac{1}{6}\left(\frac{1}{6M - 7} + \frac{1}{6M - 5}\right) < \frac{1}{3(6M - 7)}
   ```
   together with $\prod (1 + p^{-2}) \le (1 - \sum p^{-2})^{-1}$ (`prod_one_add_mul_le`) certifies $M_{\{2,3\}} \le 0.929153 < \frac{93}{100}$ (at $P_{\rm cut} = 211$, **45 primes**). The identical computation for $G_{\{2,3,5\}}$ (with $\sum_{e_5 \ge E_5} (e_5+1)\frac{4}{5} 5^{-e_5} = 5^{-E_5}(E_5 + \frac{5}{4})$) certifies $M_{\{2,3,5\}} \le 0.924468 < \frac{93}{100}$ at $P_{\rm cut} = 47$ (12 primes) and $\le 0.928395 < \frac{93}{100}$ at $P_{\rm cut} = 109$ (26 primes, trivial tail). $\square$

---

### 3.4 Proof of Theorem B.3 (Independent NAF Re-Derivation of $m_1, \dots, m_4$ & Order-3 Barrier)

1. *(Lower bounds and LP relaxation.)* For $L = 1$, $m_1 \ge 0$ is trivial and attained by $E_2 \in K_2$ (`GF-03`; or alternating $0^m 1^m$). For $L = 2$ (and hence $L = 3$), $2$-normality gives $F_N([\frac{1}{4}, \frac{3}{4}); x, 2) \to \frac{1}{2}$, so Theorem A.2(2) at $\ell = 2$ gives $\frac{1}{2} \le 2 \bar{w}_\pm(x)$, i.e., $\bar{w}_\pm(x) \ge \frac{1}{4}$. For $L = 4$, $4$-normality gives $F_N([\frac{3}{16}, \frac{13}{16}); x, 2) \to \frac{5}{8}$, so Theorem A.2(2) at $\ell = 2$ gives $\frac{5}{8} \le 2 \bar{w}_\pm(x)$, i.e., $\bar{w}_\pm(x) \ge \frac{5}{16}$.
   *(Validity of the carry-automaton LP relaxation in `scripts/phase25_naf_transfer.py` §3a.)* Reading the binary digits $b_1, \dots, b_N$ of $\lfloor 2^N x \rfloor$ from most- to least-significant bit, the canonical NAF representation $e_r \in \{-1, 0, 1\}$ satisfies the recurrence $b_i + 2 d_{i-1} - d_i = a_i$ with carries $d_i \in \{-1, 0\} \subset \{-1, 0, 1\}$ and cost $\mathbf{1}_{a_i \ne 0}$ summing to $w_\pm(\lfloor 2^N x \rfloor) + O(1)$. The empirical distribution over edges $((d_{i-1}, h_{i-1}), (d_i, h_i), w_i, a_i)$ along a prefix of length $N$ violates flow conservation at each state $(d, h)$ by at most $O(1/N)$; along any subsequence $N_r \to \infty$ realizing $\liminf_{N \to \infty} w_\pm(\lfloor 2^N x \rfloor)/N$, compactness of the finite-dimensional probability simplex yields a subsequential limit flow satisfying exact flow conservation and (by $L$-normality of $x$) uniform $L$-word marginals $2^{-L}$. Thus the LP optimum $\mathrm{LP}^*_L$ is a valid lower bound $\mathrm{LP}^*_L \le \liminf_{N \to \infty} w_\pm(\lfloor 2^N x \rfloor)/N$, independently confirming $0, \frac{1}{4}, \frac{1}{4}, \frac{5}{16}$ for $L = 1, 2, 3, 4$ (and matching Phase 25 Track D Thm. 1.7's $\bar{g}_L$).
2. *(Exact irrational $3$-normal witness $x_*$.)* Let $B_m$ be the $8m$-bit integer $(\mathtt{0001})^m(\mathtt{1110})^m$ ($m \ge 1$). Observe that $(\mathtt{0001})^m = \sum_{j=0}^{m-1} 2^{4j}$ and $(\mathtt{1110})^m = (2^{4m} - 1) - \sum_{j=0}^{m-1} 2^{4j} = 2^{4m} - 2 - \sum_{j=1}^{m-1} 2^{4j}$. Therefore:
   ```math
   B_m = 2^{4m}\sum_{j=0}^{m-1} 2^{4j} + 2^{4m} - 2 - \sum_{j=1}^{m-1} 2^{4j}
       = \sum_{j=1}^{m-1} 2^{4m + 4j} + 2^{4m + 1} - \sum_{j=1}^{m-1} 2^{4j} - 2^1.
   ```
   Every exponent in this sum is separated from its neighbors by at least $3 \ge 2$ (gaps $4, \dots, 4, 3, 5, 4, \dots, 4, 3$), and concatenating $B_m$ with $B_{m+1}$ leaves a gap of $1 + 4 = 5 \ge 2$ between the lowest digit $-2^1$ of $B_m$ and the highest digit $+2^{8(m+1)-4}$ of $B_{m+1}$. By uniqueness of NAF (Lemma A.1), this sum is the **exact canonical NAF** of $\lfloor 2^{S_M} x_* \rfloor$ for every $M \ge 1$, with weight $\sum_{m=1}^M 2m = M(M+1) = S_M / 4$. For arbitrary $N \in [S_M, S_{M+1})$, $N - S_M < 8(M+1) = O(\sqrt{N})$, and truncating the final block $B_{M+1}$ adds at most $\frac{1}{4}(N - S_M) + O(1)$ to $w_\pm$ (since each $4$-bit unit contributes $1$ signed digit plus at most $O(1)$ boundary correction), yielding $w_\pm(\lfloor 2^N x_* \rfloor) = \frac{N}{4} + O(1)$, hence $\lim_{N \to \infty} w_\pm(\lfloor 2^N x_* \rfloor)/N = \frac{1}{4}$.
   To verify $3$-normality of $x_*$: inside $(\mathtt{0001})^m$, each of the four words $\{\mathtt{000}, \mathtt{001}, \mathtt{010}, \mathtt{100}\}$ appears $m + O(1)$ times and no other $3$-word appears; inside $(\mathtt{1110})^m$, each of the remaining four words $\{\mathtt{111}, \mathtt{110}, \mathtt{101}, \mathtt{011}\}$ appears $m + O(1)$ times and no other $3$-word appears. Across $m = 1, \dots, M$, each of the $8$ length-$3$ words occurs $\sum_{m=1}^M m + O(M) = \frac{1}{2} M(M+1) + O(M) = \frac{1}{8} S_M + O(\sqrt{S_M})$ times. Since $N - S_M = O(\sqrt{N})$, $f_N(w; x_*, 2) = \frac{1}{8} + O(N^{-1/2}) \to \frac{1}{8}$ for all $w \in \{0, 1\}^3$. Irrationality of $x_*$ is immediate because $x_*$ contains arbitrarily long blocks of $(\mathtt{0001})^m$ followed by `1110`, ruling out eventual periodicity.
3. *(Exact $4$-normal witness $x_4$.)* The $16$-bit word $W_4 = \mathtt{0000100110101111}_2 = 2479$ is a binary de Bruijn cycle of order $4$: its $16$ cyclic length-$4$ windows are pairwise distinct, so every length-$4$ word occurs in $x_4 = 2479/(2^{16}-1)$ with exact limiting frequency $\frac{1}{16}$. Since $2479 = 2^{11} + 2^9 - 2^6 - 2^4 - 1$ has non-adjacent exponents $\{11, 9, 6, 4, 0\}$ and wraparound gap $16 - 11 = 5 \ge 2$, the $16m$-bit integer $\lfloor 2^{16m} x_4 \rfloor = 2479 \sum_{j=0}^{m-1} 2^{16j}$ is already in exact canonical NAF with weight $5m$, giving $\lim_{N \to \infty} w_\pm(\lfloor 2^N x_4 \rfloor)/N = \frac{5}{16}$. Adding $u = \sum_{r \ge 1} 2^{-2^{r^2}}$ changes $o(N)$ digits (preserving $4$-normality and adding $O(\sqrt{\log N}) = o(N)$ to $w_\pm$) while making $x_4 + u$ irrational (since $u$ is irrational and $x_4 \in \mathbb{Q}$).
4. *(Limitation corollary.)* Immediate: if a proof deduces $\neg\mathrm{OrderNormal}(2, 3, x)$ solely from $\bar{w}_\pm(x) \le \alpha$ with $\alpha \ge \frac{1}{4}$, applying it to $x_*$ (which satisfies $\bar{w}_\pm(x_*) = \frac{1}{4} \le \alpha$) yields a contradiction. $\square$

---

### 3.5 Proof of Lemma C.1, Theorem C.2, and Theorem C.3 (Cubic Characters & Dense Signed Families)

**Proof of Lemma C.1 (Zero external inputs).**
Write $G = H * \mathbf{1}$, so $G(n) = \sum_{d \mid n} H(d)$. Since $\chi^\circ$ is completely multiplicative ($\chi^\circ(dm) = \chi^\circ(d)\chi^\circ(m)$ for all $d, m \ge 1$),

```math
\sum_{n=1}^{X} \chi^\circ(n)\, G(n)
  = \sum_{d=1}^{X} \chi^\circ(d)\, H(d) \sum_{m=1}^{\lfloor X/d \rfloor} \chi^\circ(m).
```

Every integer $m \ge 1$ factors uniquely as $m = s \cdot m'$ where every prime divisor of $s$ divides $M$ and $\gcd(m', M) = 1$, giving $\chi^\circ(m) = \chi(m')$. Since $\chi(k) = 0$ whenever $\gcd(k, M) > 1$, for every $Y \ge 1$ we have

```math
\left|\sum_{m=1}^{Y} \chi^\circ(m)\right|
  = \left|\sum_{\substack{s \le Y \\ p \mid s \Rightarrow p \mid M}} \sum_{m'=1}^{\lfloor Y/s \rfloor} \chi(m')\right|
  \le M \cdot \#\{s \le Y : p \mid s \Rightarrow p \mid M\}
  \le M (\log_2 Y + 1)^{\omega(M)},
```

where $\left|\sum_{m'=1}^Z \chi(m')\right| \le M$ holds because $\chi$ is nonprincipal (its sum over any complete period of length $M$ vanishes, leaving at most $M - 1$ terms of modulus $\le 1$), and each of the $\omega(M)$ prime divisors $p \mid M$ has exponent $0 \le v_p(s) \le \lfloor \log_p Y \rfloor \le \lfloor \log_2 Y \rfloor$. Substituting into the convolution sum and using $|\chi^\circ(d)| \le 1$ and $1 \le (X/d)^\sigma$ ($d \le X$) yields

```math
\left|\frac{1}{X} \sum_{n=1}^{X} \chi^\circ(n)\, G(n)\right|
  \le \frac{M(\log_2 X + 1)^{\omega(M)}}{X} \sum_{d=1}^{X} |H(d)| \left(\frac{X}{d}\right)^\sigma
  \le M \Bigl(\sum_{d \ge 1} \frac{|H(d)|}{d^\sigma}\Bigr) X^{\sigma - 1} (\log_2 X + 1)^{\omega(M)} \longrightarrow 0.
```

Now let $\chi$ be a primitive cubic character modulo $M$. On the support of $c = 1 * \chi$ (i.e., $v_p(n) \not\equiv 2 \pmod 3$ whenever $\chi(p) \in \{\omega, \bar\omega\}$), we have $c(n) = A(n) e^{i\pi t(n)/3}$ with $A(n) = \prod_{\chi(p)=1}(v_p(n) + 1)$ and $e^{2\pi i t(n)/3} = \chi^\circ(n)$ (`GF-31` §1–2). Checking all six phases $s = t(n) \bmod 6 \in \{0, 1, 2, 3, 4, 5\}$ gives $c_+(n)/A(n) \in \{2, 1, -1, -2, -1, 1\}$ and $c_-(n)/A(n) \in \{0, 1, 1, 0, -1, -1\}$, with $c_-(n) = 0 \iff s \in \{0, 3\} \iff \chi^\circ(n) = 1$. Since $w_\pm(\pm 2m) = w_\pm(\pm m) = w_\pm(m)$, **identically for every $n \ge 1$**:

```math
w_\pm(c_+(n)) = \mathbf{1}_{c(n) \ne 0}\, w_\pm(A(n)), \qquad
w_\pm(c_-(n)) = \mathbf{1}_{\chi^\circ(n) \ne 1}\, \mathbf{1}_{c(n) \ne 0}\, w_\pm(A(n)).
```

Because $\chi^\circ(n) \in \{1, \omega, \bar\omega\}$ never vanishes, orthogonality gives the exact identity $\mathbf{1}_{\chi^\circ(n) \ne 1} = \frac{2}{3} - \frac{1}{3}\chi^\circ(n) - \frac{1}{3}\overline{\chi^\circ(n)}$. Applying Lemma C.1 at $\sigma = \frac{3}{4}$ to $G_\chi$ (where $G_\chi(p) = 1$ for all $p$ and $G_\chi(p^e) \le e + 1$, so $(G_\chi * \mu)(p) = 0$ and $\sum |H_\chi(d)| d^{-3/4} < \infty$) and to $U_\chi$ (same properties) immediately proves $\lim_{X \to \infty} \frac{1}{X} \sum_{n \le X} \mathbf{1}_{\chi^\circ(n) \ne 1} G_\chi(n) = \frac{2}{3} W_\chi$ and $\lim_{X \to \infty} \frac{1}{X} \sum_{n \le X} \mathbf{1}_{\chi^\circ(n) \ne 1} U_\chi(n) = \frac{2}{3} C_{\rm odd}$.

For the exact true mean $W_{\chi, \rm true}$, put $F(n) := w_\pm(c_+(n)) \le G_\chi(n)$ and fix a prime cutoff $y > M$. Call $n$ *$y$-good* if no prime $p > y$ with $\chi(p) = 1$ satisfies $p^2 \mid n$. Every $y$-good integer factors uniquely as $n = m \cdot r$ where $m$ is $y$-smooth and $r$ lies in the support of the multiplicative indicator $\rho$ ($\rho(p^e) = 0$ for $p \le y, e \ge 1$; $\rho(p^e) = \mathbf{1}_{e \le 1}$ for $p > y, \chi(p)=1$; $\rho(p^e) = \mathbf{1}_{e \not\equiv 2(3)}$ for $p > y, \chi(p) \in \{\omega, \bar\omega\}$), and on such $n$ we have $F(mr) = F(m)$ (since $A(r)$ is a power of $2$) and $\chi^\circ(mr) = \chi^\circ(m)\chi^\circ(r)$. Two explicit estimates justify passing to $X \to \infty$ and then $y \to \infty$:
1. *Uniform-in-$X$ tail for $y$-bad integers:* Write $K_1 := \sum_{d \ge 1} |H_\chi(d)| / d < \infty$. For every $Y \ge 1$, $\sum_{k \le Y} G_\chi(k) = \sum_{d \le Y} H_\chi(d) \lfloor Y/d \rfloor \le K_1 Y$. Hence for any prime $p > y$ with $\chi(p) = 1$,
   ```math
   \sum_{\substack{n \le X \\ p^2 \mid n}} G_\chi(n)
     = \sum_{e \ge 2} w_\pm(e + 1) \sum_{\substack{k \le X / p^e \\ p \nmid k}} G_\chi(k)
     \le K_1 X \sum_{e \ge 2} \frac{e + 1}{p^e}
     = K_1 X \frac{3 - 2/p}{p^2 (1 - 1/p)^2}
     \le \frac{8 K_1 X}{p^2},
   ```
   and summing over primes $p > y$ gives the uniform-in-$X$ bound
   ```math
   \frac{1}{X} \sum_{\substack{n \le X \\ n\text{ not }y\text{-good}}} G_\chi(n) \le 8 K_1 \sum_{p > y} \frac{1}{p^2}.
   ```
2. *Dominated convergence over $y$-smooth $m$:* Since $(\rho * \mu)(p) = 0$ for every prime $p > y$, $\sum_{d \ge 1} |(\rho * \mu)(d)| d^{-3/4} < \infty$, so Lemma C.1 gives $\frac{1}{X} \sum_{r \le X/m} \chi^\circ(r) \rho(r) \to 0$ as $X \to \infty$ for every fixed $y$-smooth $m$. Moreover, each summand in
   ```math
   \frac{1}{X} \sum_{\substack{n \le X \\ n\text{ }y\text{-good}}} \chi^\circ(n) F(n)
     = \sum_{m\text{ }y\text{-smooth}} \chi^\circ(m) F(m) \left(\frac{1}{X} \sum_{r \le X/m} \chi^\circ(r) \rho(r)\right)
   ```
   is bounded in modulus uniformly in $X$ by $F(m) \cdot \frac{1}{X}\lfloor X/m \rfloor \le \frac{G_\chi(m)}{m}$, whose sum over all $y$-smooth $m$ converges: $\sum_{m\text{ }y\text{-smooth}} \frac{G_\chi(m)}{m} = \prod_{p \le y} \sum_{e \ge 0} \frac{G_\chi(p^e)}{p^e} < \infty$ (since $G_\chi(p^e) \le e + 1$). By dominated convergence, $\lim_{X \to \infty} \frac{1}{X} \sum_{n \le X,\, y\text{-good}} \chi^\circ(n) F(n) = 0$ (and identically for $\overline{\chi^\circ}$).

Combining (1) and (2) gives $\limsup_{X \to \infty} \left|\frac{1}{X}\sum_{n \le X} \chi^\circ(n) F(n)\right| \le 8 K_1 \sum_{p > y} p^{-2}$; letting $y \to \infty$ proves $\frac{1}{X}\sum_{n \le X} \chi^\circ(n) F(n) \to 0$, and therefore $\lim_{X \to \infty} \frac{1}{X} \sum_{n \le X} w_\pm(c_-(n)) = \frac{2}{3} W_{\chi, \rm true}$ with zero external inputs. $\square$

**Proof of Theorem C.2.**
Since $|c_\pm(n)| \le 2 A(n) \le 2 \tau(n) \le 4\sqrt{n}$, $\log(1 + |c_\pm(n)|) = o(n)$ holds for every cubic character. Combining Lemma C.1 with Theorem A.2(3) and the certified outward-rounded enclosures of `scripts/phase25_naf_transfer.py` (§4; all 6-digit discrepancy lower bounds are evaluated from the unrounded certified upper endpoints and rounded down) yields every numerical bound and excluded normality order in parts (1)–(5):
- For $L_-(4)$ ($k = 2$) and $L_+(8)$ ($k = 3$), $\rho = \frac{2}{3} W_\chi / 2 = W_\chi / 3 \in (\frac{1}{4}, \frac{5}{16})$ for $M \in \{7, 9, 13, 19, 37\}$, so $\ell^* = 2$ in base $2$ ($r^* = 1$ in base $4$) gives $D^-(\cdot; 2), D^-(\cdot; 4) \ge \frac{2}{3} - \frac{2}{3} W_\chi$ (and $\ge \frac{2}{3} - \frac{2}{3} C_{\rm odd}$, yielding $\frac{2}{15}$ for $M = 7$ and $\frac{8}{75}$ for $M = 9, 13$ directly from `GF-31`'s $C_{\rm odd} < \frac{4}{5}, \frac{21}{25}$), while $2\rho < \frac{5}{8}$ excludes $4$-normality in base $2$ and $2$-normality in base $4$ (checked for all five moduli $7, 9, 13, 19, 37$ in `scripts/phase25_naf_transfer.py` §4b–4c). For BOTH $L_-(4)$ and $L_+(8)$ in base $8$, uniformly taking $\max(\frac{5}{6} - W_\chi,\, \frac{3}{7} D^-(\cdot; 2))$ gives $0.076428$ ($0.076461$ via $W_{\rm true}$, direct base-8 wins) at $M = 7$, $0.055852$ ($0.055863$, descent wins) at $M = 9$, $0.060196$ ($0.060239$, descent wins) at $M = 13$, $0.064400$ (descent wins) at $M = 19$, and $0.082161$ (direct base-8 wins) at $M = 37$.
- For $L_-(8)$ ($k = 3$), $\rho = \frac{2}{9} W_\chi \in (\frac{1}{6}, \frac{1}{4})$ for $M \in \{7, 9, 13\}$, so $\ell^* = 2$ gives $D^-(\cdot; 2), D^-(\cdot; 4) \ge \frac{2}{3} - \frac{4}{9} W_\chi$, $2\rho < \frac{1}{2}$ excludes $2$-normality in base $2$ and simple normality in base $4$, and $3\rho = \frac{2}{3} W_\chi < \frac{3}{4}$ excludes simple normality in base $8$ with $D^-(L_-(8); 8) \ge \frac{5}{6} - \frac{2}{3} W_\chi$.
- For $M \in \{31, 43\}$, the certified lower end satisfies $W_\chi / 3 > \frac{1}{3}$, and for $L_+(4)$ ($M \in \{7, 9, 13\}$), $W_{\chi, \rm true}/2 > \frac{1}{3}$, confirming these stay outside the theorem. $\square$

**Proof of Theorem C.3.**
1. Expanding $(2^{km} + 1)^{-1} = \sum_{j \ge 1} (-1)^{j-1} 2^{-kjm}$ gives $a_+^*(n) = \sum_{d \mid n} \mu^2(d) (-1)^{n/d - 1}$. Write $n = 2^e m$ ($m$ odd). Every squarefree divisor $d \mid n$ is either $d_1 \mid m$ (squarefree) or $2 d_1$ (when $e \ge 1$). If $e = 0$, every $n/d_1$ is odd, giving $+\sum_{d_1 \mid m} \mu^2(d_1) = 2^{\omega(m)}$. If $e = 1$, $n/d_1$ is even ($-1$) while $n/(2 d_1)$ is odd ($+1$), cancelling identically to $0$. If $e \ge 2$, both $n/d_1$ and $n/(2 d_1)$ are even ($-1$), giving $-2 \cdot 2^{\omega(m)} = -2^{\omega(m)+1}$. The same split with the extra sign $(-1)^{d-1}$ gives $a_{\rm alt, +}^*(n)$ ($+2^{\omega(m)}$ for $e=0$, $-2^{\omega(m)+1}$ for $e=1$, $0$ for $e \ge 2$). Hence $w_\pm(a_+^*(n)) = \mathbf{1}_{n \not\equiv 2 (4)}$ and $w_\pm(a_{\rm alt, +}^*(n)) = \mathbf{1}_{4 \nmid n}$, both having exact limiting mean $\frac{3}{4}$. Theorem A.2 at $k = 3$ ($\rho = \frac{1}{4}$) and $k = 4$ ($\rho = \frac{3}{16}$) gives the exact rational discrepancies and excluded orders.
2. For $E_{+, \rm odd}(2^k)$, every odd divisor $d \mid n$ has $n/d \equiv n \pmod 2$, so $(-1)^{n/d - 1} = (-1)^{n-1}$ factors out, yielding $a_{+, \rm odd}(n) = (-1)^{n-1} \tau_{\rm odd}(n)$ and $w_\pm(a_{+, \rm odd}(n)) = w_\pm(\tau_{\rm odd}(n))$. Applying Theorem A.2 with certified $W_{\rm odd}^{\rm maj}$ and $\mu_{\rm NAF}(\tau_{\rm odd})$ (§5 of the script) gives $k = 4$.
3. For $F_{2^k, +}(\tau_r)$, $a(n) = \sum_{d \mid n} \tau_{r-1}(d) (-1)^{n/d - 1}$ is multiplicative because $n/d$ is odd iff $v_2(d) = v_2(n)$: for odd $p$, $a(p^e) = \sum_{j=0}^e \binom{j+r-2}{r-2} = \binom{e+r-1}{r-1} = \tau_r(p^e)$; for $p = 2$, $a(2^e) = \binom{e+r-2}{r-2} - \sum_{j=0}^{e-1} \binom{j+r-2}{r-2} = \binom{e+r-2}{r-2} - \mathbf{1}_{e \ge 1}\binom{e+r-2}{r-1}$. At $r = 2^t$, $a(p) = 2^t$ has $w_\pm(a(p)) = 1$ for every odd prime $p$, and $|a(p^e)| \le \binom{e+r-1}{r-1} \le 2^{e+r-1}$ gives $w_\pm(a(p^e)) \le s_2(|a(p^e)|) \le e + r \le r(e+1)$. Outward-rounded Euler product certification (§5 of the script) yields the lowered thresholds $k \ge 4, 6, 8$. $\square$

---

## 4. Prior Art and Attribution

- **Non-Adjacent Form (NAF) and signed-digit arithmetic:**
  - **A. D. Booth (1951)** (*Quart. J. Mech. Appl. Math.* **4**, 236–240) introduced signed-digit recoding of binary runs.
  - **G. W. Reitwiesner (1960)** (*Binary arithmetic*, in *Advances in Computers*, Vol. 1, Academic Press, pp. 231–308) proved the fundamental existence, uniqueness, and minimal-Hamming-weight property of the Non-Adjacent Form (NAF) for every integer. Lemma A.1 supplies an elementary, Lean-aligned proof of Reitwiesner's theorem using `DigitMassTransfer.lean`'s kernel-verified `signedWeight` subadditivity as a repository input (so Reitwiesner 1960 is cited as foundational prior art rather than an unproved external black box).
  - **A. Avizienis (1961)** (*IRE Trans. Electron. Comput.* **EC-10**, 389–400) formalized redundant signed-digit systems; **W. Bosma (2001)** (*J. Théor. Nombres Bordeaux* **13**, 27–41) and **C. Heuberger & H. Prodinger (2001, 2006)** (*Computing* **66**, 377–393; *Monatsh. Math.* **147**, 219–248) established the classical asymptotic NAF density $\frac{1}{3}$ and exact fixed-length means: over **uniform NAF strings of length $\ell$**, the mean Hamming weight is $\frac{\ell}{3} + \frac{2}{9} + O(2^{-\ell})$ (whereas over uniform integers in $[0, 2^\ell)$, the mean is $\frac{\ell}{3} + \frac{4}{9} + O(2^{-\ell})$).
  - **Elementary Dirichlet-convolution cancellation:** Lemma C.1's splitting of a multiplicative function as $G = H * \mathbf{1}$ with squarefull-supported $H$ against bounded character sums is an instance of a classical elementary convolution technique in analytic number theory; its value here is applying it to the cubic-character majorants $G_\chi, U_\chi$ and the $y$-good indicator $\rho$ to obtain the $\frac{2}{3}$ phase factor without Selberg–Delange or Halász.
- **Irrationality and radix equivalence background:**
  - **P. Erdős (1948)** (*J. Indian Math. Soc.* **12**, 63–66) and **P. B. Borwein (1991, 1992)** (*J. Number Theory* **37**, 253–259; *Math. Proc. Cambridge Philos. Soc.* **112**, 141–146) proved irrationality (and non-Liouville behavior) of $E(q)$ and $E_+(q)$ for integers $q \ge 2$, without digit-distribution results.
  - **J. E. Maxfield (1953)** (*Pacific J. Math.* **3**, 189–196) proved equivalence of normality in bases $b$ and $b^k$. Our Theorems A.2, B.1, C.2, and C.3 establish nonnormality across bases $2^j$ directly via `radixDiscrepancy_descent` and multi-radix $2^s$ transfer without invoking Maxfield.
- **Repository lineage (including sibling Phase 25 Track D):**
  - Builds on Phase 23 [`GF-31`](../phase23/dense-characters-and-nonfundamental-forms.md) (cubic characters $L_\pm(2^k)$, odd-part method reaching $L_+(16)$ and $L_-(8)$ via Selberg–Delange, leaving $L_+(8)$ and $L_-(4)$ open), Phase 23 [`GF-32`](../phase23/binary-partition-and-carry-complexity.md) (carry-gauge signed representations), Phase 24 [`GF-36`](../phase24/dense-digit-mass-and-lambert.md) (`NormalityChecker/DigitMassTransfer.lean`, signed transition-count transfer Thm. 7.1 with threshold $\rho < \frac{1}{4}$, certified $W_+ \in [0.908174, 0.908184]$ and $W_+^{\rm maj} \in [0.936414, 0.936415]$ in Thm. 7.2, and cubic majorant means $W_\chi$ in Prop. 8.1), Phase 24 [`GF-40`](../phase24/classical-constants-and-joint-numerators.md) (certified $W_+ \in [0.907252, 0.912845]$ in Thm. 3.1(a) and 4-state free-boundary transducer in Thm. 3.2 proving $D^-(E_+(8); 2) \ge 2.34 \times 10^{-7}$), and [Phase 25 Track B](generalized-lambert-and-eplus.md) (circular Koksma boost to $1.4363 \times 10^{-5}$ and 7-state asymmetric transducer boost to $2.3643 \times 10^{-5}$).
  - **Sibling Phase 25 Track D ([`digit-complexity-and-lp-witnesses.md`](digit-complexity-and-lp-witnesses.md)):** Already establishes (i) the two-sided exact middle-interval formula $-2 \le 2\sigma_1(x; N) - K_{[1/6, 5/6)}(x; N) \le 1$ (Thm. 1.2), (ii) the universal base-2 discrepancy inequality $D^-(x; 2) \ge 2(\frac{1}{3} - \limsup \sigma_1/N)$ and series transfer (Thm. 2.3, Lemma 2.4), (iii) $D^-(E_+(8); 2) \ge \frac{17431}{300000}$ and $\ge 0.061210$, binary order-4 and base-8 order-2 nonnormality of $E_+(8)$, base-2 nonnormality ($D^- \ge 0.1620, 0.1303, 0.1404$) and binary order-4 nonnormality of $L_+(8)$ (mod $7, 9, 13$), and a Selberg–Delange-free proof of base-2 nonnormality of $L_-(8)$ (Thm. 2.5), (iv) the optimal-constant sandwich for $E_+(8)$ (Thm. 2.6), and (v) the exact $L$-normal signed-cost floor $\bar{g}_L = \frac{1}{3}(1 - 4^{-\lfloor L/2 \rfloor})$ for all $L$ with attainment for $L \le 10$ — including the identical block witness $B_m = (\mathtt{0001})^m(\mathtt{1110})^m$ for $L \in \{2, 3\}$ — and the sharp order-3 limitation (Thm. 1.7, §2.6). Track I independently re-derives the shared base-2 conclusions in finite-NAF geometric form without claiming priority over Track D.
- **Provisional novelty note:** Absence of a literature match does not establish priority (`docs/research-objectives.md`). Relative to both the external literature and sibling Phase 25 Track D, the provisional contributions unique to Track I are:
  1. the elementary twisted squarefull convolution proof of the $\frac{2}{3}$ phase factor (Lemma C.1), eliminating Selberg–Delange and Halász;
  2. the **first unconditional proof of nonnormality ($D^- > 0$, binary order-4 and base-4 order-2 nonnormality) of $L_-(4)$ ($k = 2$) for moduli $7, 9, 13, 19, 37$** (unreachable without the $\frac{2}{3}$ factor), together with the sharpened zero-external-input $L_-(8)$ bounds ($\approx 0.33, 0.31, 0.32$), base-2 order-2 and base-4/base-8 simple nonnormality of $L_-(8)$, and higher-moduli ($19, 37$) / base-4 order-2 extensions for $L_+(8)$;
  3. the direct multi-radix $2^s$ NAF geometric transfer (Theorem A.2), giving zero radix-descent loss in base $4$, **base-4 order-2 nonnormality of $E_+(8)$**, **base-4 and base-8 simple nonnormality of $E_+(2^k)$ lowered to $k \ge 4$**, and the general-$\ell$ ($\ell \ge 3$) tail-bound improvement at small $\rho < \frac{1}{6}$;
  4. the elementary DP-free squarefull coupled majorants $< \frac{93}{100}$ ready for Lean 4 (Theorem B.2); and
  5. the new signed dense Lambert families of Theorem C.3 ($E_+^*(8)$, $E_{\rm alt, +}^*(8)$, $E_{+, \rm odd}(16)$, $F_{2^k, +}(\tau_r)$).
  All provisional advances remain subject to independent human specialist review.

---

## 5. External Inputs and Hypothesis Verification Audit

| Result(s) in This Note | External Inputs Used | Verification / Notes |
| --- | --- | --- |
| **Lemma A.1, Theorem A.2** (NAF equivalence, general & multi-radix $2^s$ geometric transfer) | **None** | Elementary proof; Reitwiesner (1960) is reproved in Lemma A.1 (using kernel-verified `signedWeight_add_le`/`signedWeight_sub_le` in `DigitMassTransfer.lean` as a repository Lean input) and credited as prior art. |
| **Theorem B.1, Theorem B.2** ($E_+(2^k)$ bounds, base-4/8 simple nonnormality for $k \ge 4$, DP-free majorants $< 93/100$) | **None** | Pure `int`/`Fraction` independent re-certifications of Phase 24 `GF-40` Thm. 3.1(a) and `GF-36` Thm. 7.2 + elementary Wintner/independent-exponent model (`GF-36` Lemmas 3.1–3.2). |
| **Theorem B.3** (Independent NAF re-derivation of $m_1, \dots, m_4$, witnesses $x_*, x_4$, order-3 barrier; complements Track D Thm. 1.7) | **None** | Exact rational simplex LP relaxation + elementary closed-form canonical NAF constructions. |
| **Lemma C.1, Theorem C.2** (Twisted convolution $\frac{2}{3}$ factor; $L_-(4)$, $L_+(8)$, $L_-(8)$ mod $7, 9, 13, 19, 37$) | **None** | Eliminates Selberg–Delange and Halász via elementary bounded partial sums of nonprincipal $\chi$; pure `int`/`Fraction` Euler product & DP enclosures (re-certifying `GF-36` Prop. 8.1 + new $C_{\rm odd}, W_{\rm true}$, mod $19, 37$). |
| **Theorem C.3** ($E_+^*(8)$, $E_{\rm alt, +}^*(8)$, $E_{+, \rm odd}(16)$, $F_{2^k, +}(\tau_r)$) | **None** | Exact divisor identities + pure `int`/`Fraction` Euler products. |
| *Contextual comparison only* (`GF-31` Selberg–Delange, `GF-36` Senge–Straus non-dyadic barrier, Maxfield 1953) | Cited as context only; **not** used in any proof here | Senge–Straus (1973) remains the reason why non-power-of-$2$ bases (e.g. $E_+(3^k)$ in base $3$) stay outside this method. |

---

## 6. Evidence Labels and Scope Separation

- **`Paper proof` (no external inputs):** Lemma A.1 (with kernel-verified Lean repository input `signedWeight_add_le`/`signedWeight_sub_le`), Theorem A.2 (all four parts), Theorem B.3(1)–(4) (independent NAF proofs of $m_1, \dots, m_4$, $x_*$, $x_4$), Lemma C.1, and all algebraic reductions in Theorems B.1, B.2, C.2, C.3.
- **`Finite certificate` (exact `int`/`Fraction` only, zero floats):** All numerical enclosures and rational checks in [`scripts/phase25_naf_transfer.py`](../../scripts/phase25_naf_transfer.py) Sections 1–5 and 6a (**417,978 `[exact]`** and **104 `[encl]`** assertions).
- **`Finite measurement` (never asymptotic evidence):** Section 8.2 / script Section 6b (**9 `[finite]`** assertions on $N = 4000$-bit certified prefixes).
- **`Open`:** Base-2 simple normality of $E_+(8)$, $E_+(2^k)$ ($k \ge 3$), $L_+(8)$, $L_-(8)$, $L_-(4)$, $E_+^*(8)$, $E_{+, \rm odd}(16)$; base-4 simple normality of $L_-(4)$; attainment of $m_L = \bar{g}_L$ for $L > 10$; full normality and $D^- > 0$ for $E_+(4)$, $E(4)$, $E_{\rm odd}(4)$, $E^*(4)$, $E_+^*(4)$, $L_+(4)$, $L_-(4)$ (mod $31, 43$); and all unresolved benchmark constants `BC-01`…`BC-50` (including $E(2)$ `BC-37` and $E_+(2)$ `BC-39`).

---

## 7. Lean 4 Formalization Blueprint (Stage 3 Handoff)

*Status: uncompiled Lean 4 blueprint designed to sit on top of `NormalityChecker/BinaryDiscrepancy.lean` (`radixDiscrepancy`, l. 11), `NormalityChecker/DigitMassTransfer.lean` (`signedWeight`, `signedWeight_add_le`, `signedWeight_sub_le`, `tendsto_average_of_summable_conv_mobius`), `NormalityChecker/Phase22Cores.lean` (`erdosBorweinPlusCoeff`, l. 984; `erdosBorweinPlus_eq_sub`, l. 1345), and `NormalityChecker/HigherOrderTower.lean` (`OrderNormal`). Every algebraic identity and numerical bound below is already verified in `scripts/phase25_naf_transfer.py`. Builds run on `hail` (`AGENTS.md`).*

*Visibility note:* In `NormalityChecker/DigitMassTransfer.lean`, the five helpers `localBound` (l. 1629), `local_kernel_le` (l. 1399), `sum_Ico_inv_sq_le` (l. 1602), `prod_one_add_mul_le` (l. 1588), and `signedWeight_succ_le` (l. 478) are currently marked `private`. A separate `NormalityChecker/NafGeometricTransfer.lean` module therefore requires making those helpers public in `DigitMassTransfer.lean` (or co-locating the majorant certification inside `DigitMassTransfer.lean`). Also note that `Phase22Cores.lean` does not currently expose a named `erdosBorweinPlus` definition (it writes `∑' n : ℕ, (1 : ℝ) / ((b : ℝ) ^ (n + 1) + 1)` inline in `erdosBorweinPlus_eq_sub`), so we define `erdosBorweinPlus` explicitly below.

This formalization eliminates **all** automaton states, **all** transition tables, **all** circular Koksma bounds, and **all** dynamic programming to prove $D^-(E_+(8); 2) \ge \frac{7}{150}$ and `¬ OrderNormal 2 4 (erdosBorweinPlus 8)`:

```lean
-- 0. Explicit series definition (matching `Phase22Cores.erdosBorweinPlus_eq_sub`)
noncomputable def erdosBorweinPlus (b : ℕ) : ℝ :=
  ∑' n : ℕ, (1 : ℝ) / ((b : ℝ) ^ (n + 1) + 1)

-- 1. Canonical NAF & exact equivalence with existing `DigitMassTransfer.signedWeight` (Lemma A.1)
def nafDigits : ℤ → List Int  -- recursive via A % 2 and A % 4

def nafDigitAt (A : ℤ) (r : ℤ) : ℤ :=
  if 0 ≤ r then (nafDigits A).getD r.toNat 0 else 0

theorem nafDigits_val (A : ℤ) :
    (nafDigits A).enum.foldl (fun acc (r, d) => acc + d * 2 ^ r) 0 = A
theorem nafDigits_nonAdj (A : ℤ) (r : ℕ) (hr : r + 1 < (nafDigits A).length) :
    (nafDigits A)[r]! * (nafDigits A)[r + 1]! = 0
theorem signedWeight_parity_mono (q : ℕ) :
    signedWeight (2 * q) ≤ signedWeight (2 * q + 1) ∧
    signedWeight (2 * q + 2) ≤ signedWeight (2 * q + 1)
theorem nafWeight_eq_signedWeight (A : ℤ) :
    ((nafDigits A).filter (· != 0)).length = signedWeight A.natAbs

-- 2. Strict NAF tail bound & finite dyadic geometric bound (Theorem A.2(1); uses ℤ indices to avoid ℕ-subtraction truncation)
theorem naf_zero_block_tail_lt (A : ℤ) (M j ℓ : ℕ) (hj : j < M) (hℓ : 1 ≤ ℓ)
    (hz : ∀ t ∈ Finset.Icc 1 ℓ, nafDigitAt A ((M : ℤ) - j - t) = 0) :
    |∑ t ∈ Finset.Icc 1 (M - j), (nafDigitAt A ((M : ℤ) - j - t) : ℝ) / 2 ^ t|
      < (2 : ℝ) / (3 * 2 ^ ℓ)

theorem naf_dyadic_interval_count_le (A : ℤ) (M s r N : ℕ) (hs : 1 ≤ s) (hr : 1 ≤ r)
    (hN : s * N ≤ M) :
    ((Finset.range N).filter fun m =>
      (2 : ℝ) / (3 * 2 ^ (s * r)) ≤ Int.fract ((2 : ℝ) ^ (s * m) * ((A : ℝ) / 2 ^ M)) ∧
      Int.fract ((2 : ℝ) ^ (s * m) * ((A : ℝ) / 2 ^ M)) ≤ 1 - (2 : ℝ) / (3 * 2 ^ (s * r))).card
    ≤ r * signedWeight A.natAbs

-- 3. Universal real shadowing & series transfer (Theorem A.2(2)-(3), fixed-R form)
theorem frequency_naf_interval_le (x : ℝ) (s r R N : ℕ) (hs : 1 ≤ s) (hr : 1 ≤ r) (hR : 2 ≤ R)
    (hN : 0 < N) :
    frequency (shift (2 ^ s) x) ((2 : ℝ) / (3 * 2 ^ (s * r)) + (2 : ℝ)⁻¹ ^ R)
      (1 - (2 : ℝ) / (3 * 2 ^ (s * r))) N ≤
      (r : ℝ) * (signedWeight ⌊(2 : ℝ) ^ (s * N + R) * x⌋.natAbs : ℝ) / N

-- 4. DP-free {2,3,5}-coupled squarefull majorant < 93/100 (Theorem B.2;
--    requires exposing `localBound`, `local_kernel_le`, `sum_Ico_inv_sq_le`, `prod_one_add_mul_le`
--    in `DigitMassTransfer.lean`, or co-locating inside `DigitMassTransfer.lean`)
noncomputable def ePlusMajorant235 : ArithmeticFunction ℝ := ...
theorem signedWeight_erdosBorweinPlusCoeff_le (n : ℕ) :
    (signedWeight (erdosBorweinPlusCoeff n).natAbs : ℝ) ≤ ePlusMajorant235 n
theorem tsum_ePlusMajorant235_lt_93_div_100 :
    ∑' n : ℕ, (ePlusMajorant235 * (ArithmeticFunction.moebius : ArithmeticFunction ℝ)) n / n < 93 / 100

-- 5. Headline kernel-verified targets for E_+(8) and E_+(2^k) (`radixDiscrepancy` from `BinaryDiscrepancy.lean`)
theorem erdosBorweinPlus8_radixDiscrepancy_eventually_ge :
    ∀ᶠ N in Filter.atTop, (7 : ℝ) / 150 ≤ radixDiscrepancy 2 (erdosBorweinPlus 8) N
theorem erdosBorweinPlus8_not_orderNormal_four :
    ¬ OrderNormal 2 4 (erdosBorweinPlus 8)
theorem erdosBorweinPlus8_not_orderNormal_base4_two :
    ¬ OrderNormal 4 2 (erdosBorweinPlus 8)
theorem erdosBorweinPlus_two_pow_not_simplyNormal_base4 (k : ℕ) (hk : 4 ≤ k) :
    ¬ OrderNormal 4 1 (erdosBorweinPlus (2 ^ k))
theorem erdosBorweinPlus_two_pow_not_simplyNormal_base8 (k : ℕ) (hk : 4 ≤ k) :
    ¬ OrderNormal 8 1 (erdosBorweinPlus (2 ^ k))
```

*(Analogously, for cubic $L_-(4)$ mod $7, 9, 13$, Lemma C.1 reduces to standard Finset Dirichlet-convolution reindexing via `Finset.sum_comm` and `Nat.divisors` together with bounded partial sums of $\chi$, yielding `cubicMinus4_not_orderNormal_four` and `D_N(L_-(4); 2) ≥ 2/15` mod 7 and `≥ 8/75` mod 9, 13 without DP.)*

---

## 8. Exact Finite Certificates, Complete Tables, and Isolated Finite Measurements

### 8.1 Certified Quantitative Tables (`[encl]`, pure `int`/`Fraction` outward rounding)

**Table 8.1 (`[encl]`): $E_+(2^k)$ discrepancy and excluded normality order (all discrepancy lower bounds are computed from the unrounded certified upper endpoint of $W_+ \le 0.908184$ and rounded down; every $D^-(E_+(2^k); 2)$ strictly dominates `GF-36` Thm. 7.2 for all $k \ge 4$; compare Phase 25 Track D Thm. 2.5 at $k = 3, 4, 5$):**

| $k$ | $\rho = W_+/k \le$ | $D^-(E_+(2^k); 2) \ge$ [$\ell^*$] | `GF-36` / `GF-40` prior | $D^-(\cdot; 4) \ge$ [$r^*$] | $D^-(\cdot; 8) \ge$ | $D^-(\cdot; 2^k) \ge$ | Lowest excl. order ($b=2$) |
| --- | --- | --- | --- | --- | --- | --- | --- |
| $3$ ($E_+(8)$) | $0.302728$ | **$0.061211$** [$2$] | $2.34 \times 10^{-7}$ (`GF-40`) | **$0.061211$** [$1$] | **$0.026233$** | **$0.026233$** | **$L = 4$** (sharp!) |
| $4$ ($E_+(16)$) | $0.227046$ | **$0.212575$** [$2$] | $0.04590$ (`GF-36`) | **$0.212575$** [$1$] | **$0.152195$** | **$0.056686$** | **$L = 2$** (base-4 & 8 simple) |
| $5$ ($E_+(32)$) | $0.181637$ | **$0.303393$** [$2$] | $0.13672$ (`GF-36`) | **$0.303393$** [$1$] | **$0.288423$** | **$0.050150$** | $L = 2$ |
| $6$ ($E_+(64)$) | $0.151364$ | **$0.379241$** [$3$] | $0.19727$ (`GF-36`) | **$0.363938$** [$1$] | **$0.379241$** | **$0.070983$** | $L = 2$ |
| $8$ ($E_+(256)$) | $0.113523$ | **$0.492764$** [$3$] | $0.29590$ (`GF-36`) | **$0.462575$** [$2$] | **$0.492764$** | **$0.086608$** | $L = 2$ |
| $10$ | $0.090819$ | **$0.560878$** [$3$] | — | **$0.553393$** [$2$] | **$0.560878$** | **$0.090514$** | $L = 2$ |
| $16$ | $0.056762$ | **$0.689620$** [$4$] | $0.53443$ (`GF-36`) | **$0.689620$** [$2$] | **$0.663048$** | **$0.091796$** | $L = 2$ |
| $32$ | $0.028381$ | **$0.816429$** [$5$] | — | **$0.808882$** [$3$] | **$0.808882$** | **$0.091816$** | $L = 2$ |
| $64$ | $0.014191$ | **$0.894024$** [$6$] | — | **$0.894024$** [$3$] | **$0.894024$** | **$0.091816$** | $L = 2$ |

*(Note: in column $D^-(\cdot; 2^k)$, the table lists the best zero-external-input bound from Theorem A.2 and radix descent; Phase 25 Track B Theorem B2.1 gives $D^-(E_+(2^k); 2^k) \to 1$ as $k \to \infty$ using Halász 1968.)*

**Table 8.2 (`[encl]`): Cubic-character classifications $L_-(4)$, $L_+(8)$, and $L_-(8)$ (zero external inputs; all 6-digit discrepancy lower bounds are script-certified from the unrounded certified upper endpoints and rounded down, with base-8 bounds computed uniformly as $\max(\text{direct}, \text{descent})$):**

| Constant & Modulus | Certified mean input (`[encl]`) | $D^-(\cdot; 2) \ge$ | $D^-(\cdot; 4) \ge$ | $D^-(\cdot; 8) \ge$ | Excluded Normality Orders |
| --- | --- | --- | --- | --- | --- |
| **$L_-(4)$ mod $7$** *(NEW $D^- > 0$)* | $C_{\rm odd} < \frac{4}{5}$; $W_\chi \le 0.756905$; $W_{\rm true} \le 0.756872$ | **$0.162085$** ($0.162063$ [$W_\chi$]; $\ge \frac{2}{15}$) | **$0.162085$** ($0.162063$; $\ge \frac{2}{15}$) | **$0.076461$** ($0.076428$ [$W_\chi$]) | NOT $4$-normal (b=2), NOT $2$-normal (b=4) |
| **$L_-(4)$ mod $9$** *(NEW $D^- > 0$)* | $C_{\rm odd} < \frac{21}{25}$; $W_\chi \le 0.804516$; $W_{\rm true} \le 0.804479$ | **$0.130347$** ($0.130323$ [$W_\chi$]; $\ge \frac{8}{75}$) | **$0.130347$** ($0.130323$; $\ge \frac{8}{75}$) | **$0.055863$** ($0.055852$ [$W_\chi$]) | NOT $4$-normal (b=2), NOT $2$-normal (b=4) |
| **$L_-(4)$ mod $13$** *(NEW $D^- > 0$)* | $C_{\rm odd} < \frac{21}{25}$; $W_\chi \le 0.789314$; $W_{\rm true} \le 0.789162$ | **$0.140559$** ($0.140457$ [$W_\chi$]; $\ge \frac{8}{75}$) | **$0.140559$** ($0.140457$; $\ge \frac{8}{75}$) | **$0.060239$** ($0.060196$ [$W_\chi$]) | NOT $4$-normal (b=2), NOT $2$-normal (b=4) |
| **$L_-(4)$ & $L_+(8)$ mod $19, 37$** *(NEW)* | $W_{\chi_{19}} \le 0.774599$; $W_{\chi_{37}} \le 0.751172$ | **$0.150267$** / **$0.165885$** | **$0.150267$** / **$0.165885$** | **$0.064400$** / **$0.082161$** | NOT $4$-normal (b=2), NOT $2$-normal (b=4) |
| **$L_+(8)$ mod $7, 9, 13$** *(recovers Track D + b=4/8)* | Identical $\rho = W_\chi / 3$ (and $W_{\rm true}/3$) | **$0.162085$** / **$0.130347$** / **$0.140559$** ($0.162063$ / $0.130323$ / $0.140457$ [$W_\chi$]) | **$0.162085$** / **$0.130347$** / **$0.140559$** | **$0.076461$** / **$0.055863$** / **$0.060239$** ($0.076428$ / $0.055852$ / $0.060196$ [$W_\chi$]) | NOT $4$-normal (b=2), NOT $2$-normal (b=4) |
| **$L_-(8)$ mod $7, 9, 13$** *(sharpened, 0 ext.)* | $\rho = \frac{2}{9} W_{\chi, \rm true}$ (and $\frac{2}{9} W_\chi$) | **$0.330279$** / **$0.309120$** / **$0.315928$** ($0.330264$ / $0.309104$ / $0.315860$ [$W_\chi$]) | **$0.330279$** / **$0.309120$** / **$0.315928$** | **$0.328752$** / **$0.297014$** / **$0.307225$** ($0.328730$ / $0.296989$ / $0.307124$ [$W_\chi$]) | **NOT $2$-normal (b=2), simply nonnormal (b=4, 8)** |

**Table 8.3 (`[encl]`): DP-free squarefull majorants for $w_\pm(a_+(n))$:**

| Majorant | Primes explicitly multiplied | Tail bound used | Certified upper bound | $D^-(E_+(8); 2) \ge$ | Order-4 certified? |
| --- | --- | --- | --- | --- | --- |
| Pure multiplicative $G_0$ (re-certifies `GF-36` Thm. 7.2) | All odd primes (Euler product) | $\pm 1 \pmod 6$ | $0.936415 < \frac{15}{16}$ | $\frac{1}{24} \approx 0.04166$ | Yes ($\frac{2}{3} \cdot \frac{15}{16} = \frac{5}{8}$) |
| DP-free $G_{\{2,3\}}$ (mod-6 tail) | **45 primes** ($5 \le p \le 211$) | $\frac{1}{3(P-6)}$ | **$0.929153 < \frac{93}{100}$** | **$\frac{7}{150} = 0.04666\ldots$** | Yes ($0.62 < 0.625$) |
| DP-free $G_{\{2,3\}}$ (trivial tail) | 107 primes ($5 \le p < 601$) | $\frac{1}{P-1}$ (`sum_Ico_inv_sq_le`) | **$0.929681 < \frac{93}{100}$** | **$\frac{7}{150}$** | Yes ($0.62 < 0.625$) |
| DP-free $G_{\{2,3,5\}}$ (mod-6 tail) | **12 primes** ($7 \le p \le 47$) | $\frac{1}{3(P-6)}$ | **$0.924468 < \frac{93}{100}$** | **$\frac{7}{150}$** | Yes ($0.62 < 0.625$) |
| DP-free $G_{\{2,3,5\}}$ (trivial tail) | **26 primes** ($7 \le p \le 109$) | $\frac{1}{P-1}$ (`sum_Ico_inv_sq_le`) | **$0.928395 < \frac{93}{100}$** | **$\frac{7}{150}$** | Yes ($0.62 < 0.625$) |

### 8.2 Isolated Finite Measurements Only (`[finite]`; NEVER Asymptotic Evidence)

The following table from `scripts/phase25_naf_transfer.py` (§6b) records empirical statistics on certified $4000$-bit binary prefixes (with $64$-bit guard certification). **These are finite measurements only and prove nothing about asymptotic limits.**

| Series | $k$ | $f_{1, 4000}$ | $F_{4000}([\frac{1}{4}, \frac{3}{4}); \cdot, 2)$ | $F_{4000}([\frac{3}{16}, \frac{13}{16}); \cdot, 2)$ | $F_{2000}([\frac{3}{16}, \frac{13}{16}); \cdot, 4)$ | $w_\pm / 4000$ |
| --- | --- | --- | --- | --- | --- | --- |
| $E_+(8)$ | $3$ | $0.33075$ | $0.38050$ | $0.49025$ | $0.49200$ | $0.25950$ |
| $E_+(16)$ | $4$ | $0.30975$ | $0.30825$ | $0.41975$ | $0.42950$ | $0.22200$ |
| $E_+^*(8)$ | $3$ | $0.27750$ | $0.33000$ | $0.45550$ | $0.44850$ | $0.23250$ |
| $E_{+, \rm odd}(16)$ | $4$ | $0.52775$ | $0.32650$ | $0.53675$ | $0.55200$ | $0.28400$ |
| $L_+(8)$ mod $7$ | $3$ | $0.35450$ | $0.40125$ | $0.48750$ | $0.48900$ | $0.24900$ |
| $L_-(8)$ mod $7$ | $3$ | $0.58475$ | $0.23525$ | $0.32925$ | $0.33050$ | $0.16675$ |
| $L_-(4)$ mod $7$ | $2$ | $0.56800$ | $0.33350$ | $0.43850$ | $0.43100$ | $0.22950$ |
| $L_-(4)$ mod $9$ | $2$ | $0.41200$ | $0.36450$ | $0.47125$ | $0.46350$ | $0.24725$ |
| $L_-(4)$ mod $13$ | $2$ | $0.40450$ | $0.35750$ | $0.46600$ | $0.46350$ | $0.24150$ |

*(These values are recorded strictly as finite 4,000-bit prefix measurements and are never interpreted as asymptotic evidence.)*

---

## 9. Reproduction Instructions and Verification Record

Run the standalone verification script (Python 3.10+, standard library only, zero external packages):

```powershell
python -B scripts/phase25_naf_transfer.py
```

**Verified run record:**
- **Exit code:** `0` (elapsed ~28.7 s on Windows).
- **Total assertions passed:** **418,091**:
  - **417,978 `[exact]`** (canonical NAF value, non-adjacency, negation symmetry, `w_NAF = signedWeight`, and parity monotonicity across $A \in [-8192, 8192]$; brute-force minimality on $[-127, 127]$ over all $3^8 = 6{,}561$ distinct-exponent signed strings on 8 positions; 10,656 finite dyadic & multi-radix base-2/4/8 geometric bound checks on $A \in [-512, 512]$ plus special values $\pm(2^M \pm 1), \pm\lfloor(2^M-1)/3\rfloor, \pm\lfloor(2^{M+2}-1)/3\rfloor$ at $M \in \{8, 10\}$ including negative $A$, $|A| \ge 2^M$, carry wraparound, near-extremals, and tightness checks; exact `GF-36` dominance and unimodality crossovers; odd-integer telescoping checks and exact prime-count checks for 45, 107, 12, and 26 primes; exact rational LP solutions for $L = 1, 2, 3, 4$; irrational $3$-normal witness $x_*$ exact zero-overhead identity $w_\pm(\lfloor 2^{S_M} x_* \rfloor) = S_M/4$ through $M = 40$ ($S_{40} = 6560$) and $3$-word counts; $4$-normal de Bruijn witness $x_4 = 2479/65535$ through $m = 20$; exact $\mathbb{Z}[\omega]$ phase table, indicator identity, period zero-sums, and direct divisor convolutions for cubic characters mod $7, 9, 13$ through $n = 4096$; pointwise $G_{\{2,3\}}$ majorization through $n = 20{,}000$ and exact tail identities; exact $E_+^*, E_{\rm alt, +}^*, E_{+, \rm odd}, F_{2^k, +}(\tau_4)$ coefficient identities; and direct finite-$N$ shadowing on 10 series including negative $-E_+(8)$);
  - **104 `[encl]`** (independent pure-`Fraction` re-certification of Phase 24 `GF-40` Thm. 3.1(a) $W_+ \in [0.907252, 0.912845]$ with all three tail bounds explicitly asserted, and independent scaled-`int` re-certification of Phase 24 `GF-36` Thm. 7.2 $W_+ \in [0.908174, 0.908184]$; exact rational bounds $\frac{17431}{300000}$ and $\frac{11477}{187500}$ and $> 247{,}942\times$ / $> 261{,}201\times$ `GF-40` ratios; DP-free majorants $W_+^{\rm maj} \in [0.936414, 0.936415] < \frac{15}{16}$ and $G_{\{2,3\}}, G_{\{2,3,5\}} < \frac{93}{100}$; full $E_+(2^k)$ multi-radix table; cubic $C_{\rm odd}, W_\chi, W_{\chi, \rm true}$ enclosures mod $7, 9, 13$ — with tightened $W_{13} \le 0.789314$ and uniform $\max(\text{direct}, \text{descent})$ base-8 bounds — plus $W_\chi$, base-8 bounds, and base-2/base-4 order exclusions mod $19, 37$ and open checks mod $31, 43$; $E_{+, \rm odd}(16)$ and $F_{2^k, +}(\tau_r)$ enclosures; and honest open-boundary checks for $E_+(4), E_+^*(4), L_+(4)$);
  - **9 `[finite]`** (isolated 4,000-bit prefix sanity checks in Section 6b).

---

## 10. Explicit Open Questions and Standing Research Objectives Mapping

### 10.1 Standing Objectives Advanced ([`docs/research-objectives.md`](../../docs/research-objectives.md))

- **Objective 2 (Establish nonnormality):** **First unconditional proof of nonnormality ($D^- > 0$, NOT $4$-normal in base $2$, NOT $2$-normal in base $4$, hence nonnormal in every base $2^j$)** of the $k = 2$ cubic-character series **$L_-(4)$** (mod $7, 9, 13, 19, 37$); **base-4 order-2 nonnormality** of $E_+(8)$ and $L_+(8)$ (complementing Phase 25 Track D Thm. 2.5's binary order-4 nonnormality of $E_+(8)$ and $L_+(8)$ mod $7, 9, 13$, while adding mod $19, 37$); zero-external-input **base-2 order-2 nonnormality and base-4 / base-8 simple nonnormality** of $L_-(8)$ (mod $7, 9, 13$, sharpening Track D's Selberg–Delange-free nonnormality and recovering `GF-31` Thm. 4A without Selberg–Delange); **base-4 and base-8 simple nonnormality of $E_+(2^k)$ lowered to $k \ge 4$**; and new classifications of $E_+^*(8)$, $E_{\rm alt, +}^*(8)$, $E_{+, \rm odd}(16)$, and $F_{2^k, +}(\tau_r)$ ($k \ge 4, 6, 8$ for $r = 4, 8, 16$).
- **Objective 3 (Quantify digit distributions):** Independent pure-`int`/`Fraction` re-certifications recovering Track D Thm. 2.5's $D^-(E_+(8); 2) \ge \frac{17431}{300000}$ and $\ge \frac{11477}{187500} \approx 0.061211$ ($> 261{,}201\times$ `GF-40` and $> 2{,}588\times$ Track B), adding the matching zero-descent-loss base-4 bound $D^-(E_+(8); 4) \ge 0.061211$, $D^-(E_+(8); 8) \ge 0.026233$, and $\ell \ge 3$ improvements for $E_+(2^k)$ ($k \ge 6$); explicit $D^- > 0$ bounds for $L_-(4)$ ($\ge 0.162085, 0.130347, 0.140559 > \frac{2}{15}, \frac{8}{75}$ in bases $2, 4$ and $\ge 0.076461, 0.055863, 0.060239$ in base $8$), sharpened $L_-(8)$ bounds ($\ge 0.330279, 0.309120, 0.315928$), and the Theorem C.3 bounds ($E_+^*(8) \ge \frac{1}{6}$, $E_{+, \rm odd}(16) \ge 0.087720$, $F_{2^k, +}(\tau_r)$).
- **Objective 4 (Establish rigorous mathematical limitations):** Independently re-derives in canonical NAF language the $L \le 4$ cases ($m_1 = 0, m_2 = m_3 = \frac{1}{4}, m_4 = \frac{5}{16}$) of Phase 25 Track D Theorem 1.7's sharp order-3 barrier for signed-weight / NAF-density bounds above $\frac{1}{4}$ (including $E_+(8)$, $L_+(8)$, $L_-(4)$, and $E_+^*(8)$), and proves in Theorem B.2(1) the exact sharp floor $W_+^{\rm maj} \ge 0.936414$ (re-certifying `GF-36` Thm. 7.2) for any purely multiplicative majorant of $w_\pm(a_+)$.

### 10.2 Explicit Open Questions

1. **Base-2 simple normality and $3$-normality of $E_+(8)$, $L_+(8)$, and $L_-(4)$:** Both Phase 25 Track D Thm. 1.7 and Theorem B.3 prove that NAF weight alone cannot exclude $3$-normality (much less simple normality) of $E_+(8)$ or $L_-(4)$ whenever $\bar{w}_\pm \ge \frac{1}{4}$. Can an asymmetric signed-digit invariant (exploiting the fact that $a_+(n) > 0$ has density $\frac{1}{2}$ vs. $a_+(n) < 0$ density $\frac{1}{4}$) or carry-correlation structure exclude $3$-normality or simple normality of $E_+(8)$ in base $2$?
2. **Base-4 simple normality of $L_-(4)$ (mod $7, 9, 13$):** We proved $L_-(4)$ is NOT $2$-normal in base $4$ with $D^-(L_-(4); 4) \ge 0.162085$ (mod $7$). Can base-$4$ simple nonnormality of $L_-(4)$ be established (note that $2\rho = \frac{2}{3} W_\chi \approx 0.5046$ mod $7$ misses the $\frac{1}{2}$ threshold of $[1/4, 3/4)$ by just $0.0046$!)?
3. **$D^+(L_-(4); 2) < 1$ and $L_-(4) \notin K_2$:** Extending Phase 25 Track B's Signed Isolated-Odd-Arrival Theorem (Theorem B1.4) down to $k = 2$ for $L_-(4)$ and $k = 3$ for $E_+(8)$ to establish full double-sided $0 < D^- \le D^+ < 1$ remains **Open**.
4. **Remaining $k = 2$ boundary constants:** $E_+(4)$ ($W_+/2 \approx 0.454 > \frac{1}{3}$), $E_+^*(4)$ ($\frac{3}{8} > \frac{1}{3}$), $L_+(4)$ ($W_\chi/2 > \frac{1}{3}$), $L_-(4)$ modulo $31, 43$ ($W_\chi/3 > \frac{1}{3}$), $E(4)$, $E_{\rm odd}(4)$, and $E^*(4)$ remain **Open** for $D^- > 0$.
5. **Attainment of $m_L = \bar{g}_L$ for $L > 10$:** Phase 25 Track D Theorem 1.7 proves the lower bound $m_L \ge \bar{g}_L := \frac{1}{3}(1 - 4^{-\lfloor L/2 \rfloor})$ for **every** $L \ge 1$ and certifies attainment for all $L \le 10$ (matching Theorem B.3 for $L \le 4$). Does attainment $m_L = \bar{g}_L$ hold for every $L > 10$ (Track D's Question 2)?
6. **Stage 3 Lean 4 kernel verification on `hail`:** Formalize Section 7's DP-free, automaton-free blueprint (`NormalityChecker/NafGeometricTransfer.lean`, after exposing the five private helpers in `NormalityChecker/DigitMassTransfer.lean` or co-locating the majorant) to upgrade $D^-(E_+(8); 2) \ge \frac{7}{150}$, binary order-4 nonnormality of $E_+(8)$, and $D^-(L_-(4); 2) \ge \frac{2}{15}$ (mod $7$) / $\frac{8}{75}$ (mod $9, 13$) to **Kernel-verified** (`lean`).
