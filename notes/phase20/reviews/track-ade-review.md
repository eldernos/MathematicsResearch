# Independent Referee Report: Phase 20 Tracks A, B5, D, and E

**Reviewer:** Gemini 4 Argon (Cross-Provider Mathematical Referee)  
**Target Files Audited:**
- `notes/phase20/euler-product.md` (Tracks A1, A2, B5)
- `notes/phase20/theta-and-modular.md` (Tracks A3, A4)
- `notes/phase20/dense-and-partitions.md` (Tracks D1–D4)
- `notes/phase20/classical-transfers.md` (Tracks E1–E3)
- `NormalityChecker/EulerPentagonal.lean`, `NormalityChecker/CharacterLambertTransfer.lean`, and `NormalityChecker/CoefficientTransfer.lean`
- `scripts/phase20_euler_theta.py` and `scripts/phase20_dense_classical.py`

---

## Executive Summary & Track Verdicts

All four notes and their companion Lean 4 formalizations and verification scripts have been audited line-by-line for mathematical rigor, edge-case validity (including $b=2$ vs. $b\ge 3$, even vs. odd radices, primitive vs. imprimitive quadratic forms, and signed vs. nonnegative coefficients), and formal correspondence.

| Sub-Track | Subject | Verdict | Summary of Findings |
| :--- | :--- | :--- | :--- |
| **Track A1** | Euler's product $E_b = \prod_{k\ge 1}(1-b^{-k})$ | **ACCEPT (Verified)** | 0 Critical, 0 Major, 0 Minor. Exact block decomposition, all-prefix word frequency bounds, and the sharp asymptotic $1 - D_N(E_b; b) = \sqrt{2/3}\log_b N/\sqrt{N} + O_b(1/\sqrt{N})$ are completely rigorous for all $b \ge 2$. |
| **Track A2** | Powers $E_b^2$, $E_b^3$, polynomials, rational scalars | **ACCEPT (Verified)** | 0 Critical, 0 Major, 1 Minor. $E_b^3$ block digits, carry-free $4j$ embedding (disjunctivity), and $\sqrt{2}\log_b N/\sqrt{N} + O_b(1/\sqrt{N})$ asymptotic are airtight; $E_b^2 \leftrightarrow \eta(12\tau)^2$ ($V_4$ projective image, $\lambda = 3/4$) and the signed Phase 17 sieve lower bound are sound; rational scalar classification $(a/d)E_b \in K_b \iff a/d \in \mathbb Z[1/b]$ and limiting laws for $E_2/3, E_3/2$ are exact. One minor prose antecedent typo on line 258. |
| **Track B5** | Degree-$\le 2$ polynomials in unary quadratic series | **ACCEPT (Verified)** | 0 Critical, 0 Major, 0 Minor. Reduction of pairwise products $F_i F_j$ to shifted positive-definite diagonal binary forms $g(t,u) = Dm$ and $O(\log\log N/\sqrt{\log N})$ deficit rate via Bernays/Landau and coefficient transfer are complete. |
| **Track A3** | Binary theta values $\Theta_Q(1/b)$ | **ACCEPT (Verified)** | 0 Critical, 0 Major, 0 Minor. Primitive reduction $Q = gQ_0$, anisotropy modulo inert primes (both odd $p$ and $p=2$), lattice-point ellipse bounds, shifted-lattice completion of the square, rational translates, and bounded weights are all sound. |
| **Track A4** | Weight-1 modular forms & Serre's lacunary $\eta^{2r}$ | **ACCEPT (Verified)** | 0 Critical, 0 Major, 1 Minor. Every constituent in $M_1(\Gamma_1(M))$—both Deligne–Serre newforms and weight-1 Eisenstein series $E_1^{\psi,\varphi}$—is rigorously shown to be lacunary, and Corollary 2 with $A(X) \ll X\log X$ ($\beta=1$) properly handles Eisenstein series whose character ratio $\omega = \varphi\bar\psi$ has order $m \ge 4$ (where $A(X) \neq O(X)$). Minor remark on the schematic Lean signature `finite_sparse_logmass_transfer`. |
| **Track D1** | Carry-window transfer framework | **ACCEPT (Verified)** | 0 Critical, 0 Major, 0 Minor. Exact carry-window transfer (Lemma D1.1), certified polynomial and subexponential windows (Lemmas D1.2–D1.3), triangular coordinate freedom (Lemma D1.4), and the any-base positive coverage inequality $1-D_N \ge \min(\theta_N, \tfrac12-\tfrac1{2N}, b^{-3})$ (Lemma D1.5) are fully verified. |
| **Track D2** | Partition constant $P_b = 1/E_b$ | **ACCEPT (Verified)** | 0 Critical, 0 Major, 0 Minor. Elementary proof of $p(n) \le e^{\pi\sqrt{2n/3}}$, first-order window sharpness, pentagonal circle recurrence (Proposition D2.1), rate-conditional fixed-point exclusion (Proposition D2.2), and Ramanujan congruence wash-out (Proposition D2.3) are all sound. |
| **Track D3** | Sparse vs. dense theta/Eisenstein/eta rungs | **ACCEPT (Verified)** | 0 Critical, 0 Major, 0 Minor. All-base memberships (Theorem D3.1) and exact kernel transfers $\Theta^4 \equiv 16L_{\chi_4}^2 \pmod{K_b}$, $\Theta^3 \equiv 4\Theta L_{\chi_4} \pmod{K_b}$, and $\|D_N(\Theta_3(1/2)^4) - D_N(L_{\chi_4}^2)\| \le 1 - D_N(L_{\chi_4}) + 7/N$ are verified. |
| **Track D4** | Multiplication, squaring, and inversion in $K_b$ | **ACCEPT (Verified)** | 0 Critical, 0 Major, 0 Minor. Sumset criterion (Theorem D4.1), failure of squaring closure via $x = U+V$ (Proposition D4.2), radix-primary rational reciprocal test (Theorem D4.3), and the inductive construction of arbitrarily lacunary $z$ with $1-z \in K_2$ and $\liminf D_N(1/(1-z)) = 0$ (Theorem D4.4) are completely verified. |
| **Track E1** | Residue-class Lambert sums & character transfers | **ACCEPT (Verified)** | 0 Critical, 0 Major, 0 Minor. Mod-8, mod-24, and general 2-elementary quotient transfers (Theorems E1.1–E1.3) in both base 2 and general radices $b \ge 2$ for class differences are exact and match `CharacterLambertTransfer.lean`. |
| **Track E2** | Logarithmic Euler product & Möbius collapse | **ACCEPT (Verified)** | 0 Critical, 0 Major, 0 Minor. Truncation bound $\le \frac{16}{9}2^{-M}$ and the identity $\mu * \sigma_{-1} = \mathrm{id}^{-1}$ collapsing chronological prefixes to the Taylor prefixes of $\ln 2$ (Theorem E2.1) are exact. |
| **Track E3** | Normal syntheses & classical verdict | **ACCEPT (Verified)** | 0 Critical, 0 Major, 0 Minor. Sharp translation syntheses $\alpha_{b,c} + Z$ and scope limitations regarding transcendence and classical constants are accurate. |

---

## Detailed Mathematical Audit by Track

### 1. Track A1 (`notes/phase20/euler-product.md`, §§0–4)

1. **Exact base-$b$ digit expansion (Theorem 1 & Corollary 1):**
   - Pairing the positive pentagonal pair $2j$ ($a = P_{2j}^- = j(6j-1)$, $c = P_{2j}^+ = j(6j+1)$) with the negative pair $2j+1$ ($d = P_{2j+1}^- = 6j^2+5j+1$, $e = P_{2j+1}^+ = 6j^2+7j+2$) gives gaps $c - a = 2j$, $d - c = 4j+1$, $e - d = 2j+1$, and $a_{j+1} - e = 4j+3$.
   - The algebraic identity $1 - b^{-m} - b^{-n} = \sum_{i=1}^{m-1}(b-1)b^{-i} + (b-2)b^{-m} + \sum_{i=m+1}^n (b-1)b^{-i}$ ($1 \le m < n$) holds for all $b \ge 2$.
   - **Edge case $b = 2$:** When $b = 2$, $b - 2 = 0 \in \{0, 1\}$ and $b - 1 = 1 \in \{0, 1\}$. The head $1 - b^{-1} - b^{-2}$ has fractional digits $(b-2)(b-1)00 = 0100_2$, and each block $B_j = 1\,0^{2j}\,(b-1)^{4j}\,(b-2)\,(b-1)^{2j+1}\,0^{4j+2}$ has digits in $\{0, \dots, b-1\}$ with pairwise disjoint supports $[1, 4]$ and $[a_j, a_{j+1}-1]$. No carries or borrows occur across or within blocks, and infinitely many zeros prevent $(b-1)^\infty$ termination.
   - **Missing words (Corollary 1):**
     - For $b = 2$, the zero runs have lengths $1$ (at position $1$ and at $d = P_{2j+1}^-$), $2$ (at positions $3,4$), and $2j, 4j+2$ (inside $B_j$). Every zero run has length $1$ or even, so $1\,0^m\,1$ never occurs for odd $m \ge 3$.
     - For $b = 3$, $b - 2 = 1$ and $b - 1 = 2$; the digit $1$ occurs only at position $1$ (followed by $2$), at $a_j$ (flanked by $0$s), and at $d_j$ (flanked by $2$s). For $b \ge 4$, the digit $1$ occurs only at $a_j$ (flanked by $0$s). Hence $11$ is absent for all $b \ge 3$.

2. **All-prefix word frequency error bound (Theorem 2):**
   - Because every block $B_j$ begins with the digit $1$, neither zero runs nor $(b-1)$-runs ever merge across block boundaries (or across the head boundary at $a_1 = 5$).
   - In block $j$, the number of starts of $0^L$ is $g_j = (2j - L + 1)^+ + (4j + 3 - L)^+$ (plus $1$ if $b=2, L=1$). For $j \ge (L-1)/2$, $g_j - (12j+5)/2 = 1.5 - 2L$ (or $2.5 - 2L$), which has absolute value at most $2L$.
   - The smaller blocks $1 \le j < (L-1)/2$ contribute at most $\sum_{j \le (L-2)/2} (6j + 2.5) \le \frac{3}{4}L^2 + \frac{11}{4}L$, and the first four positions contribute at most $2$.
   - Within the active block $J$ containing $N$ (where $N \ge a_J - 1 = 6J^2 - J - 1 \implies J \le \sqrt{N/6} + 1/2$), the piecewise-linear excursion of $\Delta(N) = Z_w(N) - N/2$ is bounded by $2J + L + 1/2$ for $0^L$ and $2J + 1$ for $(b-1)^L$.
   - Summing these contributions yields $|\Delta(N)| \le (2L+2)\sqrt{N/6} + 0.75L^2 + 6.75L + 5.5 \le (2L+3)\sqrt{N/6} + 3L^2 + 5L + 7$ for all $L, N \ge 1$.
   - For $j \ge L/2$, constant words $0^L$ and $(b-1)^L$ account for $(6j + 4 - 2L) + (6j + 3 - 2L) = 12j + 7 - 4L$ of the $12j + 5$ block starts, leaving at most $4L - 2$ starts per block for all other words of length $L$, giving $Z_w(N) \le (4L-2)\sqrt{N/6} + 2L^2 + 12L + 4$.

3. **Sharp discrepancy asymptotic (Lemma 0 & Theorem 3):**
   - **Lemma 0(b) (Finite separation lemma):** Checked. If a half-open circle arc $J$ of length $\ell$ misses the closed ball $\{y : \|y\| \le \varepsilon\}$, it can only contain points with $\|x_n\| > \varepsilon$, so $\tfrac1N\#\{n < N : x_n \notin J\} + |J| \ge 1 - F_z(\varepsilon)/N$. If $J$ meets $\{y : \|y\| \le \varepsilon\}$, every point of $J$ lies within $\ell + \varepsilon$ of $0 \bmod 1$, so all $F_z(\ell + \varepsilon)$ points with $\|x_n\| > \ell + \varepsilon$ lie outside $J$, giving cost at least $\ell + F_z(\ell + \varepsilon)/N$.
   - **Upper bound:** Combining `discrepancy_deficit_le` with `sparse_farCount_le` (for $E_b - 1$ with $\varepsilon = 2b^{-w}$, $B = 1$) and $P(M) \le \sqrt{24M+1}/3$ at $w = \lceil \log_b \sqrt{N} \rceil + 1$ (so $4b^{-w} \le \frac{4}{b\sqrt{N}} \le \frac{2}{\sqrt{N}}$) yields $1 - D_N(E_b) \le \sqrt{\frac{2}{3}}\frac{\log_b N}{\sqrt{N}} + O_b\left(\frac{1}{\sqrt{N}}\right)$.
   - **Lower bound and $O_b(1/\sqrt{N})$ error term:** For $p > n$ the next pentagonal number, $r = p - n \ge 2$, and following gap $g \ge 2$, the tail after $p$ is bounded by $\frac{b}{b-1}b^{-r-g} \le 2b^{-r-g}$, so $b^{-r}(1 - 2b^{-g}) \ge b^{-r}/2$ and $b^{-r}(1 + 2b^{-g}) \le 3/8 < 1/2$. Thus $\|x_n\| \ge b^{-r}/2$ for **both** signs $s = \pm 1$. Every pentagonal number $p \le N$ with pair index $k \ge R$ has preceding gap $\ge 2R - 1 \ge R$ and following gap $\ge R$, giving $(P(N+1) - 2R)(R - 1)$ distinct far shifts in $[0, N)$. Optimizing the convex function $h(\ell) = \ell + \frac{M}{N}(\log_b \frac{1}{2(\ell+1/N)} - 2)$ at $\ell + 1/N = \frac{M}{N \ln b} \asymp \frac{1}{\sqrt{N}}$ directly recovers $\sqrt{\frac{2}{3}}\frac{\log_b N}{\sqrt{N}} - O_b\left(\frac{1}{\sqrt{N}}\right)$, avoiding the $O((\log\log N)/\sqrt{N})$ loss of fixed-threshold concentration bounds.

---

### 2. Track A2 & Track B5 (`notes/phase20/euler-product.md`, §§5–8)

1. **Cube $E_b^3$ (Theorem 7):**
   - **Exact digits and absence of borrow corruption:** For $j \ge 2$, pairing $k = 2j$ and $k = 2j+1$ in Jacobi's identity gives:
     $$G_j = (4j+1)b^{-T_{2j}} - (4j+3)b^{-T_{2j+1}} = 4j\,b^{-T_{2j}} + (b^{2j+1} - 4j - 3)b^{-T_{2j+1}}.$$
     For all $b \ge 2$ and $j \ge 2$, we have $4j < 4j+1 < 2^{2j} \le b^{2j}$ and $0 < b^{2j+1} - 4j - 3 < b^{2j+1}$, so $4j$ fits in the $2j$ digit positions $(T_{2j-1}, T_{2j}]$ and $b^{2j+1} - 4j - 3$ fits in the $2j+1$ digit positions $(T_{2j}, T_{2j+1}]$. Moreover, the head $k \le 3$ equals $1 - 3b^{-1} + 5b^{-3} - 7b^{-6} = (b^6 - 3b^5 + 5b^3 - 7)b^{-6}$, and $b^6 - 3b^5 + 5b^3 - 7 > 0$ for all $b \ge 2$ (at $b=2$ it is $64 - 96 + 40 - 7 = 1$; at $b=3$ it is $128$; for $b \ge 4$, $b^5(b-3) > 7$). Hence all blocks $G_j$ ($j \ge 2$) are positive and disjoint from the positive head at positions $\le 6$, so the base-$b$ expansion of $4j$ appears verbatim without carry or borrow corruption for every $b \ge 2$.
   - **Disjunctivity:** Prepending the digit $1$ to an arbitrary base-$b$ word $w$ to form the integer $W = (1w)_b$ protects leading zeros of $w$; for $b^t \ge 4$, $[Wb^t, (W+1)b^t)$ contains a multiple $4j$ of $4$, whose base-$b$ digits begin with $1w$ and appear verbatim in block $j$.
   - **Sharp asymptotic $\sqrt{2}\log_b N/\sqrt{N} + O_b(1/\sqrt{N})$:** Checked for both even and odd radices $b \ge 2$. In the lower bound, shifts $T_k - r$ with $w_k + 2 \le r \le k$ contribute $\sim \frac{1}{2}\log_b N$ far positions per $k$, while shifts $1 \le r \le w_k + 1$ reading the digits of $2k+1$ itself also contribute $\sim \frac{1}{2}\log_b N$ far positions per $k$ (for odd $b$, $2k+1 \bmod b^r$ hits each residue class at most $K/b^r + 1$ times over $K$ consecutive $k$; for even $b$, $2k+1 \bmod b^r$ hits only odd classes, at most $2K/b^r + 1$ times each, and at most $\tau b^r + 1$ odd classes lie within $\tau b^r$ of $0 \bmod b^r$, giving the same $O(K'(1 + t\log K'))$ bound on exceptional pairs).

2. **Square $E_b^2$ (Proposition 5 & Theorem 6):**
   - **Hecke eigenform & support criterion:** $\eta(12\tau)^2 = \sum_{n\ge 0} a_2(n) q^{12n+1} = \sum_{m\ge 1} c(m) q^m \in S_1(144, \chi_{-4})$ is a CM newform with projective Galois image $V_4 = D_2$ (split over $\mathbb Q(i, \sqrt{3})$), so $\lambda = 3/4$. Multiplicativity and the Hecke recursion $c(p^{e+1}) = c(p)c(p^e) - \chi_{-4}(p)c(p^{e-1})$ give $c(m) \ne 0 \iff v_p(m)$ is even for all $p \not\equiv 1 \pmod{12}$, and then $|c(m)| = \prod_{p\equiv 1\,(12)}(v_p(m)+1)$.
   - **Progression vs. full sum in Wirsing's theorem:** As noted on line 218, because $p^2 \equiv 1 \pmod{24}$ for all $p \ge 5$, every integer $m \ge 1$ in the support of $c$ automatically satisfies $m \equiv 1 \pmod{12}$, i.e. $m = 12n+1$. Thus $S_2(X) = \#\{m \le 12X+1 : c(m) \ne 0\} \asymp X/(\log X)^{3/4}$ and $A_2(X) = \sum_{m \le 12X+1} |c(m)| \asymp X/(\log X)^{1/2}$ follow directly from Wirsing's theorem on $\mathbb Z_{\ge 1}$.
   - **Validity of the Phase 17 sieve lower bound for signed $a_2(n)$:** Verified. At a good index $n$ (isolated at distance $J = \lceil C\log_b\log N \rceil$, with $1 \le |a_2(n)| \le (\log N)^{1/3}$ and tail $\tau_n \le 1/4$), the shift $n - r$ ($1 \le r \le J$) satisfies $\{b^{n-r}E_b^2\} \equiv b^{-r}(a_2(n) + \theta\tau_n) \pmod 1$ with $|\theta| \le 1$. Because $|a_2(n)| \ge 1$ and $\tau_n \le 1/4$, $|a_2(n) + \theta\tau_n| \in [3/4, (\log N)^{1/3} + 1/4]$ regardless of the sign of $a_2(n)$. For $\log_b(4(\log N)^{1/3}) \le r \le \log_b(1/(2t))$, this quantity lies in $[b^{-r}/2, 5/16] \subset (t, 1/2)$, so the two-sided circle distance satisfies $\|x_{n-r}\| > t$ for both positive and negative $a_2(n)$.

3. **Polynomials and rational scalars (Theorem 8):**
   - Verified. For $d_0 > 1$ coprime to $b$ and $(b-1)r \equiv 0 \pmod{d_0}$, $br \equiv r \pmod{d_0}$, so the integral head $I_n \bmod d_0$ is constant on each run between consecutive pentagonal numbers and jumps by $s_p = \pm 1 \not\equiv 0 \pmod{d_0}$ at each pentagonal number $p$. Thus no two adjacent runs can both occupy residue $r \bmod d_0$, bounding the upper density of $r$ by the alternating-gap weight $2/3 < 1$. The limiting measures for $E_2/3$ ($D_N \to 1/2$) and $E_3/2$ ($D_N \to 2/3$) are exact.

4. **Track B5 (Theorem 9):**
   - Verified. Every product $F_i F_j$ of unary quadratic series has exponents satisfying $Dm = g(t,u)$ for a shifted positive-definite diagonal binary quadratic polynomial $g(t,u)$, giving $S(X) \ll X/\sqrt{\log X}$ and $A(X) = O(X)$, hence $1 - D_N = O(\log\log N/\sqrt{\log N})$.

---

### 3. Track A3 & Track A4 (`notes/phase20/theta-and-modular.md`, §§1–4)

1. **Finite coefficient transfer with general mass (Lemma 1 & Corollary 2):**
   - Verified. For fixed $m > L$, the shifts $n < N$ with $m > n + L$ are $0 \le n < \min(N, m - L)$, and $\sum_{n < \min(N, m-L)} b^{n-m} < \frac{b^{\min(N, m-L) - m}}{b - 1} = \frac{b^{-L} b^{-(m-L-N)_+}}{b - 1}$. Corollary 2 cleanly absorbs any logarithmic mass growth $A(X) \ll X(\log X)^\beta$ by setting $L = \lceil (2\kappa + \beta)\log_b\log N \rceil + 1$.

2. **Binary quadratic theta values (Lemmas 3–4, Theorem 5, Proposition 6, §2.2):**
   - **Imprimitive vs. primitive forms:** Writing $Q = gQ_0$ with $g = \gcd(a, b_0, c)$ and $\Delta_0 = \Delta/g^2$ reduces $B_Q(X) = B_{Q_0}(X/g)$ to the primitive case.
   - **Anisotropy modulo inert primes:** For odd $p$ with $(\Delta_0/p) = -1$, primitivity prevents $p \mid a_0, c_0$ simultaneously (which would force $\Delta_0 \equiv b_{00}^2 \pmod p$), so completing the square via $4a_0 Q_0$ or $4c_0 Q_0$ shows $p \mid Q_0(m,n) \implies p \mid m, n$. For $p = 2$, $(\Delta_0/2) = -1 \iff \Delta_0 \equiv 5 \pmod 8$, forcing $a_0, b_{00}, c_0$ all odd, so $Q_0(m,n) \equiv m^2 + mn + n^2 \pmod 2$ is anisotropic over $\mathbb F_2$.
   - **Shifted lattices (§2.2):** Completing the square via $U = 2cl_1 - b_0l_2$, $V = 2al_2 - b_0l_1$ gives $|\Delta|^2 f(m,n) = Q(|\Delta|m + U, |\Delta|n + V) + E_0$ with $|\Delta| = 4ac - b_0^2 > 0$. Checked.

3. **Weight-1 modular forms (Theorem 7 = Theorem B):**
   - **Completeness across all constituents of $M_1(\Gamma_1(M))$:** Every $f \in M_1(\Gamma_1(M))$ is a finite linear combination of oldforms $g(t\tau)$ of weight-1 newforms $g$ and weight-1 Eisenstein series $E_1^{\psi,\varphi}(t\tau)$ with $\psi\varphi$ odd.
     - For every newform $g$, Deligne–Serre gives an odd irreducible Artin representation $\rho : \mathrm{Gal}(\bar{\mathbb Q}/\mathbb Q) \to \mathrm{GL}_2(\mathbb C)$ with finite image $G$; complex conjugation has eigenvalues $\pm 1$ (trace $0$), so Chebotarev gives a positive prime density $\delta_0(g) \ge 1/4$ where $a_g(p) = 0$, killing all odd prime powers $a_g(p^{2e+1}) = 0$ by the Hecke recursion.
     - For every weight-1 Eisenstein series $E_1^{\psi,\varphi}$, the divisor-sum coefficients $\sigma(n) = (\psi * \varphi)(n)$ are multiplicative with $\sigma(p^k) = \psi(p)^k \sum_{i=0}^k \omega(p)^i$ for $p \nmid M$, where $\omega = \varphi\bar\psi$ satisfies $\omega(-1) = \varphi(-1)\psi(-1) = -1$ and hence has **even** order $m \ge 2$. On the prime set $\{\omega(p) = -1\}$ of Dirichlet density $1/m > 0$, all odd prime powers vanish: $\sigma(p^{2e+1}) = 0$.
     - Therefore, **every** basis element of $M_1(\Gamma_1(M))$ is lacunary with support $\ll X/(\log X)^{\alpha_i}$ ($\alpha_i > 0$), and because a finite union of lacunary supports is lacunary with exponent $\alpha_f = \min_i \alpha_i > 0$, no non-lacunary weight-1 modular form exists.
   - **Handling $A(X) \not\ll X$ when $m \ge 4$:** As shown in §3, Eisenstein series with character-ratio order $m \ge 4$ have $\mathbb E|1 + \omega(p)| > 1$ and $A(X) \asymp X(\log X)^{\mathbb E|1+\omega|-1} \ne O(X)$, which integer-coefficient combinations of Galois-conjugate Eisenstein series can inherit. Using $|a_f(n)| \le C_f \tau(n) \implies A_f(X) \ll X \log X$ and applying Corollary 2 with $\beta = 1$ handles all such forms without requiring $A(X) = O(X)$.

4. **Serre's lacunary $\eta^{2r}$ overlap obstruction (§4):**
   - Verified. For $r \in \{4, 6, 8, 10, 14, 26\}$ (weight $k = r/2 \ge 2$), $S(X) \asymp X/\sqrt{\log X}$ is lacunary, but typical split-prime coefficients have size $p^{(k-1)/2}$, occupying a radix footprint of $\frac{k-1}{2}\log_b m$ digits—much wider than the average support gap $\asymp \sqrt{\log m}$.

---

### 4. Tracks D1–D4 (`notes/phase20/dense-and-partitions.md`, §§1–4)

1. **Track D1 (Carry-window transfer):**
   - **Lemmas D1.1–D1.4:** Checked. The tail estimates for polynomial growth ($|a(m)| \le Cm^k$) and subexponential growth ($|a(m)| \le C e^{\alpha\sqrt{m}}$ via concavity $\sqrt{n+j} \le \sqrt{N} + j/(2\sqrt{N})$) are exact, and coordinate freedom via the last triangular coordinate $v_L(n) = a(n+L) \bmod b^L$ is immediate.
   - **Lemma D1.5 (Any-base positive coverage $1 - D_N(x) \ge \min(\theta_N, \tfrac12 - \tfrac1{2N}, b^{-3})$):** Checked. The circle distance from the unequal-top-two-digit set $U_b$ to $F_b = \{c/(b-1)\}$ is at least $g_b = \frac{1}{b^2(b-1)}$. If an arc $J$ of length $l < b^{-3} = g_b \frac{b-1}{b}$ contains more than $\frac{N+1}{2}$ orbit points, the pigeonhole principle forces two consecutive orbit points $x_n, x_{n+1} \in J$ ($0 \le n \le N-2$). Then the arc midpoint $c$ satisfies $\|(b-1)c\| \le \frac{(b+1)l}{2}$, placing $J$ inside a ball of radius $\frac{bl}{b-1} < g_b$ around some fixed point $f \in F_b$, so $J \cap U_b = \emptyset$ and $1 - \mu_N(J) \ge \theta_N$.

2. **Track D2 (Partition constant $P_b = 1/E_b$):**
   - **Elementary upper bound $p(n) \le e^{\pi\sqrt{2n/3}}$:** From $1 - q^j \ge jq^{j-1}(1-q)$ one has $\frac{q^j}{1-q^j} \le \frac{q}{j(1-q)}$, so $\log P(q) \le \frac{\pi^2}{6}\frac{q}{1-q} \le \frac{\pi^2}{6t}$ for $q = e^{-t}$; choosing $t = \pi/\sqrt{6n}$ gives $p(n) \le e^{nt} P(e^{-t}) \le e^{\pi\sqrt{2n/3}}$ for all $n \ge 1$ (and $p(0) = 1$).
   - **Propositions D2.1–D2.3:** Checked. In Proposition D2.2, the partial sum $s_n = \sum_{0 < g_k \le n} \varepsilon_k$ follows the cycle $1, 2, 1, 0$ across the four intervals $[P_{2j-1}^-, P_{2j-1}^+)$, $[P_{2j-1}^+, P_{2j}^-)$, $[P_{2j}^-, P_{2j}^+)$, $[P_{2j}^+, P_{2j+1}^-)$ of lengths $2j-1, 4j-1, 2j, 4j+1$, so $\{n : s_n = 0\}$ has density $\lim_{j\to\infty} \frac{4j+1}{12j-1} = \frac{1}{3}$. Averaging $\|(1-s_n)c\| \le |\delta_n| + \sum_{g_k \le n} |\delta_{n-g_k}| + |\rho_n|$ over $\{n < N : s_n = 0\}$ shows that $M_N(P_b - c) = o(N^{-1/2})$ forces $\|c\| = 0$.

3. **Track D3 (Sparse rungs and exact modulo-$K_b$ transfers):**
   - **Theorem D3.1 & exact transfers:** Checked. In §3.2, $\Theta_3(1/b)^2 = 1 + 4L_{\chi_4}(b)$ yields $\Theta_3(1/b)^4 = 1 + 8L + 16L^2 \equiv 16L^2 \pmod{K_b}$ and $\Theta_3(1/b)^3 = \Theta + 4\Theta L \equiv 4\Theta L \pmod{K_b}$. In base $b = 2$, combining integer invariance (dropping $1$), sharp translation by $8L = 2^3 L$ (cost $\le 1 - D_N(8L) \le 1 - D_N(L) + 3/N$), and multiplication of $L^2$ by $16 = 2^4$ (cost $\le 4/N$) gives $|D_N(\Theta_3(1/2)^4) - D_N(L_{\chi_4}^2)| \le 1 - D_N(L_{\chi_4}) + 7/N$.

4. **Track D4 (Products, squaring, and reciprocals in $K_b$):**
   - **Theorem D4.1 & Proposition D4.2 ($x = U + V \in K_b$ with $x^2 \notin K_b$):** Checked. For all $b \ge 2$ and $r \ge 2$, $A+A$ has base-4 digits in $\{0,1,2\}$ so $\#((A+A)\cap[0,X]) \asymp X^{\log 3/\log 4} = o(X)$ and $U^2, V^2 \in K_b$. Meanwhile $2UV = 2b^r/(b^r-1)$ has reduced denominator $(b^r-1)/\gcd(2, b^r-1)$, which is coprime to $b$ and strictly exceeds $b - 1$ for every $b \ge 2, r \ge 2$ (including odd $b \ge 3, r = 2$, where $\frac{b^2-1}{2} = \frac{b+1}{2}(b-1) \ge 2(b-1) > b-1$).
   - **Theorem D4.3 & Corollary (Radix-primary reciprocal test):** Checked. For $b \ge 3$ and $m_K \ge 2$, $Q = b^{m_K}(1-z) \ge \frac{(b-2)b^2+1}{b-1} = (b-1) + \frac{b(b-1)(b-2)}{b-1} > b-1$, so $Q \mid b-1$ holds iff $M = \{1\}$.
   - **Theorem D4.4 (Arbitrarily lacunary $z$ with $1-z \in K_2$ and $\liminf D_N(1/(1-z)) = 0$):** Checked in full detail. At stage $k$, choosing $m = m_k$ divisible by $\operatorname{ord}_{Q^J}(2)$ ($Q = Q_{k-1}$ odd, $J = kQ$) collapses the geometric expansion of $y' = 1/(1 - z_{k-1} - 2^{-m})$ on each band $I_j = [jm, (j+1)m - L)$ modulo $1$ to the purely periodic orbit $2^n u_j / Q^{j+1}$ with $\gcd(u_j, Q) = 1$, up to $e_n \le 2^{j+3-L}$. Because $Q$ is odd, the subgroup $\langle h \rangle$ generated by $h = 2^{\operatorname{ord}_Q(2)}$ contains the full congruence subgroup modulo $\tilde{M}_j = \gcd(M, Q^{j+1})$ in $(\mathbb Z/Q^{j+1}\mathbb Z)^\times$ where $M = \prod_{p\mid Q} p^{v_p(h-1)} < 2^Q$, decomposing each cycle into arithmetic progressions of step $\tilde{M}_j/Q^{j+1} \le \min(1, M/Q^{j+1})$. Averaging over the $J = kQ$ bands gives $D_{N_k}(1/(1-z)) \le \frac{\log_Q M + 2}{J} + o(1) \le \frac{2}{k} + o(1) \to 0$.

---

### 5. Tracks E1–E3 (`notes/phase20/classical-transfers.md`, §§1–3) & Lean Statement Correspondence

1. **Track E1 (Residue-class Lambert sums):**
   - **Mod-8 and mod-24 identities (Theorems E1.1–E1.2):** Checked against `CharacterLambertTransfer.lean`.
   - **General 2-elementary quotient (Theorem E1.3):** When $G/H = (\mathbb Z/q\mathbb Z)^\times / H \cong (\mathbb Z/2\mathbb Z)^k$, the difference weight $\psi = \mathbf 1_{gH} - \mathbf 1_{g'H}$ and the scaled weight $\psi' = 2^k \mathbf 1_{gH} - \mathbf 1_{(m,q)=1}$ are both **integer-valued** and expand as linear combinations of real nonprincipal characters $\chi$ trivial on $H$. Since each $1 * \chi \ge 0$ has $A(X) = O(X)$ and $S(X) \ll X/\sqrt{\log X}$, both $A_{gH}(b) - A_{g'H}(b)$ and $2^k A_{gH}(b) - E_q(b)$ lie in $K_b$ in **every** base $b \ge 2$ with deficit $O(\log\log N/\sqrt{\log N})$. Converting $D_N(2^k A_{gH}(b))$ to $D_N(A_{gH}(b))$ uses $2^k \in b^{\mathbb Z}$ (in particular $b = 2$).

2. **Track E2 (Logarithmic Euler product & Möbius collapse):**
   - **Truncation error:** From $\sigma_{-1}(n) \le n$, $F(q) \le \frac{q}{(1-q)^2}$, so for $M \ge 1$, $\sum_{m > M} F(2^{-m}) \le \frac{2^{-M}}{(1 - 2^{-M-1})^2} \le \frac{16}{9}2^{-M}$.
   - **Theorem E2.1:** Since $\sigma_{-1} = 1 * \mathrm{id}^{-1}$, Dirichlet convolution with $\mu$ yields $\mu * \sigma_{-1} = \mathrm{id}^{-1}$, so collecting $mn = K \le N$ in $\sum_m \mu(m) F(2^{-m})$ gives the exact Taylor prefix $\sum_{K\le N} 2^{-K}/K$ of $\ln 2$, inheriting the Phase 19 period barrier verbatim.

3. **Track E3 (Normal syntheses & classical verdict):**
   - Verified.

4. **Lean Statement Correspondence (`EulerPentagonal.lean`, `CharacterLambertTransfer.lean`, `CoefficientTransfer.lean`):**
   - Every Lean theorem cited in the four markdown files matches the actual formal declarations in `NormalityChecker/`:
     - `EulerPentagonal.eulerPentagonal_discrepancy_tendsto_one`, `eulerPentagonal_preserves_discrepancy`, `eulerPentagonal_finite_gap_upper`, `eulerCube_discrepancy_tendsto_one`, `eulerCube_preserves_discrepancy`, `jacobiCube_absMass_le`, `cauchyConv_absMass_le`.
     - `CharacterLambertTransfer.radixDiscrepancy_mul_pow_sub_le`, `discDist_sum_intMul_le`, `radix_pow_linear_transfer`, `mod8_character_identities`, `mod8_odd_discrepancy_diff`, `mod8_class_discrepancy_diff`, `mod8_asymptotic_equivalence`.
     - `CoefficientTransfer.finite_sparse_mass_transfer`, `linear_mass_sparse_tendsto_one`, `one_sub_discrepancy_ge_of_bulk_and_far`.

---

## Findings Classification

### Critical Findings
- **None.**

### Major Findings
- **None.**

### Minor Findings

1. **`notes/phase20/euler-product.md` (Line 258 — Track A2 prose antecedent typo):**
   - *Text:* "Every binary word of length at most 10 already occurs in the first $2^{20}$ digits of $E_2^3$, which contain only 90 distinct words of length 12."
   - *Issue:* The count `90` is the number of distinct binary words of length 12 in $E_2$ (as stated in Corollary 1, line 111, and printed by `scripts/phase20_euler_theta.py`, line 715: `E_2 has 90 distinct words of length 12 there`), not in $E_2^3$ (which contains all $2^{10} = 1024$ binary words of length 10 and therefore at least $1024$ words of length 12).
   - *Fix:* Clarify the relative clause to "...whereas $E_2$ contains only 90 distinct words of length 12 there."

2. **`notes/phase20/theta-and-modular.md` (Lines 208–214 — Track A4 schematic Lean signature `finite_sparse_logmass_transfer`):**
   - *Issue:* In the recommended future Lean signature `finite_sparse_logmass_transfer`, the Markov tail term is written as `C * (N + L + 2) * (Real.log (N + L + 2)) ^ β / (N * ε * (b : ℝ) ^ L)`. When $\beta > 0$, summing $((M + k)\log^\beta(M + k + 2))/b^{L+1+k}$ over $k \ge 0$ incurs a constant factor $C_\beta > 1$ from the growth of $\log^\beta(M+k+2)$ along the geometric tail (for $\beta = 0$ this reduces to `weighted_geom_bound` with factor $1$).
   - *Fix:* When formalizing `finite_sparse_logmass_transfer` in Lean (e.g., for $\beta = 1$), include an explicit factor of $2$ in the tail numerator (using $\log(M+k+2) \le (k+1)\log(M+2)$ for $M \ge 1$).
