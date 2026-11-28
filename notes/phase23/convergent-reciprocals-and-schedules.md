# Phase 23 Track D: Convergent Reciprocal Discrepancy, Exact $L$-Normal Nonnormal Reciprocals, and Relaxed Non-Tetration Schedules

**Notation.** Fix an integer radix $b \ge 2$. For $x \in \mathbb{R}$ and $N \ge 1$, let
$$\mu_N^{\mathrm{emp}}(x; b) := \frac{1}{N} \sum_{n=0}^{N-1} \delta_{\{b^n x\}}, \qquad D_N(x; b) := \sup_{0 \le u < v \le 1} \left|\mu_N^{\mathrm{emp}}(x; b)\big([u, v)\big) - (v - u)\right|$$
be the empirical orbit measure on $\mathbb{T} = \mathbb{R}/\mathbb{Z}$ and extreme interval discrepancy (on $[0, 1)$) of $x$ in base $b$, with liminf and limsup discrepancies $D^-(x; b) := \liminf_{N\to\infty} D_N(x; b)$ and $D^+(x; b) := \limsup_{N\to\infty} D_N(x; b)$. Following the repository's standing definitions (`notes/phase21/euler-scalings-and-reciprocals.md`, `notes/phase22/normal-reciprocals-and-signs.md`, `NormalityChecker/RadixPowerTower.lean`, and `docs/results.md` GF-23), we write
$$K_b := \left\{x \in \mathbb{R} : \lim_{N\to\infty} D_N(x; b) = 1\right\}$$
for the numerical translation kernel and
$$M_b := \left\{x \in \mathbb{R} : \lim_{N\to\infty} \frac{1}{N} \sum_{n=0}^{N-1} \|b^n x\|_{\mathbb{T}} = 0\right\} = \left\{x \in \mathbb{R} : \mu_N^{\mathrm{emp}}(x; b) \xrightarrow{W_1} \delta_0 \text{ on } \mathbb{T}\right\} \subset K_b$$
for the zero-orbit subgroup. Weak\* limits of $\mu_N^{\mathrm{emp}}(x; b)$ are taken on $\mathbb{T} = \mathbb{R}/\mathbb{Z}$ unless $[0, 1]$ is specified explicitly. For a rational $r = A/D \in \mathbb{Q}$ with $\gcd(b, D) = 1$, let $\mu(r; b)$ denote the uniform probability measure on the finite periodic orbit $\{b^t r \bmod 1 : 0 \le t < \operatorname{ord}_D(b)\}$ and $D(\mu(r; b))$ its extreme interval discrepancy. A real number $y$ is **$L$-normal** in base $b$ ($L \ge 1$) if every length-$L$ word $w \in \{0, \dots, b - 1\}^L$ has asymptotic frequency $f_w(y; b) = b^{-L}$; for $L = 1$ this is simple normality. We write $e(t) := e^{2\pi i t}$, $\|t\|_{\mathbb{T}} := \min(\{t\}, 1 - \{t\})$, $W_1(\mu, \nu)$ for the $1$-Wasserstein metric on $\mathbb{T} = \mathbb{R}/\mathbb{Z}$, and $\operatorname{rad}^*(n) := \prod_{p \mid n} p$ if $4 \nmid n$ and $2 \prod_{p \mid n} p$ if $4 \mid n$.

---

## Main results

This note executes **Phase 23 Track D (sub-tracks D1, D2, and D4)**, advancing the reciprocal discrepancy and schedule program of Phase 21 (`notes/phase21/euler-scalings-and-reciprocals.md`) and Phase 22 (`notes/phase22/normal-reciprocals-and-signs.md`) in three directions:

1. **Theorem 1 (Sub-track D1 — Rational-orbit inversion, exact convergent reciprocal discrepancy, and $Q(1) = 1$ coefficient excess identity).**
   - *(Exact convergent inversion.)* Let $r = A/D \in \mathbb{Q}_{>0}$ be reduced with $\gcd(b, A D) = 1$ and $2 \in \langle b \rangle \pmod{D}$ (which forces $D$ odd, holds for **all** odd $D \ge 1$ when $b = 2$, and for $D \ge 2$ in general holds if and only if $D \mid (2 b^L - 1)$ for some $L \ge 1$). Set $P := \operatorname{lcm}(\operatorname{ord}_A(b), \operatorname{ord}_D(b))$, and choose any positive integer sequence $(m_j)_{j \ge 1}$ with $P \mid m_1$, $2 m_j \mid m_{j+1}$, and $m_{j+1} / (2 m_j) \to \infty$ (for instance the non-tetration schedule $m_j = 2^j j! P$). Then
     $$x := \frac{1}{r} \prod_{j=1}^{\infty} (1 + b^{-m_j})^{-1}, \qquad y := \frac{1}{x} = r \prod_{j=1}^{\infty} (1 + b^{-m_j})$$
     are irrational, $x$ satisfies $\mu_N^{\mathrm{emp}}(x; b) \xrightarrow{W_1} \delta_0$ on $\mathbb{T}$ and $\lim_{N\to\infty} D_N(x; b) = 1$ (so $x \in M_b \subset K_b$), while its reciprocal $y = 1/x$ converges along **all** $N$ to the exact periodic orbit $\mu(r; b)$:
     $$\mu_N^{\mathrm{emp}}(1/x; b) \xrightarrow{W_1} \mu(r; b), \qquad \lim_{N \to \infty} D_N(1/x; b) = D(\mu(r; b)), \qquad \lim_{N \to \infty} f_w(N; 1/x, b) = \mu(r; b)(C_w)$$
     for every word $w \in \{0, \dots, b - 1\}^L$ ($L \ge 1$).
   - *(Base-$2$ dense exact convergent spectrum.)* In base $b = 2$, every nontrivial periodic binary word $w$ (rotated to end in $1$) is realized as $r = v(w) / (2^{|w|} - 1)$. Consequently, the set of exact convergent reciprocal discrepancies $\mathcal{A}_{\mathrm{conv}}(2) := \{\alpha \in [0, 1] : \exists\, x \in K_2 \setminus \mathbb{Q},\ \lim_{N\to\infty} D_N(1/x; 2) = \alpha\}$ is **dense in $[0, 1]$**.
   - *(All-base universal repunit inversion and arbitrarily localized intervals.)* For **every** radix $b \ge 2$ and every reduced $r = A/D \in \mathbb{Q}_{>0}$ with $\gcd(b, A D) = 1$, replacing $1 + q$ by the base-$b$ repunit polynomial $Q_b(q) := (1 - q^b)/(1 - q) = \sum_{s=0}^{b-1} q^s$ and taking $P \mid m_1$, $b m_j \mid m_{j+1}$, $m_{j+1}/(b m_j) \to \infty$ gives irrational $x = \frac{1}{r} \prod_{j \ge 1} Q_b(b^{-m_j})^{-1}$ with $\mu_N^{\mathrm{emp}}(x; b) \xrightarrow{W_1} \delta_0$ on $\mathbb{T}$ and $\lim_{N\to\infty} D_N(x; b) = 1$ ($x \in M_b \subset K_b$) such that every weak\* limit point of $\mu_N^{\mathrm{emp}}(1/x; b)$ is a convex combination of $\mu(r; b), \mu(2 r; b), \dots, \mu((b - 1) r; b)$. In particular, for every $b \ge 2$, every $\alpha \in (0, 1)$, and every $\varepsilon > 0$, there exists an irrational $x \in M_b \subset K_b$ with $[D^-(1/x; b), D^+(1/x; b)] \subseteq [\alpha - \varepsilon, \alpha + \varepsilon]$.
   - *($Q(1) = 1$ coefficient excess identity.)* For any $L \ge 2$ and any polynomial $Q \in \mathbb{Z}[q]$ dividing $(1 - q^L)/(1 - q)$ with $Q(0) = Q(1) = 1$ and $\deg Q \ge 1$, writing $(1 - q^L) / ((1 - q) Q(q)) = \sum_{i=0}^{L-1} S_i q^i$ yields the exact excess identity $\sum_{S_i \ge 2} (S_i - 1) = \#\{i < L : S_i = 0\} + \sum_{S_i \le -1} (1 - S_i) \ge \deg Q \ge 1$, forcing $\max_{0 \le i < L} S_i \ge 2$.

2. **Theorem 2 (Sub-track D2 — Exact sharp maximum discrepancy of $L$-normal numbers).**
   For every radix $b \ge 2$ and every word length $L \ge 1$, the sharp supremum of $D^+(y; b)$ over all base-$b$ $L$-normal numbers $y \in \mathbb{R}$ is
   $$D_{\max}(b, L) := \sup\big\{D^+(y; b) : y \text{ is } L\text{-normal in base } b\big\} = 2 b^{-L}.$$
   Moreover, the value $2 b^{-L}$ is **attained** as an exact convergent limit $\lim_{N\to\infty} D_N(y; b) = 2 b^{-L}$ by an explicit $L$-normal real number (and every $\alpha \in [0, 2 b^{-L}]$ is realized as $\lim_{N\to\infty} D_N(y; b) = \alpha$ for an $L$-normal $y$), constructed via Eulerian circuits of the loop-deleted de Bruijn digraph $G_{b, L}^*$ and the affine discrepancy identity $D((1 - t)\lambda + t \sigma) = t D(\sigma)$ for all $t \in [0, 1]$ and Borel probability measures $\sigma$ on $[0, 1)$.

3. **Theorem 3 (Sub-track D2 — Simultaneous $L$-normality / word frequencies and discrepancy on reciprocals of $K_b$, resolving Phase 22 Open Problem #5).**
   - *(Base $2$: dense $L$-normal spectrum and prescribed rational word distributions.)* For every $L \ge 1$, the set of exact convergent discrepancies $\lim_{N\to\infty} D_N(1/x; 2)$ attained by irrational $x \in M_2 \subset K_2$ whose reciprocal $1/x$ is **$L$-normal** in base $2$ is **dense in $[0, 2^{1 - L}]$**. Likewise, for every $L \ge 1$ and every rational flow-consistent length-$L$ word probability distribution $\mathbf{p}$ on $\{0, 1\}^L$ whose support digraph on $\{0, 1\}^{L-1}$ is connected and which assigns positive mass to words containing both $0$ and $1$ (in particular every rational $0$-digit frequency $p_0 = a / q \in (0, 1)$), there exists an irrational $x \in M_2 \subset K_2$ whose reciprocal $1/x$ has exact limiting word frequencies $\mathbf{p}$ and exact convergent discrepancy $\lim_{N\to\infty} D_N(1/x; 2) \in (0, 1)$.
   - *(All bases $b \ge 2$, all $L \ge 1$: unconditional resolution of Phase 22 Open Problem #5.)* For **every** radix $b \ge 2$ and **every** $L \ge 1$, the refined Markov digraph $\mathcal{G}_{b, M}$ on $M := \operatorname{lcm}(1, \dots, b - 1) \cdot b^L$ vertices produces an explicit rational $r = A / (b^P - 1)$ with $\gcd(A, b) = 1$ whose periodic orbit satisfies strict cell interiority $u_n / M < \{b^n r\} < (u_n + 1) / M$ for all $n$ and exact $L$-normality of **every** multiple $s r$ ($1 \le s \le b - 1$). Feeding $r$ into universal repunit inversion yields an irrational $x \in M_b \subset K_b$ whose reciprocal $1/x$ is **exact $L$-normal along all $N$** yet **nonnormal** with strictly positive discrepancy
     $$0 < \frac{2}{b M} - O_{b, L}\!\left(\frac{\log_b R}{R}\right) \le D^-(1/x; b) \le D^+(1/x; b) \le 2 b^{-L}.$$
     At $L = 1$, this unconditionally resolves Phase 22 Open Problem #5 (simply normal nonnormal reciprocals of $x \in K_b$) in every base $b \ge 2$.
   - *(Primitive-root convergent $L$-normal reciprocals and quadratic-reciprocity obstruction.)* Whenever $p = k b^L + 1$ is prime with $\operatorname{ord}_p(b) = p - 1$, $r = 1/p$ yields exact $L$-normality and exact convergent discrepancy $\lim_{N\to\infty} D_N(1/x; b) = 2/p$ (requiring $2 \in \langle b \rangle \pmod p$, automatic since $b$ is a primitive root). Conversely, quadratic reciprocity completely obstructs the existence of such primes whenever $b \equiv 0, 1 \pmod 4$ (for all $L \ge 1$) or $b \equiv 2 \pmod 4$ with $L \ge 3$, demonstrating that the refined Markov digraph construction is strictly more general.
   - *($R_0 = 1$ obstruction.)* No pure $R_0 = 1$ signed or cyclotomic reciprocal product with a weak\* limit point $(1 - \gamma)\lambda + \gamma \delta_0$ ($\gamma > 0$) on $\mathbb{T}$ can be $L$-normal whenever $(b, L) \neq (2, 1)$, because $f_{0^L} + f_{(b-1)^L} = 2 b^{-L} + \gamma(1 - 2 b^{-L}) > 2 b^{-L}$.

4. **Theorem 4 (Sub-track D4 — Bang–Zsigmondy rigidity and Hull–Dobell reciprocal schedules).**
   - *(Rigidity.)* For every integer $b \ge 2$ and all integers $m, n \ge 1$,
     $$\operatorname{rad}^*(b^m - 1) \mid (b^n - 1) \iff m \mid n$$
     with **zero exceptions** (explicitly verifying the Zsigmondy exceptions $m = 1$; $m = 2$ with $b + 1 = 2^t$; and $(b, m) = (2, 6)$).
   - *(Characterization and normality.)* Consequently, for the all-minus product $y = \prod_{k \ge 1} (1 - b^{-m_k})^{-1}$ with $D_k = \prod_{j=1}^k (b^{m_j} - 1)$, the Hull–Dobell divisibility condition **(HD1)** $\operatorname{rad}^*(D_{k-1}) \mid (b^{m_k} - 1)$ ($\forall k \ge 2$) holds if and only if $m_{k-1} \mid m_k$ for all $k \ge 2$, together with $2 \mid m_k$ for all $k \ge 3$ whenever $b \equiv 3 \pmod 4$ (because if $m_1, m_2$ are odd then $4 \mid D_2$ forces $4 \mid (b^{m_3} - 1)$, hence $2 \mid m_3$). Under **(HD1)** and **(HD2)** $T_{k-1} / m_k \to 0$ (where $T_k = m_k D_{k-1}$ by Lemma 3.2), $y$ is base-$b$ normal with $x = 1/y \in M_b \subset K_b$ (in the full-limit sense) and all-prefix Weyl bound
     $$|W_h(N)| \le \frac{\gcd(h, D_{K-2})}{D_{K-2}} + \frac{2 T_{K-1} + 3 c_b(h)}{m_K} \qquad (N \in [m_K, m_{K+1})).$$
   - *(Growth forced by the sufficient conditions (HD1)–(HD2).)* Even when $D_{k-1} \nmid (b^{m_k} - 1)$ strictly, **(HD1)** forces $m_{k-1} \mid m_k$, so $(b^{m_{k-1}} - 1) \mid (b^{m_k} - 1)$ and $S_i(b^{m_k}) \equiv i + 1 \pmod{b^{m_{k-1}} - 1}$. Independently, combining **(HD1)**'s period $T_k = m_k D_{k-1}$ with the sufficient hypothesis **(HD2)** ($T_{k-1} / m_k \to 0$) forces eventual tetration growth $m_k > T_{k-1} = m_{k-1} D_{k-2} \ge \frac{1}{2} b^{m_{k-2}}$ for all sufficiently large $k \ge k_0$. This restricts the proof method of Theorem 4; normality of slower-growing Hull–Dobell products violating **(HD2)** is not addressed.

5. **Theorem 5 (Sub-track D4 — Anchored coprime non-tetration normal reciprocals in every base $b \ge 2$).**
   Fix any base $b \ge 2$. Let $s_b := 1$ if $b \ge 4$ and $b \not\equiv 3 \pmod 4$, and $s_b := 2$ otherwise ($b \in \{2, 3\}$ or $b \equiv 3 \pmod 4$). Fix any positive multiple $s$ of $s_b$, set $M := b^s - 1 \ge 3$ (so $\operatorname{rad}^*(M) \mid M$ and $4 \mid M$ whenever $2 \mid M$), and define $m_k = s q_k$ recursively by choosing $q_1 \ge 5$ with $\gcd(q_1, s M) = 1$ and
   $$q_k := \omega_{k-1} \frac{T_{k-1}}{s} + 1 \qquad (k \ge 2), \qquad T_k := s M^{k-1} \prod_{j=1}^k q_j,$$
   with integer parameters $\omega_k \ge 1$ satisfying $s M \mid \omega_1$, $s \mid \omega_{k-1}$ ($k \ge 3$), and $\omega_k \to \infty$ (equivalently $m_k = \omega_{k-1} T_{k-1} + s$). Then:
   - *(Exact coprime period and CRT grid.)* $D_k = M^k \prod_{j=1}^k \widetilde{d}_j$ where $\widetilde{d}_j := (b^{m_j} - 1) / M$ are pairwise coprime and coprime to $M$, $\operatorname{ord}_{D_k}(b) = T_k$, $\widehat{C}_k(h) = 0$ whenever $M^{k-1} \nmid h$, and $D(\mu(R_k; b)) \le M^{-(k-1)}$.
   - *(Normality and all-prefix Weyl bound.)* $x = \prod_{k \ge 1} (1 - b^{-m_k}) \in M_b \subset K_b$ (in the full-limit sense: $\frac{1}{N} \sum_{n < N} \|b^n x\|_{\mathbb{T}} \to 0$ and $\lim_{N\to\infty} D_N(x; b) = 1$) and $y = 1/x$ is **base-$b$ normal** with
     $$|W_h(N)| \le \frac{\gcd(h, M^{K-2})}{M^{K-2}} + \frac{T_{K-1} + s + 3 c_b(h)}{m_K} \qquad (N \in [m_K, m_{K+1})).$$
   - *(Non-tetration doubly-exponential growth and arbitrary polylogarithmic discrepancy.)* With the balanced choice $\omega_k = s M^k$, the schedule is **doubly exponential (no tetration)**: $\ln T_k = (c_* + o(1)) 2^k$ for a constant $c_* = c_*(b, s, q_1) > 0$, $x$ satisfies $1 - D_N(x; b) = O_{b,s}(N^{-1/2})$ uniformly for all $N \ge 2$, and for each fixed admissible seed $q_1$, $y = 1/x$ achieves
     $$D_N(y; b) = O_{b, s, q_1}\!\left(\frac{(\ln\ln N)^{\omega(M) + 1}}{(\ln N)^{\log_2 M}}\right).$$
     For each fixed base $b \ge 2$ and $A > 0$, choosing the least multiple $s$ of $s_b$ with $\log_2(b^s - 1) > A$ and the least admissible seed $q_1 \ge 5$ ($\gcd(q_1, s M) = 1$) yields a base-specific non-tetration normal reciprocal $1/x$ ($x = x(b, A) \in M_b \subset K_b$) with $D_N(1/x; b) = O_{b, A}((\ln N)^{-A})$.

6. **Theorem 6 (Sub-track D4 — Fully coprime base-$2$ CRT convolution, prime-exponent products, and complete-period exponential equidistribution of the partial products $R_k^{(E)}$).**
   - *(Universal $01$-transition bound and prime-exponent product.)* For any pairwise coprime sequence $(m_j)_{j \ge 1}$ of integers $\ge 2$ in base $2$, $T_k = \prod_{j=1}^k m_j$ and $\mu(R_k; 2) = \nu_1^{(k)} * \cdots * \nu_k^{(k)}$, where every non-trivial character satisfies $|\widehat{\nu_j^{(k)}}(h)| \le 1 - (2 - \sqrt{2}) / m_j$ whenever $(2^{m_j} - 1) \nmid h$. For the prime-exponent product $R_k^{(\mathrm{prime})} = \prod_{j=1}^k (1 - 2^{-p_j})^{-1}$, divergence of $\sum 1/p_j$ immediately implies $\mu(R_k^{(\mathrm{prime})}; 2) \Rightarrow \lambda$ and $D(\mu(R_k^{(\mathrm{prime})}; 2)) \to 0$.
   - *(Fully coprime all-prefix normality and complete-period sub-exponential discrepancy.)* For the fully coprime base-$2$ schedule $m_1 = 2$, $m_k = \omega_{k-1} T_{k-1} + 1$ ($k \ge 2$) with $\omega_1 \ge 2$ and $\omega_k \to \infty$, the CRT measures $\nu_j$ are independent of $k \ge j$, the partial-fraction residues satisfy the exact real identity $a_k^{(k)} / (2^{m_k} - 1) = \{-R_{k-1}\} + R_{k-1} / (2^{m_k} - 1)$ ($k \ge 2$), and both $|\widehat{C}_k(h)|$ and the band $L^2$ energy $E_k(h) := T_k^{-1} \sum_{a < T_k} |\widehat{C}_k(h(2^a - 1))|^2$ obey the squaring inequalities
     $$|\widehat{C}_k(h)| \le |\widehat{C}_{k-1}(h)|^2 + \frac{c_2(h)}{m_k}, \qquad E_k(h) \le E_{k-1}(h)^2 + \frac{7}{\omega_{k-1}} + \frac{4 c_2(h)}{m_k}.$$
     Hence $y = \prod_{k \ge 1} (1 - 2^{-m_k})^{-1}$ is **base-$2$ normal along all prefixes $N$** (with $x = 1/y \in M_2 \subset K_2$ in the full-limit sense), and for $\omega_k = 2^k$ the complete-period discrepancies break the iterated-logarithm barrier with **sub-exponential decay** $D(\mu(R_k; 2)) = O(\exp(-c_0 (\ln T_k)^{1/4}))$.
   - *(Ordinary partition partial products $R_k^{(E)} = \prod_{j=1}^k (1 - b^{-j})^{-1}$ in every base $b \ge 2$.)* Let $p$ be an anchor prime with $s_b := \operatorname{ord}_p(b)$ for odd $p$ and $s_b := \operatorname{ord}_4(b)$ for $p = 2$ ($p = 3, s_2 = 2$ for $b = 2$; $p = 2, s_b \in \{1, 2\}$ for odd $b \ge 3$; any odd prime $p \mid (b - 1)$ with $s_b = 1$ for even $b \ge 4$), and set $e_0 := v_p(b^{s_b} - 1)$. Factoring $D_k = \prod_{j=1}^k (b^j - 1) = p^{e_k} D'_k$ ($p \nmid D'_k$) with $T'_k := \operatorname{ord}_{D'_k}(b)$ and $T_p := \operatorname{ord}_{p^{e_k}}(b)$, we have $v_p(T'_k) \le \lfloor \log_p k \rfloor$ unconditionally while $e_k \ge e_0 \lfloor k / s_b \rfloor$, yielding the exact $p$-adic arithmetic-progression grid bound
     $$D\big(\mu(R_k^{(E)}; b)\big) \le p^{-r_k} \le C_b \cdot k \cdot p^{-e_0 k / s_b} \longrightarrow 0,$$
     where $r_k := \max(0,\, v_p(T_p) - v_p(T'_k))$ except for $p = 2, b \equiv 3 \pmod 4$, where the sign coset in $(\mathbb{Z}/2^e\mathbb{Z})^\times$ gives $r_k := \max(0,\, v_2(T_p) - \max(1,\, v_2(T'_k)))$.

### Evidence and status table

| Result | Sub-track | Evidence label | Verification anchor / dependencies |
|---|---|---|---|
| Theorem 1 (Rational-orbit $+1$-inversion, base-$2$ dense $\mathcal{A}_{\mathrm{conv}}(2)$, all-base repunit localization, $Q(1)=1$ excess identity) | D1 | `Paper proof` | `Finite certificate`: `scripts/phase23_reciprocals_v2.py` §1 (1,482 substantive exact checks; helper invariants excluded) |
| Realizing every irrational $\alpha \in (0, 1)$ as exact $\lim_{N\to\infty} D_N(1/x; b) = \alpha$ ($x \in K_b$) | D1 | `Open` | Open Problem #1 (§8) |
| Theorem 2 ($D_{\max}(b, L) = 2 b^{-L}$ sharp ceiling, attainment, affine mixture across $[0, 2 b^{-L}]$) | D2 | `Paper proof` | `Finite certificate`: `scripts/phase23_reciprocals_v2.py` §2 (125 substantive exact checks) |
| Theorem 3 (Base-$2$ dense $L$-normal spectrum; **all-base $b \ge 2, L \ge 1$ unconditional resolution of Phase 22 Open Problem #5** via $\mathcal{G}_{b, Q b^L}$; primitive-root $2/p$ implication & QR obstruction; $R_0 = 1$ obstruction) | D2 | `Paper proof` | `Finite certificate`: `scripts/phase23_reciprocals_v2.py` §3 (3,732 substantive exact checks; 11 finite prime examples for Thm 3(c), infinitude in unobstructed classes is an open Artin-type question) |
| Theorem 4 (Bang–Zsigmondy rigidity $\operatorname{rad}^*(b^m-1)\mid(b^n-1) \iff m \mid n$, Hull–Dobell normality & growth forced by (HD1)–(HD2)) | D4 | `Paper proof` + `External input` (Bang 1886; Zsigmondy 1892) | Depends on Phase 22 Theorem 2 (band-averaging framework); `Finite certificate`: `scripts/phase23_reciprocals_v2.py` §4 (2,343 substantive exact checks) |
| Theorem 5 (Anchored coprime non-tetration normal reciprocals for all $b \ge 2$, $\ln T_k \sim c_* 2^k$, $D_N = O_{b,A}((\ln N)^{-A})$) | D4 | `Paper proof` | `Finite certificate`: `scripts/phase23_reciprocals_v2.py` §5 (4,431 substantive exact checks) |
| Theorem 6 (Fully coprime base-$2$ CRT convolution, prime product $\mu(R_k^{(\mathrm{prime})}) \Rightarrow \lambda$, all-prefix normality + complete-period $O(\exp(-c_0 (\ln T_k)^{1/4}))$, exponential complete-period equidistribution of $R_k^{(E)}$ in all $b \ge 2$) | D4 | `Paper proof` | `Finite certificate`: `scripts/phase23_reciprocals_v2.py` §6 (80 substantive exact checks) |
| Normality of ordinary partition constant $P_b = 1/E_b$ (short-orbit gap $N \ll T_k$) | D4 | `Open` | Schedule bridge §5.5 & Open Problem #3 |

Floating-point orbit discrepancies, Weyl-sum checks, and growth-constant audits in `scripts/phase23_reciprocals_v2.py` (Sections 1b, 2a for $P > 120$, 3a for $P > 100$, 5a Weyl checks, 5c, and 6a–6c; 510 floating-point checks total) are **finite measurements (not evidence)** supporting sanity checks of the proofs, never proof substitutes. Cross-model review is not independent human peer review.

---

## 1. Sub-track D1: Convergent Reciprocal Discrepancy for $x \in K_b$

Phase 22 (`notes/phase22/normal-reciprocals-and-signs.md`, Theorem 6) realized every oscillating discrepancy interval $[D^-(1/x; b), D^+(1/x; b)] = [0, \alpha]$ ($\alpha \in [0, 1]$) with $x \in K_b$ by alternating $+1$ or cyclotomic factors with double $-1$ reset factors. Because the $-1$ resets repeatedly collapsed the $\delta_0$ mass back to $0$, the resulting reciprocal discrepancy always satisfied $D^-(1/x; b) = 0$. To obtain **convergent** intermediate limits $\lim_{N\to\infty} D_N(1/x; b) = \alpha \in (0, 1)$, we invert the construction: start from a rational seed $r = A/D$ carrying the desired target orbit $\mu(r; b)$, and dress $1/r$ by an infinite product of inverse $+1$-factors (or repunit factors) that drives $x$ cleanly into $M_b \subset K_b$ while locking $y = 1/x$ onto the exact periodic orbit $\mu(r; b)$.

### 1.1 Discrepancy stability under bounded-transport perturbation

Because $\mu(r; b)$ is purely atomic, weak\* convergence $\mu_N \Rightarrow \mu(r; b)$ alone does not automatically guarantee $D(\mu_N) \to D(\mu(r; b))$ without ruling out boundary wrap-around at $0/1$. The following elementary lemma handles this cleanly with zero separation hypothesis beyond staying away from the endpoints $0$ and $1$.

**Lemma 1.1 (Discrepancy stability for interior $W_\infty$-perturbations).** *Let $\mu$ and $\nu$ be Borel probability measures on $[0, 1)$. Suppose $\nu = (1 - \eta)\tilde{\nu} + \eta \nu_{\mathrm{err}}$ for some $\eta \in [0, 1]$ and Borel probability measures $\tilde{\nu}, \nu_{\mathrm{err}}$ on $[0, 1)$ such that there is a coupling $\pi$ of $(\mu, \tilde{\nu})$ supported on $\{(u, v) \in [0, 1)^2 : |u - v| \le \delta\}$. Then*
```math
\big|D(\nu) - D(\mu)\big| \le 2\delta + \eta.
```

*Proof.* Let $I = [u, v) \subseteq [0, 1)$ be any interval, and define $I^+ := [\max(0, u - \delta), \min(1, v + \delta))$ and $I^- := (u + \delta, v - \delta)$ (empty if $v - u \le 2\delta$). Whenever $(a, c) \in \operatorname{supp}(\pi)$, $|a - c| \le \delta$ implies both ($c \in I \Rightarrow a \in I^+$) and ($a \in I^- \Rightarrow c \in I$). Hence $\mu(I^-) \le \tilde{\nu}(I) \le \mu(I^+)$. Since $|I^+| \le |I| + 2\delta$ and $|I^-| \ge |I| - 2\delta$ (and $D(\mu) = \sup_{0 \le a < b \le 1} |\mu((a, b)) - (b - a)|$ by approximating $(a, b) = \bigcup_{\varepsilon \downarrow 0} [a + \varepsilon, b)$),
```math
\nu(I) - |I| = (1 - \eta)\tilde{\nu}(I) + \eta \nu_{\mathrm{err}}(I) - |I| \le \mu(I^+) - (|I^+| - 2\delta) + \eta \le D(\mu) + 2\delta + \eta,
```
```math
|I| - \nu(I) \le |I| - (1 - \eta)\mu(I^-) \le (|I^-| + 2\delta) - \mu(I^-) + \eta \le D(\mu) + 2\delta + \eta.
```
Thus $D(\nu) \le D(\mu) + 2\delta + \eta$. Reversing the roles of $\mu$ and $\tilde{\nu}$ in the same coupling gives $(1 - \eta)\mu(I) \le (1 - \eta)\tilde{\nu}(I^+) \le \nu(I^+)$ and $\nu(I^-) \le \tilde{\nu}(I^-) + \eta \le \mu(I) + \eta$, whence $D(\mu) \le D(\nu) + 2\delta + \eta$. $\square$

### 1.2 Proof of Theorem 1 (Rational-orbit $+1$-inversion)

Let $r = A/D \in \mathbb{Q}_{>0}$ be reduced with $\gcd(b, A D) = 1$ and $2 \equiv b^{s_0} \pmod D$ for some $s_0 \ge 0$ (which automatically forces $D$ odd). Set $P := \operatorname{lcm}(\operatorname{ord}_A(b), \operatorname{ord}_D(b))$, and take $(m_j)_{j \ge 1}$ with $P \mid m_1$, $2 m_j \mid m_{j+1}$, and $m_{j+1}/(2 m_j) \to \infty$. Define the partial products
```math
X_k := \frac{1}{r} \prod_{j=1}^k (1 + b^{-m_j})^{-1} = \frac{D}{A} \prod_{j=1}^k \frac{b^{m_j}}{b^{m_j} + 1}, \qquad Y_k := \frac{1}{X_k} = r \prod_{j=1}^k (1 + b^{-m_j}),
```
and their limits $x := \lim_{k\to\infty} X_k$, $y := \lim_{k\to\infty} Y_k = 1/x$.

**Step 1: Period divisibility and $x \in M_b \subset K_b$ with $\lim_{N\to\infty} D_N(x; b) = 1$.**
We prove by induction on $k \ge 0$ that $\operatorname{den}(X_k) \mid (b^{2 m_k} - 1)$ (with convention $2 m_0 := P$, so $\operatorname{ord}_{\operatorname{den}(X_k)}(b) \mid 2 m_k$). For $k = 0$, $\operatorname{den}(X_0) = A \mid (b^P - 1)$. For $k \ge 1$, the reduced denominator $\operatorname{den}(X_k)$ divides $\operatorname{den}(X_{k-1}) \cdot (b^{m_k} + 1)$ (any cancellation with the numerator only shrinks $\operatorname{den}(X_k)$). By the induction hypothesis and $2 m_{k-1} \mid m_k$, we have $\operatorname{den}(X_{k-1}) \mid (b^{m_k} - 1)$. Hence for every prime $p$:
- if $p$ is odd, $\gcd(b^{m_k} - 1, b^{m_k} + 1) \in \{1, 2\}$, so $p$ cannot divide both $b^{m_k} - 1$ and $b^{m_k} + 1$, giving $v_p(\operatorname{den}(X_k)) \le v_p(b^{m_k} - 1) + v_p(b^{m_k} + 1) = v_p(b^{2 m_k} - 1)$;
- if $p = 2$, $v_2(\operatorname{den}(X_k)) \le v_2(\operatorname{den}(X_{k-1})) + v_2(b^{m_k} + 1) \le v_2(b^{m_k} - 1) + v_2(b^{m_k} + 1) = v_2(b^{2 m_k} - 1)$.

Therefore $\operatorname{den}(X_k) \mid (b^{2 m_k} - 1)$ holds unconditionally for every $k \ge 1$ (covering all parities of $b$ and $A$).

Now write the **exact signed band identity** for $X_k = X_{k-1} \frac{b^{m_k}}{b^{m_k} + 1}$ at $0 \le r_0 < m_k$:
```math
b^{r_0} X_k = b^{r_0} X_{k-1} - \frac{b^{r_0} X_{k-1}}{b^{m_k} + 1}, \qquad b^{m_k + r_0} X_k = b^{r_0} (b^{m_k} - 1) X_{k-1} + \frac{b^{r_0} X_{k-1}}{b^{m_k} + 1}.
```
Because $\operatorname{den}(X_{k-1}) \mid (b^{2 m_{k-1}} - 1) \mid (b^{m_k} - 1)$, the term $b^{r_0}(b^{m_k} - 1) X_{k-1}$ is an integer. Hence
```math
\{b^{m_k + r_0} X_k\} = \left\{\frac{b^{r_0} X_{k-1}}{b^{m_k} + 1}\right\} \qquad (0 \le r_0 < m_k).
```
Set $C_0 := \lceil \log_b(2 X_0) \rceil + 1$ (since $0 < X_{k-1} \le X_0 = 1/r$ for all $k$). Summing circular distances to $0$ over band $i = 1$ ($m_k \le n < 2 m_k$) gives
```math
\frac{1}{m_k} \sum_{r_0=0}^{m_k - 1} \|b^{m_k + r_0} X_k\|_{\mathbb{T}} \le \frac{1}{m_k} \left( \sum_{r_0=0}^{m_k - C_0 - 1} \frac{b^{r_0} X_0}{b^{m_k}} + \frac{C_0}{2} \right) \le \frac{1 + C_0/2}{m_k} =: \frac{C_1}{m_k}.
```
On band $i = 0$ ($0 \le r_0 < m_k$), $\|b^{r_0} X_k\|_{\mathbb{T}} \le \|b^{r_0} X_{k-1}\|_{\mathbb{T}} + \min\!\left(\frac{1}{2}, \frac{b^{r_0} X_0}{b^{m_k}}\right)$ (whose tail averages to $\le C_1 / m_k$ by the same split at $m_k - C_0$), and since $\operatorname{ord}_{\operatorname{den}(X_{k-1})}(b) \mid 2 m_{k-1} \mid m_k$, the points $\{b^{r_0} X_{k-1}\}$ traverse $\mu(X_{k-1}; b)$ an exact integer number of times. Averaging bands $i = 0$ and $i = 1$ yields the contraction recursion
```math
W_1\big(\mu(X_k; b), \delta_0\big) \le \frac{1}{2} W_1\big(\mu(X_{k-1}; b), \delta_0\big) + \frac{C_1}{m_k}.
```
Iterating gives $W_1(\mu(X_k; b), \delta_0) \le 2^{-k} W_1(\mu(X_0; b), \delta_0) + \sum_{j=1}^k 2^{-(k-j)} C_1 / m_j \to 0$.

To upgrade this from complete periods $2 m_k$ to **all** $N \in [2 m_k, 2 m_{k+1})$, note that $|x - X_{k+1}| \le 2 X_0 b^{-m_{k+2}}$, so for every $n < 2 m_{k+1}$ we have $b^n |x - X_{k+1}| \le 2 X_0 b^{2 m_{k+1} - m_{k+2}} \to 0$ (as $m_{k+2}/(2 m_{k+1}) \to \infty$). Split $[2 m_k, 2 m_{k+1})$ into two regimes:
- If $2 m_k \le N \le m_{k+1}$, all $n < N$ lie in band $i = 0$ of $X_{k+1}$, where $\|b^n X_{k+1} - b^n X_k\|_{\mathbb{T}} \le \min(1/2, b^n X_0 / b^{m_{k+1}})$ (averaging to $\le C_1 / N$). Writing $N = q (2 m_k) + t$ with $q \ge 1$ and $0 \le t < 2 m_k$, nonnegativity of $\|\cdot\|_{\mathbb{T}}$ bounds the sum over $[0, N)$ by $(q + 1)$ complete periods of $X_k$:
  $$\frac{1}{N} \sum_{n=0}^{N-1} \|b^n X_k\|_{\mathbb{T}} \le \frac{q + 1}{q} W_1\big(\mu(X_k; b), \delta_0\big) \le 2 W_1\big(\mu(X_k; b), \delta_0\big).$$
- If $m_{k+1} < N < 2 m_{k+1}$, $[0, m_{k+1})$ consists of exact full periods of $X_k$ (plus tail $\le C_1 / m_{k+1}$), while $[m_{k+1}, N)$ lies inside band $i = 1$ of $X_{k+1}$, whose total sum is $\le C_1$. Thus $\frac{1}{N}\sum_{n<N} \|b^n X_{k+1}\|_{\mathbb{T}} \le W_1(\mu(X_k; b), \delta_0) + 2 C_1 / m_{k+1}$.

Hence $W_1(\mu_N^{\mathrm{emp}}(x; b), \delta_0) \to 0$ on $\mathbb{T}$ as $N \to \infty$. By Markov's inequality on $[\varepsilon, 1 - \varepsilon]$ with $\varepsilon = \sqrt{W_1 / 2}$, $D_N(x; b) \ge 1 - \sqrt{8 W_1(\mu_N^{\mathrm{emp}}(x; b), \delta_0)} \to 1$, so $\lim_{N\to\infty} D_N(x; b) = 1$ and $x \in M_b \subset K_b$.

**Step 2: Exact convergence of $\mu_N^{\mathrm{emp}}(y; b)$, $D_N(y; b)$, and word frequencies.**
Set $S_k := \sum_{j=1}^k m_j$. Because $m_{j+1} / (2 m_j) \to \infty$, we have $S_{k-1} = o(m_k)$ and $S_k = (1 + o(1)) m_k \ll m_{k+1}$. Let $\Delta_k := \lfloor \sqrt{m_{k+1}} \rfloor$ and $T_r := \operatorname{ord}_D(b)$. For every $n$ in the clean window $[S_k, m_{k+1} - \Delta_k)$:
1. Expanding $Y_k = r \prod_{j=1}^k (1 + b^{-m_j}) = \sum_{I \subseteq \{1,\dots,k\}} b^{-\sum_{j \in I} m_j} r$, every exponent $n - \sum_{j \in I} m_j$ is nonnegative (since $n \ge S_k$). Because $T_r \mid P \mid m_j$ for all $j$, $b^{m_j} \equiv 1 \pmod D$ and hence $b^{n - \sum_{j \in I} m_j} r \equiv b^n r \pmod 1$ for every subset $I$. Summing over all $2^k$ subsets and using $2 \equiv b^{s_0} \pmod D$ yields the **exact subset-sum orbit lock**:
   ```math
   b^n Y_k \equiv 2^k b^n r \equiv b^{n + k s_0} r \pmod 1 \qquad (n \ge S_k).
   ```
2. The tail error satisfies $0 < b^n (y - Y_k) \le 2 y \, b^{n - m_{k+1}} \le 2 y \, b^{-\Delta_k} =: \delta_k \to 0$.
3. Because $r = A/D$ is reduced with $\gcd(b, D) = 1$:
   - if $D \ge 2$, every point of the orbit $\operatorname{supp}(\mu(r; b))$ lies in $[1/D, 1 - 1/D]$, so once $\delta_k < 1/(2 D)$, adding $b^n(y - Y_k) \in (0, \delta_k]$ never wraps across $0$ or $1$, giving $\{b^n y\} = \{b^{n + k s_0} r\} + b^n(y - Y_k) \in (0, 1)$ within $\delta_k$ of $\{b^{n + k s_0} r\}$ in $\mathbb{R}$;
   - if $D = 1$, then $r = A \in \mathbb{Z}_{>0}$, $\mu(r; b) = \delta_0$, $b^n Y_k \in \mathbb{Z}$, and once $\delta_k < 1$, $\{b^n y\} = b^n(y - Y_k) \in (0, \delta_k]$ again stays in $[0, 1)$ without wrap-around at distance $\le \delta_k$ from $0$ (and falls inside $C_{0^L}$ once $\delta_k < b^{-L}$, matching $\delta_0(C_w) = \mathbf{1}[w = 0^L]$).

Now let $N \in [m_k, m_{k+1})$ ($k$ large). Partition $[0, N)$ into:
- the clean $k$-window $W_k := [S_{k-1}, m_k - \Delta_{k-1})$ (where $\{b^n y\}$ tracks the shifted periodic orbit $\{b^{n + (k-1) s_0} r\}$ within $\delta_{k-1}$),
- the clean $(k+1)$-window $W_{k+1} := [S_k, \min(N, m_{k+1} - \Delta_k))$ (where $\{b^n y\}$ tracks $\{b^{n + k s_0} r\}$ within $\delta_k$),
- the exceptional prefix/transition/suffix indices $E_N := [0, N) \setminus (W_k \cup W_{k+1})$, whose cardinality is at most
  $$|E_N| \le S_{k-1} + (S_k - m_k + \Delta_{k-1}) + \Delta_k = 2 S_{k-1} + \Delta_{k-1} + \Delta_k = o(m_k) = o(N)$$
  (note $\Delta_k$ is only needed if $N > m_{k+1} - \Delta_k$, in which case $\Delta_k = \lfloor \sqrt{m_{k+1}} \rfloor = o(N)$).
Within each clean window $W_j$ ($j \in \{k, k+1\}$), removing at most $T_r - 1$ trailing indices leaves an exact integer multiple of $T_r$ consecutive steps of the orbit $\mu(r; b)$. Absorbing those at most $2 T_r$ indices into $E_N$, we write $\mu_N^{\mathrm{emp}}(y; b) = (1 - \eta_N) \tilde{\nu}_N + \eta_N \nu_{\mathrm{err}}$ with $\eta_N \le (|E_N| + 2 T_r)/N \to 0$ and a real-line transport coupling $W_\infty^{[0,1)}(\tilde{\nu}_N, \mu(r; b)) \le \delta_{k-1} \to 0$.

By Lemma 1.1, $|D_N(y; b) - D(\mu(r; b))| \le 2 \delta_{k-1} + \eta_N \to 0$, and $W_1(\mu_N^{\mathrm{emp}}(y; b), \mu(r; b)) \le \delta_{k-1} + \eta_N \to 0$. For any word $w \in \{0, \dots, b - 1\}^L$ ($L \ge 1$): when $D \ge 2$, by `RadixPowerTower.coprime_rat_cylinder_margin` every point of $\operatorname{supp}(\mu(r; b))$ stays at distance $\ge 1 / (D b^L)$ from the endpoints of the $b$-adic cylinder $C_w$, so once $\delta_{k-1} < 1 / (D b^L)$ every clean index $n$ lands in the exact same cylinder $C_w$ as $\{b^{n + (j-1) s_0} r\}$ (and when $D = 1$, every clean index lands in $C_{0^L}$ once $\delta_{k-1} < b^{-L}$). Hence $|f_w(N; y, b) - \mu(r; b)(C_w)| \le \eta_N \to 0$.

**Step 3: Irrationality of $x$ and $y$.**
If $y = p/q$ were rational, then $D y = D r \prod_{j \ge 1} (1 + b^{-m_j}) = A \prod_{j \ge 1} (1 + b^{-m_j})$ would have an eventually periodic base-$b$ expansion. Yet the partial product $A \prod_{j < k}(1 + b^{-m_j}) < 2^{k-1} A \le b^{k-1} A$ has integer part of at most $\lceil \log_b A \rceil + k$ base-$b$ digits and fractional length $S_{k-1}$. For $k$ large enough that $S_{k-1} + \lceil \log_b A \rceil + k < m_k / 2$ (which holds since $m_k \ge 2^{k-1} m_1$ and $S_{k-1} = o(m_k)$), the base-$b$ expansion of $D y$ consists of non-overlapping shifted copies of $A \prod_{j < k}(1 + b^{-m_j})$ separated by zero-runs of length at least $m_k - S_{k-1} - \lceil \log_b A \rceil - k \to \infty$, impossible for a rational with infinitely many nonzero digits. Hence $y$ and $x = 1/y$ are irrational.

### 1.3 Base-$2$ density and all-base universal repunit inversion

**Corollary 1.2 (Base-$2$ dense convergent reciprocal spectrum).** *In base $b = 2$, $\mathcal{A}_{\mathrm{conv}}(2)$ is dense in $[0, 1]$.*

*Proof.* When $b = 2$, $2 \in \langle 2 \rangle \pmod D$ holds for every odd $D \ge 1$. For any nontrivial binary word $w \in \{0, 1\}^P$ containing both $0$ and $1$, rotate $w$ so its last bit is $1$ and set $r := v(w) / (2^P - 1) = A / D$ in lowest terms (so $A, D$ are odd, $\gcd(2, A D) = 1$). Theorem 1 realizes $D(\mu(r; 2)) \in \mathcal{A}_{\mathrm{conv}}(2)$. Taking $w = 0^z w_{\mathrm{dB}, m}$ where $w_{\mathrm{dB}, m}$ is a cyclic binary de Bruijn word of order $m$ (length $2^m$, rotated to end in $1$), the periodic orbit $\mu(r; 2)$ approximates $\frac{z}{z + 2^m} \delta_0 + \frac{2^m}{z + 2^m} \lambda$ in discrepancy up to $O(m / (z + 2^m) + 2^{-m})$ (the $2^m$ de Bruijn shifts have discrepancy $\le 2^{1 - m}$ by Theorem 2, and $z - m$ shifts inside $0^z$ lie within $2^{-m}$ of $0$). Choosing $m$ large and $z / (z + 2^m) \to \alpha$ yields values in $\mathcal{A}_{\mathrm{conv}}(2)$ arbitrarily close to any $\alpha \in [0, 1]$. $\square$

**Proposition 1.3 (Universal repunit inversion in every base $b \ge 2$).** *For any radix $b \ge 2$, any reduced $r = A/D \in \mathbb{Q}_{>0}$ with $\gcd(b, A D) = 1$, and any schedule $(m_j)_{j \ge 1}$ with $P = \operatorname{lcm}(\operatorname{ord}_A(b), \operatorname{ord}_D(b)) \mid m_1$, $b m_j \mid m_{j+1}$, and $m_{j+1} / (b m_j) \to \infty$, let $Q_b(q) := (1 - q^b)/(1 - q) = \sum_{s=0}^{b-1} q^s$ and*
```math
x := \frac{1}{r} \prod_{j=1}^\infty Q_b(b^{-m_j})^{-1} = \frac{1}{r} \prod_{j=1}^\infty \frac{1 - b^{-m_j}}{1 - b^{-b m_j}}, \qquad y := \frac{1}{x} = r \prod_{j=1}^\infty \left(1 + b^{-m_j} + \dots + b^{-(b - 1) m_j}\right).
```
*Then $x, y$ are irrational, $\mu_N^{\mathrm{emp}}(x; b) \xrightarrow{W_1} \delta_0$ on $\mathbb{T}$ and $\lim_{N\to\infty} D_N(x; b) = 1$ (so $x \in M_b \subset K_b$), and every weak\* limit point of $\mu_N^{\mathrm{emp}}(1/x; b)$ is a convex combination of $\mu(r; b), \mu(2 r; b), \dots, \mu((b - 1) r; b)$ (with clean-window approximation in $W_\infty^{[0,1)}$ on each interior block $[s m_k + (b-1) S_{k-1},\; (s+1) m_k - \Delta'_k)$ for $0 \le s \le b - 2$ and on the final block $[(b - 1) m_k + (b - 1) S_{k-1},\; m_{k+1} - \Delta_k)$, where $\Delta'_k := \lfloor \sqrt{m_k} \rfloor$ and $\Delta_k := \lfloor \sqrt{m_{k+1}} \rfloor$). Moreover, for every $b \ge 2$, $\alpha \in (0, 1)$, and $\varepsilon > 0$, there exists an irrational $x \in M_b \subset K_b$ with $[D^-(1/x; b), D^+(1/x; b)] \subseteq [\alpha - \varepsilon, \alpha + \varepsilon]$.*

*Proof.*
1. **Exact band identity and $x \in M_b \subset K_b$ ($\lim_{N\to\infty} D_N(x; b) = 1$).** We prove $\operatorname{den}(X_k) \mid (b^{b m_k} - 1)$ by induction on $k \ge 0$ (with $b m_0 := P$). At step $k \ge 1$, the induction hypothesis and $b m_{k-1} \mid m_k$ give $\operatorname{den}(X_{k-1}) \mid (b^{m_k} - 1)$. In
   ```math
   X_k = X_{k-1} \cdot \frac{b^{(b - 1) m_k}(b^{m_k} - 1)}{b^{b m_k} - 1},
   ```
   the quotient $(b^{m_k} - 1) / \operatorname{den}(X_{k-1})$ is therefore an integer, so $\operatorname{den}(X_k) \mid (b^{b m_k} - 1)$ immediately. Writing $q = b^{-m_k}$, the identity $(1 - q) / (1 - q^b) = 1 + \frac{-q + q^b}{1 - q^b}$ gives for $0 \le i < b$ and $0 \le r_0 < m_k$:
   ```math
   b^{i m_k + r_0} X_k \equiv S_i \, b^{r_0} X_{k-1} + b^{r_0} X_{k-1} \tau_i(b^{-m_k}) \pmod 1,
   ```
   where $S_0 = 1$, $S_1 = \dots = S_{b-1} = 0$, $\tau_0(q) = (-q + q^b)/(1 - q^b)$, and $\tau_i(q) = q^{b - i}(1 - q)/(1 - q^b)$ ($1 \le i < b$). Every band $i \in \{1, \dots, b - 1\}$ has $S_i = 0$ and tail bounded by $\min(1/2, b^{r_0 - m_k} X_0)$ (averaging to $\le C_1 / m_k$), and band $0$ has tail bounded by $\min(1/2, b^{r_0 - m_k} X_0)$, yielding the $1/b$-contraction
   ```math
   W_1\big(\mu(X_k; b), \delta_0\big) \le \frac{1}{b} W_1\big(\mu(X_{k-1}; b), \delta_0\big) + \frac{C_1}{m_k} \longrightarrow 0.
   ```
   To upgrade to **all** $N \in [b m_k, b m_{k+1})$, note that $1 - (1 - q)/(1 - q^b) = (q - q^b)/(1 - q^b) \le q$ for $q \in (0, 1)$, so $0 < X_{k+1} - x \le X_0 \sum_{j \ge k+2} b^{-m_j} \le 2 X_0 b^{-m_{k+2}}$. Thus for every $n < b m_{k+1}$, $b^n |x - X_{k+1}| \le 2 X_0 b^{b m_{k+1} - m_{k+2}} \to 0$ (as $m_{k+2}/(b m_{k+1}) \to \infty$). Split $[b m_k, b m_{k+1})$ into two regimes:
   - If $b m_k \le N \le m_{k+1}$, every $n < N$ lies in band $i = 0$ of $X_{k+1}$, where $\|b^n X_{k+1} - b^n X_k\|_{\mathbb{T}} \le \min(1/2, b^n X_0 / b^{m_{k+1}})$ (averaging to $\le C_1 / N$). Writing $N = q (b m_k) + t$ ($q \ge 1$, $0 \le t < b m_k$), nonnegativity of $\|\cdot\|_{\mathbb{T}}$ bounds the sum over $[0, N)$ by $(q + 1)$ complete periods of $X_k$, giving $\frac{1}{N} \sum_{n=0}^{N-1} \|b^n X_k\|_{\mathbb{T}} \le \frac{q + 1}{q} W_1(\mu(X_k; b), \delta_0) \le 2 W_1(\mu(X_k; b), \delta_0)$.
   - If $m_{k+1} < N < b m_{k+1}$, $[0, m_{k+1})$ consists of exact full periods of $X_k$ (since $\operatorname{ord}_{\operatorname{den}(X_k)}(b) \mid b m_k \mid m_{k+1}$, plus band-$0$ tail $\le C_1 / m_{k+1}$), while $[m_{k+1}, N)$ lies inside bands $i \in \{1, \dots, b - 1\}$ of $X_{k+1}$, each having $S_i = 0$ and total circular-distance sum $\le C_1$, contributing at most $(b - 1) C_1 / N \le (b - 1) C_1 / m_{k+1}$. Hence $\frac{1}{N} \sum_{n < N} \|b^n X_{k+1}\|_{\mathbb{T}} \le W_1(\mu(X_k; b), \delta_0) + b C_1 / m_{k+1}$.

   Combining both regimes yields $W_1(\mu_N^{\mathrm{emp}}(x; b), \delta_0) \to 0$ on $\mathbb{T}$ and $\lim_{N\to\infty} D_N(x; b) = 1$, so $x \in M_b \subset K_b$.

2. **Block structure of $y = 1/x$.** Set $S_k := \sum_{j=1}^k m_j$, $\Delta'_k := \lfloor \sqrt{m_k} \rfloor$, and $\Delta_k := \lfloor \sqrt{m_{k+1}} \rfloor$. Expanding $Y_k = Y_{k-1} \sum_{u=0}^{b-1} b^{-u m_k}$, note that $Y_{k-1} = r \prod_{j < k} Q_b(b^{-m_j}) < y$ is a sum of $b^{k-1}$ terms of the form $b^{-t} r$ with $0 \le t \le (b - 1) S_{k-1}$. For $n$ in the $s$-th clean block $[s m_k + (b - 1) S_{k-1},\; (s + 1) m_k - \Delta'_k)$ ($0 \le s \le b - 2$), or in the final block $[(b - 1) m_k + (b - 1) S_{k-1},\; m_{k+1} - \Delta_k)$ ($s = b - 1$):
   - Every term with $u \le s$ has nonnegative exponent $n - u m_k - t \ge 0$, and since $b^{m_j} \equiv 1 \pmod D$ for all $j$, each $Y_{k-1}$-term contributes $b^n r \pmod 1$, so the $b^{k-1}$ terms of $Y_{k-1}$ sum to $b^{k-1} b^n r = b^{n + k - 1} r \pmod 1$ (simply shifting the orbit by $k - 1$ steps).
   - The inactive terms $u > s$ of $Y_k$ (when $0 \le s \le b - 2$) satisfy $0 < b^n Y_{k-1} \sum_{u = s + 1}^{b-1} b^{-u m_k} \le 2 y \, b^{n - (s + 1) m_k} \le 2 y \, b^{-\Delta'_k} \to 0$, and the product tail satisfies $0 < b^n(y - Y_k) \le 2 y \, b^{n - m_{k+1}} \le 2 y \, b^{-\Delta_k} \to 0$.
   - Summing over the $s + 1$ active terms $u = 0, \dots, s$ gives:
     - for $0 \le s \le b - 2$: $b^n y \equiv (s + 1) b^{n + k - 1} r + O(y \, b^{-\Delta'_k}) \pmod 1$ (tracking the periodic orbit $\mu((s + 1) r; b)$);
     - for $s = b - 1$: the $b$ active terms give $b \cdot b^{n + k - 1} r + O(y \, b^{-\Delta_k}) = b^{n + k} r + O(y \, b^{-\Delta_k}) \pmod 1$ (returning to the orbit $\mu(r; b)$).
   Thus $Q_b$ operates in **every** base $b \ge 2$ without requiring $2 \in \langle b \rangle \pmod D$, because the full-block multiplier is the radix $b$ itself while the intermediate blocks $s = 0, \dots, b - 2$ traverse $\mu(r; b), \mu(2 r; b), \dots, \mu((b - 1) r; b)$. Because the interior transition zones between blocks $s = 0, \dots, b - 2$ have total length $O(b^2 S_{k-1} + b \Delta'_k) = o(m_k)$, and the trailing cutoff $\Delta_k$ is only encountered when $N > m_{k+1} - \Delta_k$ (where $\Delta_k = \lfloor \sqrt{m_{k+1}} \rfloor = o(N)$), every weak\* limit point of $\mu_N^{\mathrm{emp}}(y; b)$ is a convex combination $\sum_{s=1}^{b-1} \theta_s \mu(s r; b)$ ($\theta_s \ge 0, \sum \theta_s = 1$).

3. **Arbitrarily localized $[D^-, D^+] \subseteq [\alpha - \varepsilon, \alpha + \varepsilon]$.** Let $\mu_\alpha := (1 - \alpha)\lambda + \alpha \delta_0$. Multiplication by any $s \in \{1, \dots, b - 1\}$ on $\mathbb{T}$ fixes both $\lambda$ and $\delta_0$ ($s_* \mu_\alpha = \mu_\alpha$). Choose a base-$b$ periodic word $w = 0^z w_{\mathrm{dB}, m}$ (with $w_{\mathrm{dB}, m}$ an order-$m$ base-$b$ de Bruijn word rotated to end in $1$, so $r = v(w)/(b^P - 1)$ has $\gcd(A, b) = 1$) such that $W_1(\mu(r; b), \mu_\alpha) < \vartheta := \varepsilon^2 / (32 b)$. Since $x \mapsto s x \bmod 1$ is $s$-Lipschitz on $\mathbb{T}$, $W_1(\mu(s r; b), \mu_\alpha) = W_1(s_* \mu(r; b), s_* \mu_\alpha) \le s \vartheta < \varepsilon^2 / 32$ for every $1 \le s \le b - 1$. By convexity, every weak\* limit point $\nu = \sum_{s=1}^{b-1} \theta_s \mu(s r; b)$ satisfies $W_1(\nu, \mu_\alpha) < \varepsilon^2 / 32$, and by Lemma 1.1 on the clean blocks, every subsequential limit of $D_N(y; b)$ equals $D(\nu)$ for such a $\nu$. For any probability measure $\nu$ on $[0, 1)$, comparing against $\mu_\alpha$ by smoothing indicator functions over width $\eta := \sqrt{W_1(\nu, \mu_\alpha)}$ yields $|D(\nu) - \alpha| \le 4 \sqrt{W_1(\nu, \mu_\alpha)} < \varepsilon$. Irrationality of $x, y$ follows as in Step 3 of Theorem 1 (with $b^{k-1} A$ bounding the integer part of $A \prod_{j < k} Q_b(b^{-m_j})$). $\square$

### 1.4 The $Q(1) = 1$ cyclotomic coefficient excess identity

**Proposition 1.4 ($Q(1) = 1$ coefficient excess identity).** *Let $L \ge 2$ and let $Q \in \mathbb{Z}[q]$ divide $(1 - q^L)/(1 - q)$ with $Q(0) = Q(1) = 1$ and $\deg Q \ge 1$. Write $A(q) := \frac{1 - q^L}{(1 - q) Q(q)} = \sum_{i=0}^{L - 1} S_i q^i$ (with $S_i = 0$ for $i > \deg A$). Then*
```math
\sum_{i:\, S_i \ge 2} (S_i - 1) \;=\; \#\{i < L : S_i = 0\} \;+\; \sum_{i:\, S_i \le -1} (1 - S_i) \;\ge\; \deg Q \;\ge\; 1.
```
*In particular, $\max_{0 \le i < L} S_i \ge 2$.*

*Proof.* Evaluate $A(1) = L / Q(1) = L$, so $\sum_{i=0}^{L-1} (S_i - 1) = A(1) - L = 0$. Splitting the sum by the sign of $S_i - 1$ yields the exact identity. Since $\deg A = L - 1 - \deg Q$, the last $\deg Q$ coefficients $S_{L - \deg Q}, \dots, S_{L - 1}$ vanish, so $\#\{i < L : S_i = 0\} \ge \deg Q \ge 1$. $\square$

*Heuristic remark (motivation for rational-seed inversion, not a proved limitation).* In a pure $R_0 = 1$ cyclotomic product $x = \prod_{k \ge 1} Q_k(b^{-m_k})$ with $Q_k \mid (1 - q^{L_k})/(1 - q)$ and $Q_k(0) = 1$, Proposition 1.4 shows that enforcing $Q_k(1) = 1$ (to avoid multiplying the denominator by $|Q_k(1)| \ge 2$) necessarily introduces band multipliers $S_i \ge 2$ alongside the zero-bands $S_i = 0$. Conversely, in a finite exhaustive search (`scripts/phase23_reciprocals_v2.py` §1e, `Finite certificate` for $L \le 50$) over all $1,050$ cyclotomic divisors $Q \mid (1 - q^L)/(1 - q)$ with $L \le 50$, $|Q(1)| \ge 2$, and band multipliers $|S_i| \le 1$ (of which $562$ satisfy $\deg Q \le \lfloor L/2 \rfloor$), every divisor had zero-band density $\rho := \#\{i < L : S_i = 0\} / L \ge 1/2$. While neither observation is a general impossibility theorem for pure $R_0 = 1$ products, they motivate inverting the construction via an explicit rational seed $r$ in Theorem 1 and Proposition 1.3.

---

## 2. Sub-track D2: Exact $D_{\max}(b, L) = 2 b^{-L}$ and $L$-Normal Nonnormal Reciprocals in All Bases

### 2.1 Sharp maximum discrepancy of $L$-normal numbers (Theorem 2)

*Literature note.* The cylinder-cover upper bound $D^+(y; b) \le 2 b^{-L}$ is an elementary folklore consequence of $b$-adic interval approximation (cf. Bugeaud, *Distribution Modulo One and Diophantine Approximation*, Ch. 4); we did not locate a prior published source establishing exact attainment of $D_{\max}(b, L) = 2 b^{-L}$ and full realization of $[0, 2 b^{-L}]$ via loop-deleted de Bruijn Eulerian circuits $G_{b, L}^*$, so a self-contained proof is recorded below.

**Proof of Theorem 2.**
*Upper bound ($D^+(y; b) \le 2 b^{-L}$).* Let $y \in \mathbb{R}$ be $L$-normal in base $b$, and let $\nu$ be any weak\* limit point of $\mu_N^{\mathrm{emp}}(y; b)$. For every length-$L$ word $w \in \{0, \dots, b - 1\}^L$, let $C_w = [a_w, a_w + b^{-L})$ be the corresponding $b$-adic cylinder. Since $y$ is $L$-normal, $\mu_N^{\mathrm{emp}}(y; b)(C_w) \to b^{-L}$ as $N \to \infty$ for all $b^L$ words $w$. Consider any interval $I = [u, v) \subseteq [0, 1)$. Let $\mathcal{W}_{\mathrm{in}}$ be the set of $b$-adic intervals $C_w \subseteq I$, and $\mathcal{W}_{\mathrm{cov}}$ the set of $C_w$ intersecting $I$. At most two cylinders (those containing $u$ and $v$) lie in $\mathcal{W}_{\mathrm{cov}} \setminus \mathcal{W}_{\mathrm{in}}$. Hence
```math
\sum_{w \in \mathcal{W}_{\mathrm{in}}} \mu_N^{\mathrm{emp}}(y; b)(C_w) \;\le\; \mu_N^{\mathrm{emp}}(y; b)(I) \;\le\; \sum_{w \in \mathcal{W}_{\mathrm{cov}}} \mu_N^{\mathrm{emp}}(y; b)(C_w),
```
while $|I| - 2 b^{-L} \le |\mathcal{W}_{\mathrm{in}}| b^{-L} \le |I| \le |\mathcal{W}_{\mathrm{cov}}| b^{-L} \le |I| + 2 b^{-L}$. For every $\varepsilon > 0$, choosing $N$ large enough that $|\mu_N^{\mathrm{emp}}(y; b)(C_w) - b^{-L}| \le \varepsilon b^{-L}$ for all $b^L$ words $w$ yields
```math
\big|\mu_N^{\mathrm{emp}}(y; b)(I) - |I|\big| \le 2 b^{-L} + \varepsilon \qquad (\forall I \subseteq [0, 1)),
```
uniformly in $I$. Taking $\sup_I$ and $\limsup_{N\to\infty}$ gives $D^+(y; b) \le 2 b^{-L}$.

*Exact attainment via the loop-deleted de Bruijn digraph $G_{b, L}^*$.* Fix $b \ge 2$ and $L \ge 1$. Consider the directed de Bruijn graph $G_{b, L}$ with vertex set $V = \{0, \dots, b - 1\}^{L-1}$ (for $L = 1$, a single vertex $\varnothing$) and $b^L$ directed edges $u \xrightarrow{d} \mathrm{shift}(u, d)$ corresponding bijectively to the $b^L$ words of length $L$. Delete the two extreme self-loops $0^L$ (at vertex $0^{L-1}$) and $(b - 1)^L$ (at vertex $(b - 1)^{L-1}$) to form $G_{b, L}^*$:
- For $L = 1$, $G_{b, 1}^*$ consists of $b - 2$ self-loops $1, 2, \dots, b - 2$ on the single vertex $\varnothing$ (empty when $b = 2$).
- For $L \ge 2$, every vertex $v \in V$ still has $\deg^+(v) = \deg^-(v)$ (equal to $b - 1 \ge 1$ at $0^{L-1}$ and $(b - 1)^{L-1}$, and $b$ at all other vertices). Moreover, $G_{b, L}^*$ is strongly connected: $G_{b, L}$ is strongly connected (from any $u$ to any $v$, pushing the $L - 1$ digits of $v$ yields a directed path), and a shortest directed path between any two distinct vertices never traverses a self-loop, so deleting the self-loops $0^L$ and $(b - 1)^L$ preserves strong connectivity. Hence $G_{b, L}^*$ admits an Eulerian circuit $C^*$ of exact length $b^L - 2$ visiting both $0^{L-1}$ and $(b - 1)^{L-1}$.

For any integer $R \ge 1$, define the cyclic word $W_R^{\mathrm{exact}}$ of length $P_R = R b^L$ by traversing $R$ copies of $C^*$ and inserting $R$ consecutive $0$-loops at one visit to $0^{L-1}$ and $R$ consecutive $(b - 1)$-loops at one visit to $(b - 1)^{L-1}$ (for $L = 1$: $W_R^{\mathrm{exact}} := 0^R (b - 1)^R (1 2 \cdots (b - 2))^R$, rotated to end in $1$). Every length-$L$ word appears **exactly $R$ times** cyclically in $W_R^{\mathrm{exact}}$, so the periodic rational $r_R := v(W_R^{\mathrm{exact}}) / (b^{P_R} - 1)$ is **exact $L$-normal**. Set $k_R := \lceil \log_b R \rceil$, $\delta_R := b^{-k_R} \le 1/R$, and $I_R := [\delta_R, 1 - \delta_R)$ ($R$ large):
- For $0 \le t < R - k_R$, the $t$-th shift of the $0^R$-block begins with at least $k_R + L - 1$ zeros, so $\{b^n r_R\} < b^{-k_R} = \delta_R$.
- For $0 \le t < R - k_R$, the $t$-th shift of the $(b - 1)^R$-block begins with at least $k_R + L - 1$ digits $(b - 1)$, so $\{b^n r_R\} > 1 - b^{-k_R} = 1 - \delta_R$.

Hence the interval $I_R$ of length $1 - 2\delta_R$ misses at least $2(R - k_R)$ points out of $R b^L$, giving
```math
|I_R| - \mu(r_R; b)(I_R) \ge (1 - 2\delta_R) - \left(1 - \frac{2(R - k_R)}{R b^L}\right) = \frac{2}{b^L} - \frac{2 k_R}{R b^L} - \frac{2}{R} = 2 b^{-L} - O_b\!\left(\frac{\log_b R}{R}\right).
```
Letting $R \to \infty$, we obtain exact $L$-normal periodic rationals $r_R$ with $D(\mu(r_R; b)) \to 2 b^{-L}$.

To attain $2 b^{-L}$ **exactly** as $\lim_{N\to\infty} D_N(y; b)$ by a single real number $y$, rotate each block $W_{R_j}^{\mathrm{exact}}$ so that it begins with the common $(L - 1)$-prefix $0^{L-1}$ (empty when $L = 1$), and concatenate $c_j$ copies of $W_{R_j}^{\mathrm{exact}}$ (choosing $R_j \to \infty$ slowly enough that $P_{R_{j+1}} = o(\sum_{i \le j} c_i P_{R_i})$). Because every block starts with the same $(L - 1)$-prefix $0^{L-1}$, every length-$L$ word crossing a block junction agrees with the cyclic wrap-around of the preceding block (alternatively, boundary windows at junctions form an $o(1)$ proportion). Along every prefix $N$, the empirical measure $\mu_N^{\mathrm{emp}}(y; b)$ is a convex combination of $\mu(r_{R_j}; b)$ and $\mu(r_{R_{j+1}}; b)$ plus $o(1)$ error, so $y$ is $L$-normal and $D_N(y; b) \to 2 b^{-L}$.

*Realizing every $\alpha \in [0, 2 b^{-L}]$ via the affine mixture law.* Observe that for **any** Borel probability measure $\sigma$ on $[0, 1)$ and any $t \in [0, 1]$, the convex combination $\mu_t := (1 - t)\lambda + t \sigma$ satisfies
```math
D(\mu_t) = \sup_{0 \le u < v \le 1} \big|(1 - t)(v - u) + t \sigma([u, v)) - (v - u)\big| = t \sup_{0 \le u < v \le 1} \big|\sigma([u, v)) - (v - u)\big| = t D(\sigma).
```
Interleaving blocks of $W_{R_j}^{\mathrm{exact}}$ (density $t := \alpha / (2 b^{-L})$) with blocks of full de Bruijn words $W_{\mathrm{dB}, m_j}$ of growing order $m_j \to \infty$ (density $1 - t$, converging weakly to $\lambda$, each rotated to start with $0^{L-1}$) produces an $L$-normal real number $y_\alpha$ whose empirical measure converges on $[0, 1]$ to $(1 - t)\lambda + t \sigma_{\mathrm{ext}}$, where the weak\* limit $\sigma_{\mathrm{ext}} = \lim_{R\to\infty} \mu(r_R; b)$ on $[0, 1]$ assigns mass $b^{-L}$ to $\{0\}$ and mass $b^{-L}$ to $\{1\}$ (so $\sigma_{\mathrm{ext}}((0, 1)) = 1 - 2 b^{-L}$ and $D(\sigma_{\mathrm{ext}}) = 2 b^{-L}$), yielding $\lim_{N\to\infty} D_N(y_\alpha; b) = t \cdot 2 b^{-L} = \alpha$. $\square$

### 2.2 Proof of Theorem 3 (Unconditional $L$-normal nonnormal reciprocals in ALL bases $b \ge 2$)

#### Part (a): Base $2$ — dense $L$-normal spectrum and prescribed rational word distributions
In base $2$, every rational $r = v(w) / (2^P - 1)$ with $w$ ending in $1$ has odd numerator and odd denominator, so Theorem 1 applies directly and transfers **both** the exact limiting $L$-word distribution and the exact limiting discrepancy $D(\mu(r; 2))$ to $y = 1/x$ ($x \in M_2 \subset K_2$).
- For $L$-normality across $[0, 2^{1 - L}]$, fix $R$ large and an order-$m$ binary de Bruijn word $w_{\mathrm{dB}, m}$ ($m \ge L$, rotated so both $W_R^{\mathrm{exact}}$ and $w_{\mathrm{dB}, m}$ share the common $(L - 1)$-prefix $0^{L-1}$ and end with $1$). Concatenating $c_{\mathrm{ext}}$ copies of $W_R^{\mathrm{exact}}$ and $c_{\mathrm{dB}}$ copies of $w_{\mathrm{dB}, m}$ preserves **exact** uniform length-$L$ word counts (every boundary window matches cyclic wrap-around via the shared $(L - 1)$-prefix $0^{L-1}$) while sweeping the convex weight $t = c_{\mathrm{ext}} P_R / (c_{\mathrm{ext}} P_R + c_{\mathrm{dB}} 2^m) \in [0, 1]$ across all rationals; letting $R, m \to \infty$ yields exact $L$-normal convergent discrepancies dense in $[0, 2^{1 - L}]$.
- For any rational flow-consistent length-$L$ word distribution $\mathbf{p}$ on $\{0, 1\}^L$ (i.e., $p_w = c_w / P$ with $c_w \in \mathbb{Z}_{\ge 0}$ satisfying $\sum_{d \in \{0,1\}} c_{u d} = \sum_{d \in \{0,1\}} c_{d u}$ for every $u \in \{0, 1\}^{L-1}$, whose support digraph on $\{0, 1\}^{L-1}$ is connected and which assigns positive mass to words containing both $0$ and $1$), Euler's theorem gives a cyclic word $w$ of length $P$ with exact $L$-word frequencies $\mathbf{p}$. Rotating $w$ to end in $1$ and applying Theorem 1 produces an irrational $x \in M_2 \subset K_2$ whose reciprocal $1/x$ has exact limiting word frequencies $\mathbf{p}$ and exact convergent discrepancy $D(\mu(r; 2)) \in (0, 1)$.

#### Part (b): ALL bases $b \ge 2$, ALL $L \ge 1$ — the refined Markov digraph $\mathcal{G}_{b, Q b^L}$
In base $b \ge 3$, universal repunit inversion (Proposition 1.3) forces $y = 1/x$ to visit the orbits $\mu(s r; b)$ for **every** $s \in \{1, \dots, b - 1\}$. To guarantee that $y = 1/x$ is $L$-normal along **all** $N$ (without relying on $2 \in \langle b \rangle \pmod D$ or Artin's primitive root conjecture), we construct an explicit rational $r$ such that **every multiple $s r$ ($1 \le s \le b - 1$) is simultaneously exact $L$-normal**, while maintaining strictly positive discrepancy!

Define
```math
Q := \operatorname{lcm}(1, 2, \dots, b - 1), \qquad M := Q b^L, \qquad J_u := \left[\frac{u}{M},\, \frac{u + 1}{M}\right) \quad (0 \le u < M).
```
Consider the directed graph $\mathcal{G}_{b, M}$ on vertex set $V_M := \{0, 1, \dots, M - 1\}$ with $b M$ directed edges: for each $u \in V_M$ and each $d \in \{0, \dots, b - 1\}$, put a directed edge
```math
u \xrightarrow{\;d\;} v := (b u + d) \bmod M.
```
**Why $\mathcal{G}_{b, M}$ encodes $b$-adic dynamics on $J_u$.** Observe that $T_b(J_u) = [b u / M,\; b(u + 1) / M) \bmod 1$ is the exact disjoint union of the $b$ cells $J_{(b u + d) \bmod M}$ ($0 \le d < b$). Consequently, any closed walk $(u_0, u_1, \dots, u_{P-1})$ in $\mathcal{G}_{b, M}$ is uniquely tracked by a single periodic orbit of $T_b$ whose leading base-$b$ digit at step $n$ is
```math
\alpha_n := \left\lfloor \frac{b u_n}{M} \right\rfloor \in \{0, \dots, b - 1\}.
```

**Lemma 2.1 (Exact cell tracking and strict interiority for $\mathcal{G}_{b, M}$).** *Let $(u_0 \xrightarrow{d_0} u_1 \xrightarrow{d_1} \cdots \xrightarrow{d_{P-1}} u_0)$ be any closed walk in $\mathcal{G}_{b, M}$ whose edge digit labels $(d_n)_{n=0}^{P-1}$ are not all $0$ and not all $b - 1$. Set $\alpha_n := \lfloor b u_n / M \rfloor \in \{0, \dots, b - 1\}$, $A := \sum_{n=0}^{P-1} \alpha_n b^{P - 1 - n}$, and $r := A / (b^P - 1)$. Then for **every** $n \in \{0, \dots, P - 1\}$,*
```math
\frac{u_n}{M} \;<\; \{b^n r\} \;<\; \frac{u_n + 1}{M}.
```

*Proof.* Since $b \mid M$, write $M = b M'$ with $M' = Q b^{L-1} \in \mathbb{Z}_{\ge 1}$. For every $u_n \in \{0, \dots, M - 1\}$ and $d_n \in \{0, \dots, b - 1\}$,
```math
\frac{u_n}{M'} = \frac{b u_n}{M} \;\le\; \frac{b u_n + d_n}{M} \;<\; \frac{b(u_n + 1)}{M} = \frac{u_n + 1}{M'}.
```
Because $u_n$ and $u_n + 1$ are consecutive integers, there is no integer strictly between $u_n / M'$ and $(u_n + 1) / M'$. Therefore $\lfloor (b u_n + d_n) / M \rfloor = \lfloor b u_n / M \rfloor = \alpha_n$, and by definition of the edge $u_n \xrightarrow{d_n} u_{n+1}$,
```math
b u_n + d_n = \alpha_n M + u_{n+1} \qquad (\forall n \bmod P).
```
Let $x_n := \{b^n r\}$ (so $b x_n = \alpha_n + x_{n+1}$). Subtracting $u_{n+1} / M = (b u_n + d_n) / M - \alpha_n$ yields the exact linear recurrence for $\Delta_n := M x_n - u_n$:
```math
\Delta_{n+1} = b \Delta_n - d_n \implies \Delta_n = \frac{1}{b^P - 1} \sum_{j=0}^{P-1} d_{n + j} b^{P - 1 - j},
```
verified directly by $b \Delta_n - \Delta_{n+1} = d_n$ and uniqueness of the $P$-periodic solution. Since $d_j \in \{0, \dots, b - 1\}$ for all $j$, we obtain $0 \le \Delta_n \le 1$, with $\Delta_n = 0 \iff d_j = 0$ for all $j$, and $\Delta_n = 1 \iff d_j = b - 1$ for all $j$. By hypothesis the digit labels $(d_j)$ are neither identically $0$ nor identically $b - 1$, so $0 < \Delta_n < 1$ for every $n$, i.e., $u_n / M < x_n < (u_n + 1) / M$. $\square$

*Remark (necessity of the digit-label hypothesis).* Whenever $\gcd(b - 1, M) > 1$ (which holds for every $b \ge 3$ since $(b - 1) \mid Q \mid M$), $\mathcal{G}_{b, M}$ carries additional non-extreme self-loops: $0$-labelled loops at vertices $u$ with $(b - 1) u \equiv 0 \pmod M$, and $(b - 1)$-labelled loops at vertices $u$ with $(b - 1)(u + 1) \equiv 0 \pmod M$. For example, in $\mathcal{G}_{3, 6}$ ($b = 3, L = 1$), vertex $u = 3$ has a $0$-labelled loop $3 \xrightarrow{0} 3$ and vertex $u = 2$ has a $2$-labelled loop $2 \xrightarrow{2} 2$; both constant walks give $r = 1/2$, landing on the cell boundary $u/M = 1/2$ rather than in the strict interior. Requiring $(d_n)$ not all $0$ and not all $b - 1$ excludes all such boundary walks.

**Lemma 2.2 (Simultaneous exact $L$-normality of all $s r$, $1 \le s < b$).** *If the closed walk of Lemma 2.1 visits every vertex $u \in V_M$ the exact same number of times $P / M$ (for instance, every directed edge of $\mathcal{G}_{b, M}$ exactly $R$ times, so $P = R b M$), then for **every** $s \in \{1, \dots, b - 1\}$, the orbit $\mu(s r; b)$ is **exact $L$-normal**: every length-$L$ word $w \in \{0, \dots, b - 1\}^L$ occurs exactly $P / b^L$ times.*

*Proof.* Fix $s \in \{1, \dots, b - 1\}$ and any length-$L$ word $w$ with $b$-adic cylinder $C_w = [k / b^L, (k + 1) / b^L)$. The preimage of $C_w$ under multiplication by $s$ modulo $1$ is
```math
\{x \in [0, 1) : \{s x\} \in C_w\} = \bigsqcup_{j=0}^{s-1} \left[\frac{j + k / b^L}{s},\; \frac{j + (k + 1) / b^L}{s}\right).
```
Because $s \mid Q$, we have $M / (s b^L) = Q / s \in \mathbb{Z}_{\ge 1}$, so every endpoint $(j b^L + k) / (s b^L) = (Q / s)(j b^L + k) / M$ is an integer multiple of $1 / M$. Hence the preimage is an exact disjoint union of $s \cdot (Q / s) = Q$ grid cells $J_u$ ($u \in V_M$). By Lemma 2.1, every orbit point $x_n = \{b^n r\}$ lies in the strict interior of $J_{u_n}$, so $\{s x_n\} \in C_w$ holds if and only if $u_n$ lies in the corresponding set of $Q$ vertices. Since each vertex $u \in V_M$ is visited $P / M$ times, the word $w$ occurs in $\{b^n (s r)\}$ exactly $Q \cdot (P / M) = P / b^L$ times. $\square$

**Completing the proof of Theorem 3(b).**
1. In $\mathcal{G}_{b, M}$, every vertex $u$ has $\deg^+(u) = \deg^-(u) = b$. Deleting the two extreme self-loops $0 \xrightarrow{0} 0$ and $(M - 1) \xrightarrow{b - 1} (M - 1)$ yields $\mathcal{G}_{b, M}^*$, which remains balanced ($\deg^+(u) = \deg^-(u) \ge b - 1 \ge 1$) and strongly connected (from any $u$, choosing digits $d_0, \dots, d_{t-1}$ maps $u$ to $(b^t u + \sum d_j b^{t-1-j}) \bmod M$, which surjects onto $V_M$ once $b^t \ge M$, avoiding the deleted self-loops by choosing the first step away from $0$ or $M - 1$). Hence $\mathcal{G}_{b, M}^*$ has an Eulerian circuit $C_M^*$ of exact length $b M - 2$ visiting both $0$ and $M - 1$.
2. Fix $R \ge 1$, traverse $R$ copies of $C_M^*$ while inserting $R$ consecutive $(0 \xrightarrow{0} 0)$ loops at $0$ and $R$ consecutive $(M - 1 \xrightarrow{b-1} M - 1)$ loops at $M - 1$, giving a closed walk of length $P = R b M$ that traverses every edge of $\mathcal{G}_{b, M}$ exactly $R$ times (hence visits every vertex $u \in V_M$ exactly $R b = P / M$ times). Because the walk uses every edge of $\mathcal{G}_{b, M}$, its edge digit labels $(d_n)$ include every digit $0, 1, \dots, b - 1$ (in particular not all $0$ and not all $b - 1$), so Lemma 2.1 and Lemma 2.2 apply.
3. Rotate the walk so that the last vertex $u_{P-1}$ satisfies $\alpha_{P-1} = \lfloor b u_{P-1} / M \rfloor = 1$ (which always exists since $M \ge 2$ and every vertex is visited). Then $A = \sum_{n=0}^{P-1} \alpha_n b^{P-1-n} \equiv 1 \pmod b$, so $\gcd(A, b) = 1$, and reducing $r = A / (b^P - 1)$ yields $\gcd(b, A_{\mathrm{red}} D_{\mathrm{red}}) = 1$.
4. Apply universal repunit inversion (Proposition 1.3) to $r$ to obtain irrational $x \in M_b \subset K_b$ and $y = 1/x$. Since every clean block of $y$ stays within $W_\infty^{[0,1)}$-distance $\delta_k \to 0$ of $\mu(s r; b)$ ($1 \le s \le b - 1$), and by `coprime_rat_cylinder_margin` each orbit $\mu(s r; b)$ is separated from cylinder boundaries, every $L$-word frequency converges along all $N$: $f_w(N; 1/x, b) \to b^{-L}$. Thus $1/x$ is exact $L$-normal.
5. Finally, to verify $D^-(1/x; b) > 0$, observe that inside the $R$ consecutive $(0 \xrightarrow{0} 0)$ loops, the first $R - k_R$ steps satisfy $0 < \{b^n r\} < b^{-k_R}$ (with $k_R := \lceil \log_b R \rceil$), so for every $1 \le s \le b - 1$, $0 < \{b^n (s r)\} = s \{b^n r\} < b \cdot b^{-k_R} =: \eta_R$. Similarly, the first $R - k_R$ steps of the $(M - 1)$-loop block satisfy $1 - b^{-k_R} < \{b^n r\} < 1$, so $1 - \eta_R < \{b^n (s r)\} < 1$ for every $1 \le s \le b - 1$. Therefore the single common interval $I_R := [\eta_R, 1 - \eta_R)$ simultaneously misses at least $2(R - k_R)$ out of $P = R b M$ points in every orbit $\mu(s r; b)$ ($1 \le s \le b - 1$). Consequently, every convex combination $\nu = \sum_{s=1}^{b-1} \theta_s \mu(s r; b)$ satisfies
   ```math
   D(\nu) \ge |I_R| - \nu(I_R) \ge (1 - 2\eta_R) - \left(1 - \frac{2(R - k_R)}{R b M}\right) = \frac{2}{b M} - \frac{2 k_R}{R b M} - \frac{2 b}{R}.
   ```
   Choosing $R$ sufficiently large makes the lower bound strictly positive, establishing $0 < D^-(1/x; b) \le D^+(1/x; b) \le 2 b^{-L}$. $\square$

#### Part (c): Primitive-root exact convergent $L$-normal reciprocals and quadratic-reciprocity obstruction
*Literature note.* Uniform $L$-word distribution and period structure for full-reptend fractions $1/p$ with $p \equiv 1 \pmod{b^L}$ are classical elementary properties of repeating radix expansions (cf. Gauss's *Disquisitiones Arithmeticae* and Hardy–Wright, §9.12), and the quadratic-reciprocity obstruction follows directly from Euler's criterion and Gauss's law of quadratic reciprocity. As an implication, Theorem 3(c) is unconditional; infinitude of such primes in the unobstructed residue classes is an Artin-type question not addressed here.

Suppose $p = k b^L + 1$ is an odd prime such that $\operatorname{ord}_p(b) = p - 1$ (so $b$ is a primitive root mod $p$, automatically implying $2 \in \langle b \rangle \pmod p$). Then the periodic orbit of $r = 1/p$ visits every reduced fraction $\{a / p : 1 \le a \le p - 1\}$ exactly once. For each $b$-adic cylinder $C_w = [m / b^L, (m + 1) / b^L)$ ($0 \le m < b^L$), the inequalities $m k b^L = m(p - 1) < m p < (m k + 1) b^L = m p + (b^L - m)$ show that the integers $a \in \{1, \dots, p - 1\}$ with $a / p \in C_w$ are precisely $m k + 1 \le a \le (m + 1) k$. Hence every $L$-word $w$ occurs exactly $k = (p - 1) / b^L$ times. Moreover, for the sorted points $a / p$ ($a = 1, \dots, p - 1$), we have $\max_{1 \le a \le p - 1} (\frac{a}{p - 1} - \frac{a}{p}) = 1 - \frac{p - 1}{p} = \frac{1}{p}$ and $\min_{1 \le a \le p - 1} (\frac{a - 1}{p - 1} - \frac{a}{p}) = 0 - \frac{1}{p} = -\frac{1}{p}$, so $D(\mu(1/p; b)) = 2/p$ exactly. Applying Theorem 1 gives an irrational $x = p \prod_{j \ge 1} (1 + b^{-m_j})^{-1} \in M_b \subset K_b$ whose reciprocal $1/x$ is exact $L$-normal with exact convergent discrepancy $\lim_{N\to\infty} D_N(1/x; b) = 2/p$.

**Quadratic-reciprocity obstruction.** Write $b = 2^e b_{\mathrm{odd}}$ ($b_{\mathrm{odd}}$ odd) and suppose $p = k b^L + 1$ is an odd prime.
1. If $b \equiv 1 \pmod 4$ ($e = 0$): $p \equiv 1 \pmod{b}$, so by quadratic reciprocity $\left(\frac{b}{p}\right) = \left(\frac{p}{b}\right) = \left(\frac{1}{b}\right) = +1$ for all $L \ge 1$.
2. If $b \equiv 0 \pmod 4$ ($e \ge 2$): $p \equiv 1 \pmod 4$ and $p \equiv 1 \pmod{b_{\mathrm{odd}}}$, so $\left(\frac{b_{\mathrm{odd}}}{p}\right) = \left(\frac{p}{b_{\mathrm{odd}}}\right) = +1$; if $e$ is even then $\left(\frac{2^e}{p}\right) = +1$, while if $e \ge 3$ is odd then $8 \mid b \mid (p - 1)$ so $\left(\frac{2}{p}\right) = +1$ as well. Hence $\left(\frac{b}{p}\right) = +1$ for all $L \ge 1$.
3. If $b \equiv 2 \pmod 4$ ($e = 1$) and $L \ge 3$: $8 \mid b^L \mid (p - 1)$ and $b_{\mathrm{odd}} \mid (p - 1)$, so $\left(\frac{2}{p}\right) = +1$ and $\left(\frac{b_{\mathrm{odd}}}{p}\right) = \left(\frac{p}{b_{\mathrm{odd}}}\right) = +1$, giving $\left(\frac{b}{p}\right) = +1$.

In all three regimes, $b$ is a quadratic residue mod $p$ and can **never** be a primitive root modulo any $p = k b^L + 1$.

#### Part (d): The $R_0 = 1$ obstruction for $(b, L) \neq (2, 1)$
Suppose a reciprocal $y$ has a weak\* limit point of the form $\nu = (1 - \gamma)\lambda + \gamma \delta_0$ with $\gamma > 0$ (as produced by all $R_0 = 1$ signed or cyclotomic products in Phase 22). Since $\delta_0$ puts its entire mass $1$ into the closure of the two extreme cylinders $C_{0^L} \cup C_{(b-1)^L}$, any sequence of empirical measures $\mu_{N_j}^{\mathrm{emp}}(y; b) \Rightarrow \nu$ satisfies
```math
\liminf_{j \to \infty} \big(f_{0^L}(N_j; y, b) + f_{(b-1)^L}(N_j; y, b)\big) \ge (1 - \gamma) \cdot 2 b^{-L} + \gamma = 2 b^{-L} + \gamma(1 - 2 b^{-L}).
```
Whenever $(b, L) \neq (2, 1)$, we have $b^L \ge 3$ and hence $1 - 2 b^{-L} > 0$, contradicting $L$-normality ($f_{0^L} + f_{(b-1)^L} = 2 b^{-L}$). Only at $(b, L) = (2, 1)$ does $2 b^{-L} = 1$, which is why Phase 22's signed-factor construction succeeded in base $2$ at $L = 1$ and could never extend directly to $b \ge 3$ or $L \ge 2$.

---

## 3. Sub-track D4(i): Bang–Zsigmondy Rigidity and the Hull–Dobell Family

Phase 22 established normality of $y = \prod_{k \ge 1} (1 - b^{-m_k})^{-1}$ under the full divisibility hypothesis $D_{k-1} \mid (b^{m_k} - 1)$ (where $D_k = \prod_{j=1}^k (b^{m_j} - 1)$). While the Lean-verified period-lifting theorem `RadixPowerTower.orderOf_mul_pow_sub_one` assumes full divisibility $D_{k-1} \mid (b^{m_k} - 1)$, the same exact period formula $T_k = m_k D_{k-1}$ holds under the weaker Hull–Dobell hypothesis **(HD1)** $\operatorname{rad}^*(D_{k-1}) \mid (b^{m_k} - 1)$ (proved below as Lemma 3.2; cf. Phase 22 Theorem 1(1)). It is therefore natural to ask whether relaxing $D_{k-1} \mid (b^{m_k} - 1)$ to **(HD1)** escapes the Phase 22 tetration growth regime. Theorem 4 shows that **(HD1)** still gives normality under **(HD2)** $T_{k-1} / m_k \to 0$, **but** Bang–Zsigmondy rigidity locks the exponent schedule into a divisibility chain $m_{k-1} \mid m_k$, and the sufficient conditions **(HD1)**–**(HD2)** still enforce eventual tetration growth.

### 3.1 Proof of Bang–Zsigmondy rigidity and Hull–Dobell period lifting

**Lemma 3.1 (Bang–Zsigmondy rigidity).** *For every integer $b \ge 2$ and all integers $m, n \ge 1$,*
```math
\operatorname{rad}^*(b^m - 1) \mid (b^n - 1) \iff m \mid n.
```

*Proof.* The direction $(\Leftarrow)$ is immediate since $m \mid n \implies (b^m - 1) \mid (b^n - 1)$ and $\operatorname{rad}^*(b^m - 1) \mid (b^m - 1)$.

For $(\Rightarrow)$, suppose $\operatorname{rad}^*(b^m - 1) \mid (b^n - 1)$. We check the three exceptional regimes of Bang (1886) and Zsigmondy (1892) directly:
1. $m = 1$: $1 \mid n$ holds unconditionally for all $n \ge 1$ (including $b = 2$, where $\operatorname{rad}^*(1) = 1$).
2. $m = 2$ and $b + 1 = 2^t$ ($t \ge 2$): then $b \equiv 3 \pmod 4$, so $v_2(b - 1) = 1$ whereas $b^2 - 1 = (b - 1)(b + 1)$ is divisible by $2 \cdot 4 = 8$, hence $4 \mid \operatorname{rad}^*(b^2 - 1)$. If $n$ were odd, then $b^n - 1 \equiv 3 - 1 = 2 \pmod 4$, contradicting $4 \mid (b^n - 1)$. Thus $2 \mid n$.
3. $(b, m) = (2, 6)$: here $2^6 - 1 = 63 = 3^2 \cdot 7$, so $\operatorname{rad}^*(63) = 21$. Since $\operatorname{ord}_3(2) = 2$ and $\operatorname{ord}_7(2) = 3$, $21 \mid (2^n - 1)$ implies $\operatorname{lcm}(2, 3) = 6 \mid n$.

In every remaining case, Bang–Zsigmondy's theorem guarantees the existence of a **primitive prime divisor** $p \mid (b^m - 1)$ such that $p \nmid (b^d - 1)$ for all $1 \le d < m$, i.e., $\operatorname{ord}_p(b) = m$. Since $p \mid \operatorname{rad}^*(b^m - 1) \mid (b^n - 1)$, we conclude $m = \operatorname{ord}_p(b) \mid n$. $\square$

**Lemma 3.2 (Hull–Dobell period lifting; paper proof).** *For all integers $b \ge 2$ and $m, D \ge 1$ with $\gcd(b, D) = 1$ and $\operatorname{rad}^*(D) \mid (b^m - 1)$,*
```math
D \mid \frac{b^{t m} - 1}{b^m - 1} \iff D \mid t \qquad (\forall t \ge 1), \qquad \operatorname{ord}_{D(b^m - 1)}(b) = m D.
```
*Moreover, the partial geometric sums $S_i(b^m) := \sum_{j=0}^i b^{j m} \bmod D$ ($0 \le i < D$) form a bijection onto $\mathbb{Z}/D\mathbb{Z}$.*

*Proof.* Set $q := b^m \ge 2$. First, for every integer $N \ge 1$, $(b^m - 1) \mid (b^N - 1) \iff m \mid N$: writing $N = t m + r$ with $0 \le r < m$ gives $b^N - 1 = b^r(b^{t m} - 1) + (b^r - 1)$ with $0 \le b^r - 1 < b^m - 1$, so divisibility holds iff $r = 0$. Writing $N = t m$ ($t \ge 1$), we have $D(b^m - 1) \mid (b^N - 1)$ iff $D \mid \frac{q^t - 1}{q - 1}$. Checking each prime power $p^e \parallel D$ ($e \ge 1$):
- **Odd prime $p \mid D$:** $p \mid \operatorname{rad}^*(D) \mid (q - 1)$, so lifting the exponent (LTE) gives $v_p\!\left(\frac{q^t - 1}{q - 1}\right) = v_p(t)$, hence $p^e \mid \frac{q^t - 1}{q - 1} \iff p^e \mid t$.
- **$p = 2$ and $v_2(D) = 1$ ($e = 1$):** $2 \mid \operatorname{rad}^*(D) \mid (q - 1)$ implies $q$ is odd, so $\frac{q^t - 1}{q - 1} = \sum_{j=0}^{t-1} q^j \equiv t \pmod 2$, giving $2 \mid \frac{q^t - 1}{q - 1} \iff 2 \mid t$.
- **$p = 2$ and $v_2(D) \ge 2$ ($4 \mid D$):** $4 \mid \operatorname{rad}^*(D) \mid (q - 1)$, so $2$-adic LTE gives $v_2\!\left(\frac{q^t - 1}{q - 1}\right) = v_2(t)$, hence $2^e \mid \frac{q^t - 1}{q - 1} \iff 2^e \mid t$.

Multiplying over all prime powers $p^e \parallel D$ yields $D \mid \frac{q^t - 1}{q - 1} \iff D \mid t$, and therefore $D(b^m - 1) \mid (b^N - 1) \iff m D \mid N$ for all $N \ge 1$. Since $\gcd(b, D(b^m - 1)) = 1$, the least positive such $N$ is $\operatorname{ord}_{D(b^m - 1)}(b) = m D$ (including $D(b^m - 1) = 1$ when $b = 2, m = 1, D = 1$). Finally, for $0 \le i_1 < i_2 < D$, $S_{i_2}(q) - S_{i_1}(q) = q^{i_1 + 1} \frac{q^{i_2 - i_1} - 1}{q - 1}$; since $\gcd(q, D) = 1$, this is divisible by $D$ iff $D \mid (i_2 - i_1)$, which is impossible for $0 < i_2 - i_1 < D$. Hence $i \mapsto S_i(q) \bmod D$ is a bijection on $\mathbb{Z}/D\mathbb{Z}$. $\square$

### 3.2 Proof of Theorem 4 (Hull–Dobell characterization, normality, and growth under (HD1)–(HD2))

**Characterization of (HD1).** Since $\operatorname{rad}^*(D_{k-1}) = \operatorname{lcm}_{j < k} \operatorname{rad}^*(b^{m_j} - 1)$ except possibly at the prime $2$ (when $4 \mid D_{k-1}$ even though $4 \nmid (b^{m_j} - 1)$ for each $j < k$), Lemma 3.1 implies that $\operatorname{rad}^*(b^{m_j} - 1) \mid (b^{m_k} - 1)$ for all $j < k$ is equivalent to $m_j \mid m_k$ for all $j < k$ (equivalently $m_{k-1} \mid m_k$ by induction). The sole extra $2$-adic condition occurs when $b \equiv 3 \pmod 4$ and $m_1, m_2$ are odd: then $v_2(b^{m_1} - 1) = v_2(b^{m_2} - 1) = 1$, so $4 \mid D_2$ even though $4 \nmid (b^{m_j} - 1)$ ($j = 1, 2$), forcing $4 \mid (b^{m_3} - 1)$, i.e., $2 \mid m_3$ (and hence $2 \mid m_k$ for all $k \ge 3$).

**Exact period and normality under (HD1)–(HD2).** Under **(HD1)**, applying Lemma 3.2 at each step $k \ge 1$ (with $D = D_{k-1}$, $D_0 := 1$) gives $T_k := \operatorname{ord}_{D_k}(b) = m_k D_{k-1}$ for all $k \ge 1$, and implies that $\widehat{C}_{k-1}(H) = 0$ whenever $D_{k-2} \nmid H$ ($k \ge 2$): writing $R_{k-1} = R_{k-2} \frac{b^{m_{k-1}}}{b^{m_{k-1}} - 1}$, the $D_{k-2}$ bands $0 \le i < D_{k-2}$ at fixed $r < m_{k-1}$ shift the $D_{k-2}$-component by $S_i(b^{m_{k-1}}) \bmod D_{k-2}$, which runs bijectively over $\mathbb{Z}/D_{k-2}\mathbb{Z}$ by Lemma 3.2 (forming a shifted uniform $D_{k-2}$-point grid). At step $k \ge 2$, define $S_i(q) := 1 + q + \dots + q^i$. Because $\operatorname{rad}^*(D_{k-1}) \mid (b^{m_k} - 1)$ ensures $p \mid (b^{m_k} - 1)$ for every odd prime $p \mid D_{k-1}$ and $4 \mid (b^{m_k} - 1)$ whenever $4 \mid D_{k-1}$, LTE (and $S_i(b^{m_2}) \equiv i + 1 \pmod 2$ when $v_2(D_{k-1}) = 1$) yields for **every** divisor $d' \mid D_{k-1}$ (in particular $d' := D_{k-2} / \gcd(h, D_{k-2})$),
```math
d' \mid S_i(b^{m_k}) \iff d' \mid (i + 1).
```
Now apply the band-averaging framework of Phase 22 Theorem 2 (`notes/phase22/normal-reciprocals-and-signs.md`, §2) to the exact band identity $b^{i m_K + r} R_K \equiv S_i(b^{m_K}) b^r R_{K-1} + \frac{b^r R_{K-1}}{b^{m_K} - 1} \pmod 1$ for $N = I m_K + r_0 \in [m_K, m_{K+1})$ ($I \ge 1, 0 \le r_0 < m_K$). Because **(HD1)** does not force $T_{K-1} \mid m_K$, we account for incomplete periods explicitly: on each of the $I$ complete bands $0 \le i < I$, writing $m_K = q_K T_{K-1} + u_K$ ($0 \le u_K < T_{K-1}$) leaves at most $T_{K-1}$ extra steps (contributing at most $I T_{K-1} / N \le T_{K-1} / m_K$ in total), while on the $q_K$ complete periods $\widehat{C}_{K-1}(h S_i(b^{m_K})) = 0$ unless $d' \mid (i + 1)$. On the partial final band $0 \le r < r_0$, writing $r_0 = q' T_{K-1} + u'$ ($0 \le u' < T_{K-1}$) leaves at most $T_{K-1}$ extra steps (contributing at most $T_{K-1} / N \le T_{K-1} / m_K$), while the $q'$ complete periods vanish unless $d' \mid (I + 1)$. Combining these two incomplete-period remainders ($2 T_{K-1} / m_K$) with the exact partial-band inequality $(m_K \lfloor I / d' \rfloor + r_0 \mathbf{1}[d' \mid (I + 1)]) / N \le 1 / d'$ (Phase 22, Lemma 2.1), the per-band tail error $c_b(h) / m_K$, and the approximation error $|y - R_K| \le 16 b^{-m_{K+1}}$ (contributing $\le 2 c_b(h) / m_K$) gives, for all $N \in [m_K, m_{K+1})$,
```math
|W_h(N)| \le \frac{\gcd(h, D_{K-2})}{D_{K-2}} + \frac{2 T_{K-1} + 3 c_b(h)}{m_K}.
```
Under **(HD2)** ($T_{K-1} / m_K \to 0$), this vanishes for every $h \neq 0$, proving base-$b$ normality of $y$.

**All-prefix proof that $x = 1/y \in M_b \subset K_b$.** We prove a general bound for any all-minus product $x = \prod_{j=1}^\infty (1 - b^{-m_j})$ with $m_{j+1}/m_j \to \infty$ (which holds under **(HD1)–(HD2)** since $m_{j+1}/m_j \ge m_{j+1}/T_j \to \infty$, and likewise in Theorems 5 and 6(b)). Let $X_k := \prod_{j=1}^k (1 - b^{-m_j}) \in (0, 1)$ and $S_k := \sum_{j=1}^k m_j$. Since $b^{S_k} X_k = \prod_{j=1}^k (b^{m_j} - 1) \in \mathbb{Z}$, we have $b^n X_k \in \mathbb{Z}$ for every $n \ge S_k$, and $0 < X_k - x = X_k \big(1 - \prod_{j \ge k+1}(1 - b^{-m_j})\big) \le \sum_{j \ge k+1} b^{-m_j} \le 2 b^{-m_{k+1}}$. Because $m_{k+1}/m_k \to \infty$, we have $S_k = (1 + o(1)) m_k = o(m_{k+1})$, so $S_k < m_{k+1}$ for all large $k$. For **any** $N \in [m_{k+1}, m_{k+2})$, partition $[0, N)$ into up to four ranges:
1. $[0, S_k)$: at most $S_k$ indices, each with $\|b^n x\|_{\mathbb{T}} \le 1/2$;
2. $[S_k, m_{k+1})$: here $b^n X_k \in \mathbb{Z}$, so $\|b^n x\|_{\mathbb{T}} \le b^n(X_k - x) \le 2 b^{n - m_{k+1}}$, summing to $\le \sum_{t=1}^\infty 2 b^{-t} \le 2$;
3. $[m_{k+1}, \min(N, S_{k+1}))$: since $S_{k+1} = S_k + m_{k+1}$, at most $S_k$ indices, each contributing $\le 1/2$;
4. $[S_{k+1}, N)$ (if $N > S_{k+1}$): here $b^n X_{k+1} \in \mathbb{Z}$ and $n < m_{k+2}$, so $\|b^n x\|_{\mathbb{T}} \le b^n(X_{k+1} - x) \le 2 b^{n - m_{k+2}}$, summing to $\le 2$.

Summing across all four ranges yields, for **every** $N \in [m_{k+1}, m_{k+2})$,
```math
W_1\big(\mu_N^{\mathrm{emp}}(x; b), \delta_0\big) = \frac{1}{N} \sum_{n=0}^{N-1} \|b^n x\|_{\mathbb{T}} \le \frac{S_k + 4}{N} \le \frac{S_k + 4}{m_{k+1}} \longrightarrow 0.
```
(On $[0, 1]$, $\{b^n x\} = 1 - b^n(X_k - x)$ accumulates at $1^-$, i.e., $\delta_1$ on $[0, 1]$ and $\delta_0$ on $\mathbb{T}$.) By Markov's inequality, $D_N(x; b) \ge 1 - \sqrt{8 W_1(\mu_N^{\mathrm{emp}}(x; b), \delta_0)} \to 1$, establishing $x \in M_b \subset K_b$ in the repository's full-limit sense.

**Growth forced by the sufficient conditions (HD1)–(HD2).** Even when $D_{k-1} \nmid (b^{m_k} - 1)$ strictly, **(HD1)** and Lemma 3.1 force $m_{k-1} \mid m_k$ for all $k \ge 2$, hence $(b^{m_{k-1}} - 1) \mid (b^{m_k} - 1)$ and $S_i(b^{m_k}) \equiv i + 1 \pmod{b^{m_{k-1}} - 1}$ identically. Independently, because **(HD1)** forces $T_k = m_k D_{k-1}$ with $D_{k-1} = \prod_{j < k} (b^{m_j} - 1) \ge b^{m_{k-1}} / 2$, the sufficient normality hypothesis **(HD2)** ($m_k / T_{k-1} \to \infty$) implies $m_k > T_{k-1}$ for all $k \ge k_0$, forcing eventual tetration growth
```math
m_k > T_{k-1} = m_{k-1} D_{k-2} \ge \frac{1}{2} b^{m_{k-2}} \qquad (k \ge k_0),
```
so the active stage index $K(N)$ grows only as $O(\log^* N)$. Thus the sufficient conditions **(HD1)**–**(HD2)** used in Theorem 4 force tetration growth; whether Hull–Dobell products with slower growth (violating **(HD2)**) are base-$b$ normal is not addressed by this method. $\square$

---

## 4. Sub-track D4(ii): Anchored Coprime Non-Tetration Normal Reciprocals in Every Base $b \ge 2$

To escape the tetration growth $m_{k+1} \ge b^{m_{k-1}} / 2$ forced by the sufficient conditions **(HD1)–(HD2)** whenever $\operatorname{rad}^*(D_{k-1}) \mid (b^{m_k} - 1)$ and $T_{k-1} / m_k \to 0$, we must **stop** forcing the full prime support of $D_{k-1}$ to divide $b^{m_k} - 1$. Instead, we anchor every exponent $m_k = s q_k$ to a single fixed period $s$ (generating a fixed anchor modulus $M := b^s - 1 \ge 3$ whose lifted powers $M^{k-1}$ supply exact Fourier vanishing off $M^{k-1}\mathbb{Z}$) while making the cofactors $q_k$ **pairwise coprime** so the remaining factors $\widetilde{d}_k := (b^{m_k} - 1) / M$ never accumulate multiplicative period explosions!

### 4.1 Proof of Theorem 5

Fix $b \ge 2$. Recall $s_b = 1$ if $b \ge 4$ and $b \not\equiv 3 \pmod 4$, and $s_b = 2$ otherwise. For any multiple $s$ of $s_b$, set $M := b^s - 1$. Notice:
- $M \ge 3$ always (at $b = 2, s = 2$: $M = 3$; at $b = 3, s = 2$: $M = 8$; at $b = 4, s = 1$: $M = 3$; at $b = 5, s = 1$: $M = 4$).
- Whenever $2 \mid M$, we have $4 \mid M$: if $b$ is even then $M$ is odd; if $b \equiv 1 \pmod 4$ then $4 \mid (b - 1) \mid M$; if $b \equiv 3 \pmod 4$ then $2 \mid s$, so $8 \mid (b^2 - 1) \mid M$.
- Hence $\operatorname{rad}^*(M) \mid M$, and by LTE, for every $k \ge 1$ and every prime $p \mid M$:
  ```math
  v_p(b^{s n} - 1) = v_p(M) + v_p(n) \qquad (\forall n \ge 1), \qquad \operatorname{ord}_{M^k}(b) = s M^{k-1}.
  ```
  Indeed, $\operatorname{ord}_M(b) = s$ (since $b^d - 1 < b^s - 1 = M$ for $1 \le d < s$); if $M^k \mid (b^n - 1)$ then $s \mid n$, so writing $n = s u$ gives $k v_p(M) \le v_p(M) + v_p(u)$ for every $p \mid M$, hence $M^{k-1} \mid u$ and $s M^{k-1} \mid n$.

Now construct $(q_k)_{k \ge 1}$ recursively: pick $q_1 \ge 5$ with $\gcd(q_1, s M) = 1$, and for $k \ge 2$ set
```math
q_k := \omega_{k-1} \frac{T_{k-1}}{s} + 1, \qquad m_k := s q_k = \omega_{k-1} T_{k-1} + s, \qquad T_k := s M^{k-1} \prod_{j=1}^k q_j,
```
where $\omega_k \ge 1$ satisfies $s M \mid \omega_1$, $s \mid \omega_{k-1}$ ($k \ge 3$), and $\omega_k \to \infty$.

**Step 1: Exact pairwise coprime factorization and exact period $T_k$.**
For every $k \ge 2$, $\gcd(q_k, s M \prod_{j < k} q_j) = 1$: at $k = 2$, $s M \mid \omega_1$ gives $q_2 = \omega_1 q_1 + 1 \equiv 1 \pmod{s M q_1}$; for $k \ge 3$, $M \prod_{j < k} q_j \mid (T_{k-1} / s)$ and $s \mid \omega_{k-1}$ give $q_k \equiv 1 \pmod{s M \prod_{j < k} q_j}$. Thus $q_1, q_2, \dots$ are pairwise coprime and each $q_k$ is coprime to $s M$.

Set $\widetilde{d}_k := (b^{s q_k} - 1) / M$. Then:
1. **$\gcd(\widetilde{d}_k, M) = 1$:** For every prime $p \mid M$, LTE gives $v_p(b^{s q_k} - 1) = v_p(M) + v_p(q_k) = v_p(M)$, so $p \nmid \widetilde{d}_k$.
2. **$\gcd(\widetilde{d}_j, \widetilde{d}_k) = 1$ for $j < k$:** We have $\gcd(b^{s q_j} - 1, b^{s q_k} - 1) = b^{\gcd(s q_j, s q_k)} - 1 = b^s - 1 = M$, so dividing by $M$ leaves $\gcd(\widetilde{d}_j, \widetilde{d}_k) = 1$.
3. **Order contribution of $\widetilde{d}_k$:** Let $d := \operatorname{ord}_{\widetilde{d}_k}(b) \mid s q_k$. Because $\gcd(M, \widetilde{d}_k) = 1$, $\operatorname{lcm}(s, d) = \operatorname{ord}_{b^{s q_k} - 1}(b) = s q_k$; since $\gcd(s, q_k) = 1$, this forces $q_k \mid d \mid s q_k$.

Hence $D_k = \prod_{j=1}^k (b^{m_j} - 1) = M^k \prod_{j=1}^k \widetilde{d}_j$ is a pairwise coprime factorization with exact multiplicative order
```math
\operatorname{ord}_{D_k}(b) = \operatorname{lcm}\!\left(s M^{k-1},\; \operatorname{ord}_{\widetilde{d}_1}(b), \dots, \operatorname{ord}_{\widetilde{d}_k}(b)\right) = s M^{k-1} \prod_{j=1}^k q_j = T_k.
```

**Step 2: Exact CRT Fourier vanishing off $M^{k-1}\mathbb{Z}$ and complete-period discrepancy $\le M^{-(k-1)}$.**
Write $D_k = M^k \cdot U_k$ where $U_k := \prod_{j=1}^k \widetilde{d}_j$ is coprime to $M$, and set $L_k := s \prod_{j=1}^k q_j$. Then $T_k = M^{k-1} L_k$, $b^{L_k} \equiv 1 \pmod{U_k}$, and since $\gcd(L_k / s, M) = 1$, LTE gives $v_p(b^{L_k} - 1) = v_p(M)$ for every $p \mid M$, so $b^{L_k} = 1 + u_k M$ with $\gcd(u_k, M) = 1$ (and $4 \mid M$ whenever $2 \mid M$). As $t$ runs over $\{0, \dots, M^{k-1} - 1\}$, $b^{t L_k} \bmod M^k$ therefore runs bijectively over $1 + M\mathbb{Z} / M^k \mathbb{Z}$ while fixing the $U_k$-component of $R_k = b^{\sum m_j} / D_k$. Writing $b^{n_0} R_k \equiv \frac{a_0}{M^k} + \frac{c_0}{U_k} \pmod 1$ with $\gcd(a_0, M) = 1$, each coset $\{b^{n_0 + t L_k} R_k \bmod 1 : 0 \le t < M^{k-1}\}$ is an exact shifted $M^{k-1}$-point uniform arithmetic progression
```math
\left\{\theta(n_0) + \frac{j}{M^{k-1}} \bmod 1 \;:\; 0 \le j < M^{k-1}\right\}.
```
Every shifted $M^{k-1}$-grid has Fourier coefficients vanishing identically whenever $M^{k-1} \nmid h$, and extreme interval discrepancy $\le M^{-(k-1)}$. Averaging uniformly over the $L_k$ cosets yields
```math
\widehat{C}_k(h) = 0 \quad \text{whenever } M^{k-1} \nmid h, \qquad D\big(\mu(R_k; b)\big) \le M^{-(k-1)}.
```

**Step 3: Band decomposition, all-prefix Weyl bound, and normality of $y = 1/x$.**
Fix $h \neq 0$ and $N \in [m_K, m_{K+1})$ ($K \ge 3$). Write $N = I m_K + r_0$ with $I \ge 1$ and $0 \le r_0 < m_K$. Because $m_K = \omega_{K-1} T_{K-1} + s$, we have $b^{m_K} \equiv b^s \pmod{D_{K-1}}$, so the exact band identity for $R_K = R_{K-1} \frac{b^{m_K}}{b^{m_K} - 1}$ is
```math
b^{i m_K + r} R_K \equiv S_i(b^s) \, b^r R_{K-1} + \frac{b^r R_{K-1}}{b^{m_K} - 1} \pmod 1 \qquad (i \ge 0,\ 0 \le r < m_K),
```
where $S_i(b^s) := 1 + b^s + \dots + b^{i s} = (b^{(i+1) s} - 1)/(b^s - 1)$. Because $v_p(b^s - 1) = v_p(M)$ (with $4 \mid M$ whenever $2 \mid M$), LTE yields $v_p(S_i(b^s)) = v_p(i + 1)$ for every prime $p \mid M$. Setting $d' := M^{K-2} / \gcd(h, M^{K-2})$, we obtain
```math
M^{K-2} \mid h S_i(b^s) \iff d' \mid S_i(b^s) \iff d' \mid (i + 1).
```
Averaging $e(h b^{i m_K + r} R_K)$ over $0 \le r < m_K = \omega_{K-1} T_{K-1} + s$:
- The $s$ extra steps beyond $\omega_{K-1}$ complete periods of $T_{K-1}$ contribute at most $s / m_K$ per band.
- The tail $h b^r R_{K-1} / (b^{m_K} - 1)$ contributes at most $c_b(h) / m_K$ per band (with $c_b(h) := 4 + 2 \lceil \log_b(4\pi |h| R_\infty) \rceil$).
- On the $\omega_{K-1}$ complete periods of $T_{K-1}$, the average $\widehat{C}_{K-1}(h S_i(b^s))$ vanishes identically unless $d' \mid (i + 1)$.
- Out of the $I$ complete bands $0 \le i < I$, exactly $\lfloor I / d' \rfloor$ satisfy $d' \mid (i + 1)$. On the incomplete band $0 \le r < r_0 < m_K$, write $r_0 = q T_{K-1} + t$ ($0 \le t < T_{K-1}$); the leftover $t$ steps contribute at most $T_{K-1} / N \le T_{K-1} / m_K$. Setting $\theta := r_0 / m_K \in [0, 1)$, if $d' \nmid (I + 1)$ then the $q$ complete periods vanish identically and the surviving band weight is $\lfloor I / d' \rfloor / (I + \theta) \le 1 / d'$; if $d' \mid (I + 1)$ then writing $I + 1 = m d'$ ($m \ge 1$) gives $\lfloor I / d' \rfloor = m - 1$ and
  ```math
  \frac{\lfloor I / d' \rfloor + \theta}{I + \theta} = \frac{m - 1 + \theta}{m d' - 1 + \theta} \le \frac{1}{d'},
  ```
  since $(\theta - 1)(d' - 1) \le 0$.
- Finally, the approximation error $|y - R_K| \le 4 b^{-m_{K+1}}$ over $n < N < m_{K+1}$ contributes at most $2 c_b(h) / m_K$.

Combining all pieces yields the sharp all-prefix Weyl bound
```math
|W_h(N)| \le \frac{\gcd(h, M^{K-2})}{M^{K-2}} + \frac{T_{K-1} + s + 3 c_b(h)}{m_K} \qquad (\forall N \in [m_K, m_{K+1})).
```
Since $M^{K-2} \to \infty$ and $T_{K-1} / m_K < 1 / \omega_{K-1} \to 0$, $W_h(N) \to 0$ for every $h \neq 0$, proving base-$b$ normality of $y$. For $x = 1/y = \prod_{k \ge 1} (1 - b^{-m_k})$, note that $m_{k+1}/m_k > \omega_k \to \infty$, so $S_k := \sum_{j=1}^k m_j = o(m_{k+1})$. By the four-range all-prefix decomposition proved in §3.2, every $N \in [m_{k+1}, m_{k+2})$ satisfies
```math
W_1\big(\mu_N^{\mathrm{emp}}(x; b), \delta_0\big) = \frac{1}{N} \sum_{n=0}^{N-1} \|b^n x\|_{\mathbb{T}} \le \frac{S_k + 4}{N} \le \frac{S_k + 4}{m_{k+1}} \longrightarrow 0
```
(with $\{b^n x\} = 1 - b^n(X_k - x)$ accumulating at $1^-$ in $[0, 1)$, i.e., $\delta_1$ on $[0, 1]$ and $\delta_0$ on $\mathbb{T}$). Hence $\lim_{N\to\infty} D_N(x; b) = 1$ and $x \in M_b \subset K_b$ in the repository's full-limit sense.

**Step 4: Doubly-exponential growth and polylogarithmic discrepancy under $\omega_k = s M^k$.**
Choose the balanced schedule $\omega_k := s M^k$ ($k \ge 1$, so $s M \mid \omega_1$ and $s \mid \omega_{k-1}$ for all $k \ge 3$). Then
```math
T_k = M q_k T_{k-1} = M \left(M^{k-1} T_{k-1} + 1\right) T_{k-1} = M^k T_{k-1}^2 + M T_{k-1}.
```
Dividing $\ln T_k = 2 \ln T_{k-1} + k \ln M + \ln(1 + M^{1-k} / T_{k-1})$ by $2^k$ and summing the convergent series $\sum_{k \ge 2} (k \ln M + O(T_{k-1}^{-1})) / 2^k < \infty$ yields
```math
\ln T_k = (c_* + o(1)) 2^k, \qquad \ln m_k = \ln(\omega_{k-1} T_{k-1} + s) = \left(\frac{c_*}{2} + o(1)\right) 2^k
```
for an explicit constant $c_* = c_*(b, s, q_1) > 0$. This is **doubly exponential (strictly non-tetration)**.

We read off the resulting quantitative rates for $x$ and $y = 1/x$:
1. **Uniform all-$N$ rate for $x \in M_b$:** Since $m_k = s M^{k-1} T_{k-1} + s$ implies $T_{k-1} \asymp m_k / (s M^{k-1})$, we have $T_k \asymp M^k T_{k-1}^2 \asymp m_k^2 / (s^2 M^{k-2})$ and hence $m_{k+1} = s M^k T_k + s \asymp (M^2 / s) m_k^2$. Consequently $S_k = O(m_k) = O_{b,s}(m_{k+1}^{1/2})$. For any $N \in [m_{k+1}, m_{k+2})$ ($k$ large), set $\Delta := \lceil \log_b N \rceil$ (so $2 b^{-\Delta} \le 2 / N < 1/2$ and $\Delta = O_{b,s}(\log_b m_{k+1}) \ll m_{k+1}$). For every $n \in [S_k, m_{k+1} - \Delta) \cup [S_{k+1}, \min(N, m_{k+2} - \Delta))$, we have $\{b^n x\} \in [1 - 2 b^{-\Delta}, 1)$, so the interval $I := [0, 1 - 2 b^{-\Delta})$ contains at most $2 S_k + 2\Delta$ points of $\{b^n x : 0 \le n < N\}$. Therefore
   ```math
   1 - D_N(x; b) \le 1 - \big(|I| - \mu_N^{\mathrm{emp}}(x; b)(I)\big) \le 2 b^{-\Delta} + \frac{2 S_k + 2\Delta}{N} \le \frac{2 S_k + 2 \lceil \log_b N \rceil + 2}{N} = O_{b, s}\!\left(N^{-1/2}\right)
   ```
   uniformly for all $N \ge 2$ (using $S_k = O_{b,s}(m_{k+1}^{1/2}) = O_{b,s}(N^{1/2})$).
2. **All-prefix discrepancy rate for $y = 1/x$ (fixed seed $q_1$):** For $N \in [m_K, m_{K+1})$, we have $\ln N \le \ln m_{K+1} \le (c_* + o(1)) 2^K$ (with $c_* = c_*(b, s, q_1) > 0$), so $2^K \ge (\frac{1}{c_*} - o(1)) \ln N$, which implies
   ```math
   K \ge \log_2 \ln N - O_{b,s,q_1}(1) \implies M^{K-2} \ge c_1(b,s,q_1) (\ln N)^{\log_2 M}.
   ```
   Also $T_{K-1} / m_K < 1 / \omega_{K-1} = 1 / (s M^{K-1}) \le M^{-(K-2)}$. Plugging the Weyl bound into the Erdős–Turán inequality with cutoff $H := M^{K-2}$ gives
   ```math
   D_N(y; b) \le \frac{C}{H} + C \sum_{h=1}^{H} \frac{1}{h} \left(\frac{\gcd(h, H)}{H} + \frac{2}{H} + \frac{3 c_b(h)}{m_K}\right).
   ```
   Observe that
   $$\sum_{h=1}^H \frac{\gcd(h, H)}{h} = \sum_{d \mid H} d \sum_{\substack{1 \le u \le H/d \\ \gcd(u, H/d) = 1}} \frac{1}{d u} \le \sum_{d \mid H} (1 + \ln(H / d)) \le \tau(H) (1 + \ln H).$$
   Because $H = M^{K-2}$ is supported on the fixed finite set of $\omega(M)$ prime factors of $M$, its divisor count is only
   $$\tau(M^{K-2}) = \prod_{p \mid M} \big((K - 2) v_p(M) + 1\big) = O_M\!\left(K^{\omega(M)}\right) = O_M\!\left((\ln\ln N)^{\omega(M)}\right),$$
   while $\ln H = O_M(K) = O_M(\ln\ln N)$ and $\sum_{h=1}^H \frac{c_b(h)}{h m_K} = O_b\left(\frac{(\ln H)^2}{m_K}\right) \ll \frac{1}{H}$. Therefore, with implied constant and onset depending on $b, s, q_1$,
   ```math
   D_N(y; b) = O_{b, s, q_1}\!\left(\frac{\tau(H) \ln H}{H}\right) = O_{b, s, q_1}\!\left(\frac{(\ln\ln N)^{\omega(M) + 1}}{(\ln N)^{\log_2 M}}\right).
   ```
   For each fixed base $b \ge 2$ and real $A > 0$, fixing $s$ to be the least multiple of $s_b$ with $\log_2(b^s - 1) > A$ and $q_1 \ge 5$ to be the least integer coprime to $s M$ produces a base-specific $x = x(b, A) \in M_b \subset K_b$ satisfying $D_N(1/x; b) = O_{b, A}((\ln N)^{-A})$. $\square$

*(Remark: Whereas Phase 22 required $D_{k-1} \mid (b^{m_k} - 1)$ and incurred tetration growth, anchoring on $M = b^s - 1$ in Theorem 5 reduces schedule growth from tetration to doubly exponential $\ln m_k \sim \frac{c_*}{2} 2^k$ while achieving arbitrarily high polylogarithmic discrepancy $(\ln N)^{-A}$.)*

---

## 5. Sub-track D4(iii): Fully Coprime Base-$2$ CRT Convolution, Prime Products, and $R_k^{(E)}$

What happens when we drop **even** the fixed anchor $s$ and take **pairwise coprime** exponents $(m_j)_{j \ge 1}$ in base $2$, or pass all the way to the prime-exponent product $R_k^{(\mathrm{prime})} = \prod_{j=1}^k (1 - 2^{-p_j})^{-1}$ and the ordinary partition partial products $R_k^{(E)} = \prod_{j=1}^k (1 - b^{-j})^{-1}$? Theorem 6 resolves all three.

### 5.1 Universal $01$-transition bound and prime-exponent partial products

**Lemma 5.1 (Universal $01$-transition Fourier bound).** *Let $m \ge 2$ and let $1 \le u \le 2^m - 2$. Define the uniform $\times 2$-orbit sum*
```math
S(u, m) := \frac{1}{m} \sum_{r=0}^{m-1} e\!\left(\frac{2^r u}{2^m - 1}\right).
```
*Then*
```math
\big|S(u, m)\big| \le 1 - \frac{2 - \sqrt{2}}{m}.
```

*Proof.* Write the $m$-bit binary expansion of $u \in \{1, \dots, 2^m - 2\}$ cyclically; since $u \neq 0$ and $u \neq 2^m - 1$, it contains both $0$ and $1$, so there exists an index $r_0 \in \{0, \dots, m - 1\}$ where the cyclic $2$-bit window starting at $r_0$ is `01` ($b_{r_0} = 0$ and $b_{r_0 + 1} = 1$). Let $x := \{2^{r_0} u / (2^m - 1)\}$ and $y := \{2^{r_0 + 1} u / (2^m - 1)\} = \{2 x\}$. Because $b_{r_0} = 0$ and $b_{r_0 + 1} = 1$, we have $x \in [1/4, 1/2)$ and $y = 2 x \in [1/2, 1)$, so $y - x = x \in [1/4, 1/2)$. Hence $\cos(2\pi (y - x)) \le \cos(\pi / 2) = 0$ and $|e(x) + e(y)| = \sqrt{2 + 2 \cos(2\pi(y - x))} \le \sqrt{2}$. Pairing the two indices $r_0, r_0 + 1$ and bounding the remaining $m - 2$ unit-modulus terms by $1$ gives
```math
|S(u, m)| \le \frac{m - 2 + |e(x) + e(y)|}{m} \le \frac{m - 2 + \sqrt{2}}{m} = 1 - \frac{2 - \sqrt{2}}{m}. \qquad \square
```

**Corollary 5.2 (Complete-period equidistribution of the prime-exponent product).** *Let $p_1 < p_2 < \dots$ be the primes ($p_1 = 2$) and $R_k^{(\mathrm{prime})} := \prod_{j=1}^k (1 - 2^{-p_j})^{-1}$. Then $\operatorname{ord}_{D_k}(2) = \prod_{j=1}^k p_j$ and $D(\mu(R_k^{(\mathrm{prime})}; 2)) \to 0$ as $k \to \infty$.*

*Proof.* Since $p_1, \dots, p_k$ are pairwise coprime, $2^{p_1} - 1, \dots, 2^{p_k} - 1$ are pairwise coprime (as $\gcd(2^a - 1, 2^b - 1) = 2^{\gcd(a, b)} - 1 = 1$), so $T_k = \operatorname{lcm}(p_1, \dots, p_k) = \prod_{j=1}^k p_j$. By CRT, $R_k^{(\mathrm{prime})} \equiv \sum_{j=1}^k \frac{a_j^{(k)}}{2^{p_j} - 1} \pmod 1$ with $\gcd(a_j^{(k)}, 2^{p_j} - 1) = 1$, giving the exact convolution factorization $\mu(R_k^{(\mathrm{prime})}; 2) = \nu_1^{(k)} * \cdots * \nu_k^{(k)}$ and $\widehat{C}_k(h) = \prod_{j=1}^k \widehat{\nu_j^{(k)}}(h)$. For any fixed $h \neq 0$, once $2^{p_j} - 1 > |h|$ we have $(2^{p_j} - 1) \nmid h a_j^{(k)}$, so Lemma 5.1 gives
```math
|\widehat{C}_k(h)| \le \prod_{\substack{j \le k \\ 2^{p_j} - 1 > |h|}} \left(1 - \frac{2 - \sqrt{2}}{p_j}\right) \le \exp\!\left(-(2 - \sqrt{2}) \sum_{\substack{j \le k \\ 2^{p_j} - 1 > |h|}} \frac{1}{p_j}\right) \longrightarrow 0 \qquad (k \to \infty)
```
by Euler's divergence of $\sum_p 1/p$. By Weyl's criterion, $\mu(R_k^{(\mathrm{prime})}; 2) \Rightarrow \lambda$, and since $\lambda$ is atomless, $D(\mu(R_k^{(\mathrm{prime})}; 2)) \to 0$. $\square$

### 5.2 Fully coprime base-$2$ schedule $m_k = \omega_{k-1} T_{k-1} + 1$: squaring inequalities

Now take $m_1 = 2$ and $m_k = \omega_{k-1} T_{k-1} + 1$ ($k \ge 2$) with $T_k = \prod_{j=1}^k m_j$, $\omega_1 \ge 2$, and $\omega_k \to \infty$.

1. **Pairwise coprimality and $k$-independence of $\nu_j$.** Since $m_j \mid T_{k-1}$ for all $j < k$, $\gcd(m_j, m_k) = 1$, so $D_k = \prod_{j=1}^k (2^{m_j} - 1)$ is pairwise coprime and $\operatorname{ord}_{D_k}(2) = T_k$. Writing $R_k \equiv \sum_{j=1}^k \frac{a_j^{(k)}}{2^{m_j} - 1} \pmod 1$ with $\gcd(a_j^{(k)}, 2^{m_j} - 1) = 1$, for every $j < k$ we have $m_k \equiv 1 \pmod{m_j} \implies 2^{m_k} \equiv 2 \pmod{2^{m_j} - 1} \implies 2^{m_k} / (2^{m_k} - 1) \equiv 2 \pmod{2^{m_j} - 1}$, whence
   ```math
   a_j^{(k)} \equiv 2 \, a_j^{(k-1)} \equiv 2^{k - j} a_j^{(j)} \pmod{2^{m_j} - 1}.
   ```
   Because multiplication by $2$ only cyclically shifts the $\times 2$-orbit of $a_j^{(j)} / (2^{m_j} - 1)$, the uniform orbit probability measure $\nu_j$ is **independent of $k \ge j$**, giving $\widehat{C}_k(h) = \prod_{j=1}^k \widehat{\nu_j}(h)$ (in particular $|\widehat{C}_k(h)|$ is **monotone nonincreasing** in $k$ for every $h \in \mathbb{Z}$).

2. **Exact real partial-fraction identity ($k \ge 2$).** Comparing $R_k = R_{k-1} + \frac{R_{k-1}}{2^{m_k} - 1}$ with $R_k \equiv 2 R_{k-1} + \frac{a_k^{(k)}}{2^{m_k} - 1} \pmod 1$ gives $\frac{a_k^{(k)}}{2^{m_k} - 1} \equiv -R_{k-1} + \frac{R_{k-1}}{2^{m_k} - 1} \pmod 1$. Since $1 < R_{k-1} < 2$, $\{-R_{k-1}\} \le 1 - 1/D_{k-1}$, and $2^{m_k} - 1 > 4 D_{k-1}$ for all $k \ge 2$ (at $k = 2$, $m_2 \ge 2 m_1 + 1 \implies 2^{m_2} - 1 > 4(2^{m_1} - 1)$; for $k \ge 3$, $m_k > T_{k-1} \ge \sum_{j < k} m_j + 2$), the right-hand side lies strictly in $(0, 1)$, giving the **exact real equality**
   ```math
   \frac{a_k^{(k)}}{2^{m_k} - 1} = \{-R_{k-1}\} + \frac{R_{k-1}}{2^{m_k} - 1} \qquad (k \ge 2).
   ```

3. **Squaring inequality for $|\widehat{C}_k(h)|$.** Set $c_2(h) := 4 + 2 \lceil \log_2(4\pi |h|) \rceil$. Let $w_r := e(-h \cdot 2^r R_{k-1})$ ($T_{k-1}$-periodic with mean $\overline{\widehat{C}_{k-1}(h)}$) and $z_r^{(k)} := e(h \cdot 2^r a_k^{(k)} / (2^{m_k} - 1))$. Using the exact partial-fraction identity and splitting $0 \le r < m_k$ at $m_k - L_h$ ($L_h := \lceil \log_2(4\pi |h|) \rceil$), we obtain
   ```math
   \sum_{r=0}^{m_k - 1} \big|z_r^{(k)} - w_r\big| \le 2\pi |h| R_{k-1} \sum_{r=0}^{m_k - L_h - 1} \frac{2^r}{2^{m_k} - 1} + 2 L_h \le 2 + 2 L_h = c_2(h) - 2.
   ```
   Since $m_k = \omega_{k-1} T_{k-1} + 1$, $\frac{1}{m_k} \sum_{r=0}^{m_k - 1} w_r = \frac{\omega_{k-1} T_{k-1}}{m_k} \overline{\widehat{C}_{k-1}(h)} + \frac{w_0}{m_k}$ differs from $\overline{\widehat{C}_{k-1}(h)}$ by at most $2 / m_k$. Hence $|\widehat{\nu_k}(h) - \overline{\widehat{C}_{k-1}(h)}| \le c_2(h) / m_k$, and multiplying by $|\widehat{C}_{k-1}(h)| \le 1$ yields
   ```math
   |\widehat{C}_k(h)| = |\widehat{C}_{k-1}(h)| \cdot |\widehat{\nu_k}(h)| \le |\widehat{C}_{k-1}(h)|^2 + \frac{c_2(h)}{m_k}.
   ```

4. **Squaring inequality for the band $L^2$ energy $E_k(h)$.** Define $E_k(h) := \frac{1}{T_k} \sum_{a=0}^{T_k - 1} |\widehat{C}_k(h(2^a - 1))|^2$. Because $h(2^a - 1) \bmod (2^{m_j} - 1)$ depends only on $a \bmod m_j$ and $m_1, \dots, m_k$ are pairwise coprime, CRT factors $E_k(h)$ identically as
   ```math
   E_k(h) = \prod_{j=1}^k e_j(h), \qquad e_j(h) := \frac{1}{m_j} \sum_{s=0}^{m_j - 1} \big|\widehat{\nu_j}\big(h(2^s - 1)\big)\big|^2 \in [0, 1].
   ```
   In particular, $E_k(h)$ is **monotone nonincreasing** in $k$. Notice the exact autocorrelation identity
   $$\widehat{\nu_j}\big(h(2^s - 1)\big) = \frac{1}{m_j} \sum_{r=0}^{m_j - 1} z_{(r + s) \bmod m_j}^{(j)} \overline{z_r^{(j)}}.$$
   Replacing $z_r^{(j)}$ by $w_r := e(-h \cdot 2^r R_{j-1})$ converts the factor $2^s$ into a cyclic index shift. By the triangle inequality, uniformly over all $0 \le s < m_j$:
   ```math
   \left|\widehat{\nu_j}\big(h(2^s - 1)\big) - \frac{1}{m_j} \sum_{r=0}^{m_j - 1} w_{(r + s) \bmod m_j} \overline{w_r}\right| \le \frac{2}{m_j} \sum_{r=0}^{m_j - 1} \big|z_r^{(j)} - w_r\big| \le \frac{2 c_2(h)}{m_j}.
   ```
   Write $s = q_s T_{j-1} + a$ ($0 \le a < T_{j-1}$) and $\theta_s := s / m_j \in [0, 1)$. For $0 \le r < m_j - s$, $w_{r + s} \overline{w_r} = e(-h(2^a - 1) 2^r R_{j-1})$ ($T_{j-1}$-periodic, average $\overline{\widehat{C}_{j-1}(h(2^a - 1))}$); for $m_j - s \le r < m_j$, $(r + s) - m_j = r + s - \omega_{j-1} T_{j-1} - 1 \equiv r + (a - 1) \pmod{T_{j-1}}$, giving average $\overline{\widehat{C}_{j-1}(h(2^{a-1} - 1))}$. Accounting for at most one incomplete period of $T_{j-1}$ on each subinterval (total $\le 2 T_{j-1} / m_j < 2 / \omega_{j-1}$), squaring via $|z|^2 \le |w|^2 + 2|z - w|$ and convexity $|(1-\theta)u + \theta v|^2 \le (1-\theta)|u|^2 + \theta|v|^2$, and averaging over all $0 \le s < m_j = \omega_{j-1} T_{j-1} + 1$ (where each residue class $a \bmod T_{j-1}$ has $\frac{1}{m_j} \sum_{q < \omega_{j-1}} \theta_{q T_{j-1} + a} \le \frac{1}{2 T_{j-1}}(1 + \frac{1}{\omega_{j-1}})$ and $\frac{1}{m_j} \sum_{q < \omega_{j-1}} (1 - \theta_{q T_{j-1} + a}) \le \frac{1}{2 T_{j-1}}(1 + \frac{2}{\omega_{j-1}})$) yields
   ```math
   e_j(h) \le E_{j-1}(h) + \frac{7}{\omega_{j-1}} + \frac{4 c_2(h)}{m_j} \implies E_j(h) \le E_{j-1}(h)^2 + \frac{7}{\omega_{j-1}} + \frac{4 c_2(h)}{m_j}.
   ```
   To show $E_j(h) \to 0$ for every fixed $h \neq 0$: pick $j_1$ so large that $2^{m_{j_1} / 2} + 1 > |h|$. For every $1 \le s < m_{j_1}$, $\gcd(m_{j_1}, s) \le m_{j_1} / 2$, so $(2^{m_{j_1}} - 1) / \gcd(2^{m_{j_1}} - 1, 2^s - 1) \ge 2^{m_{j_1}/2} + 1 > |h|$, hence $(2^{m_{j_1}} - 1) \nmid h(2^s - 1)$. By Lemma 5.1,
   $$E_{j_1}(h) \le e_{j_1}(h) \le \frac{1}{m_{j_1}} + \frac{m_{j_1} - 1}{m_{j_1}} \left(1 - \frac{2 - \sqrt{2}}{m_{j_1}}\right)^2 \le 1 - \frac{3(2 - \sqrt{2})}{4 m_{j_1}} < 1.$$
   Since $E_j(h)$ is monotone nonincreasing, $L := \lim_{j\to\infty} E_j(h)$ exists in $[0, E_{j_1}(h)] \subset [0, 1)$. Letting $j \to \infty$ in the squaring inequality gives $L \le L^2$, forcing $L = 0$. Likewise, $|\widehat{C}_k(h)|$ is monotone nonincreasing with $|\widehat{C}_{j_0}(h)| < 1$ once $2^{m_{j_0}} - 1 > |h|$, so $L' := \lim_{k\to\infty} |\widehat{C}_k(h)| \le (L')^2$ forces $\lim_{k\to\infty} |\widehat{C}_k(h)| = 0$.

### 5.3 All-prefix normality and complete-period sub-exponential rate for $m_k = \omega_{k-1} T_{k-1} + 1$

**All-prefix normality ($W_h(N) \to 0$).** Fix $h \neq 0$ and $\varepsilon > 0$. Since $m_K = \omega_{K-1} T_{K-1} + 1$, we have $2^{m_K} \equiv 2 \pmod{D_{K-1}}$, so the exact band identity for $R_K$ is
```math
2^{i m_K + r} R_K \equiv (2^{i+1} - 1) \, 2^r R_{K-1} + \frac{2^r R_{K-1}}{2^{m_K} - 1} \pmod 1 \qquad (i \ge 0,\ 0 \le r < m_K).
```
For $N = I m_K + r_0 \in [m_K, m_{K+1})$ ($I \ge 1, 0 \le r_0 < m_K$), cutting the last $\Delta_K := \lceil \log_2 m_K \rceil$ terms for $|y - R_K| \le 4 \cdot 2^{-m_{K+1}}$ and bounding the leftover $t < T_{K-1}$ terms in the incomplete band by $T_{K-1} / N < 1/\omega_{K-1}$ yields
```math
|W_h(N)| \le \frac{1}{I + r_0/m_K} \left(\sum_{i=0}^{I-1} \big|\widehat{C}_{K-1}(h(2^{i+1} - 1))\big| + \frac{r_0}{m_K} \big|\widehat{C}_{K-1}(h(2^{I+1} - 1))\big|\right) + \frac{1}{\omega_{K-1}} + \frac{c_2(h) + \Delta_K}{m_K}.
```
Choose $r_*$ such that $E_{r_*}(h) < \varepsilon^2 / 16$, and then $K_0 > r_*$ so that for all $K \ge K_0$, $\max_{0 \le i < T_{r_*}} |\widehat{C}_{K-1}(h(2^{i+1} - 1))| < \varepsilon / 4$ (a finite set of nonzero frequencies!) and $\frac{1}{\omega_{K-1}} + \frac{c_2(h) + \Delta_K}{m_K} < \varepsilon / 4$.
- If $I < T_{r_*}$: every index $0 \le i \le I$ lies in $\{0, \dots, T_{r_*} - 1\}$, giving $|W_h(N)| < \varepsilon / 4 + \varepsilon / 4 < \varepsilon$.
- If $I \ge T_{r_*}$: use monotonicity $|\widehat{C}_{K-1}(H)| \le |\widehat{C}_{r_*}(H)|$ and $T_{r_*}$-periodicity of $|\widehat{C}_{r_*}(h(2^{i+1} - 1))|$ in $i$. Writing $I = Q T_{r_*} + t$ ($Q \ge 1, 0 \le t < T_{r_*}$), the $I + 1 \le (Q + 1) T_{r_*}$ terms in the sum are bounded by $(Q + 1)$ complete periods of $T_{r_*}$, so by Cauchy–Schwarz:
  $$\frac{1}{I + r_0/m_K} (\cdots) \le \frac{Q + 1}{Q} \cdot \frac{1}{T_{r_*}} \sum_{a=0}^{T_{r_*} - 1} \big|\widehat{C}_{r_*}(h(2^a - 1))\big| \le 2 \sqrt{E_{r_*}(h)} < \frac{\varepsilon}{2},$$
  giving $|W_h(N)| < \frac{3\varepsilon}{4} < \varepsilon$. Thus $y = 1/x$ is base-$2$ normal along all $N$. Moreover, because $m_{k+1} / m_k > \omega_k \to \infty$, we have $S_k := \sum_{j=1}^k m_j = o(m_{k+1})$, so the four-range all-prefix decomposition of §3.2 yields $W_1(\mu_N^{\mathrm{emp}}(x; 2), \delta_0) \le (S_k + 4) / N \le (S_k + 4) / m_{k+1} \to 0$ for all $N \in [m_{k+1}, m_{k+2})$, hence $\lim_{N\to\infty} D_N(x; 2) = 1$ and $x \in M_2 \subset K_2$ in the repository's full-limit sense.

**Complete-period sub-exponential rate for $\omega_k = 2^k$.** For $\omega_k = 2^k$, the recurrence $m_{k+1} - 1 = \frac{\omega_k}{\omega_{k-1}} m_k(m_k - 1)$ becomes $m_{k+1} = 2 m_k(m_k - 1) + 1$, so $m_k^2 \le m_{k+1} \le 2 m_k^2$ (for all $m_k \ge 2$) and $\ln T_k = (c_* + o(1)) 2^k$ ($c_* > 0$). Fix $1 \le h \le H$ and let $j_0 = j_0(h) := \min\{j \ge 1 : 2^{m_j} - 1 > h\}$. Then $m_{j_0 - 1} \le \log_2(h + 1)$, so $m_{j_0} \le 2 (\log_2(H + 1))^2$ and $2^{j_0} = O(\ln\ln H)$. Set $k_1 := j_0 + 1$: by monotonicity and Lemma 5.1, $\delta_{k_1} := 1 - |\widehat{C}_{k_1}(h)| \ge (2 - \sqrt{2}) / m_{j_0}$. For all $k \ge k_1$, $m_{k+1} \ge m_{j_0 + 2} \ge m_{j_0 + 1}^2 \ge m_{j_0}^4$ (while $c_2(h) = O(\log_2 h) = O(m_{j_0})$), so $\varepsilon_{k+1} := c_2(h) / m_{k+1} \le \frac{1}{8} \delta_{k_1}$ (for $j_0$ above an absolute constant $J_0$). While $\delta_k \le 1/8$, the squaring inequality gives $\delta_{k+1} \ge 2\delta_k - \delta_k^2 - \varepsilon_{k+1} \ge \frac{7}{4} \delta_k$; thus within $r_1 \le \frac{\ln m_{j_0}}{\ln(7/4)} + O(1)$ steps (plus at most $4$ steps to drop from $7/8$ to $3/8$), we reach $k_2 = k_1 + r_1 + 4$ with $|\widehat{C}_{k_2}(h)| \le 3/8$ and
```math
2^{k_2} = O\!\left((\ln\ln H) \cdot m_{j_0}^{\ln 2 / \ln(7/4)}\right) = O\!\left((\ln H)^{2.5}\right).
```
Moreover, $m_{k_2 + 1} \ge 32 c_2(h)$ and $m_{k+1} \ge m_k^2$ imply $\varepsilon_{k_2 + t + 1} \le (1/4)^{2^{t+1}}$ for all $t \ge 0$, whence by induction $|\widehat{C}_{k_2 + t}(h)| \le \frac{1}{2} (3/4)^{2^t}$ (since $\frac{1}{4}(3/4)^{2^{t+1}} + (1/4)^{2^{t+1}} \le \frac{1}{2}(3/4)^{2^{t+1}}$). Taking Erdős–Turán cutoff $H := \lfloor \exp(c' (\ln T_k)^{1/4}) \rfloor$ makes $2^{k - k_2} \ge c_1 (\ln T_k) / (\ln H)^{2.5} \ge c_2 (\ln T_k)^{3/8} \gg \ln H$, yielding
```math
D\big(\mu(R_k; 2)\big) \le \frac{C}{H} + C \sum_{h=1}^H \frac{|\widehat{C}_k(h)|}{h} = O\!\left(\exp\!\left(-c_0 (\ln T_k)^{1/4}\right)\right).
```

### 5.4 Complete-period exponential equidistribution of $R_k^{(E)} = \prod_{j=1}^k (1 - b^{-j})^{-1}$

Fix any base $b \ge 2$ and choose an anchor prime $p$, setting $s_b := \operatorname{ord}_p(b)$ when $p$ is odd and $s_b := \operatorname{ord}_4(b)$ when $p = 2$, together with $e_0 := v_p(b^{s_b} - 1)$, as follows:
- $b = 2$: $p = 3$, $s_2 = 2$, $e_0 = 1$;
- $b \ge 3$ odd, $b \equiv 1 \pmod 4$: $p = 2$, $s_b = 1$, $e_0 = v_2(b - 1) \ge 2$;
- $b \ge 3$ odd, $b \equiv 3 \pmod 4$: $p = 2$, $s_b = 2$, $e_0 = v_2(b^2 - 1) \ge 3$;
- $b \ge 4$ even: any odd prime $p \mid (b - 1)$, $s_b = 1$, $e_0 = v_p(b - 1) \ge 1$.

Write $R_k^{(E)} = b^{k(k+1)/2} / D_k$ in lowest terms, where $D_k = \prod_{j=1}^k (b^j - 1) = p^{e_k} D'_k$ with $p \nmid D'_k$, $T_p := \operatorname{ord}_{p^{e_k}}(b)$, $T'_k := \operatorname{ord}_{D'_k}(b)$, and $T_k = \operatorname{lcm}(T_p, T'_k)$.

1. **Linear lower bound on $e_k$:** Every $j \in \{1, \dots, k\}$ divisible by $s_b$ satisfies $v_p(b^j - 1) = e_0 + v_p(j / s_b) \ge e_0$, so
   ```math
   e_k = v_p(D_k) \ge e_0 \left\lfloor \frac{k}{s_b} \right\rfloor + v_p\!\left(\left\lfloor \frac{k}{s_b} \right\rfloor!\right) \ge e_0 \left\lfloor \frac{k}{s_b} \right\rfloor.
   ```
2. **Logarithmic upper bound on $v_p(T'_k)$:** Every prime $q \neq p$ dividing $D'_k$ divides $b^j - 1$ for some $1 \le j \le k$, so $\operatorname{ord}_q(b) \mid j$ and hence $v_p(\operatorname{ord}_q(b)) \le v_p(j) \le \lfloor \log_p k \rfloor$. Lifting to $q^a$ multiplies the order by at most a power of $q$ (with $v_p(q^{a-1}) = 0$ since $q \neq p$). Taking $\operatorname{lcm}$ over all $q \mid D'_k$ yields **unconditionally**:
   ```math
   v_p(T'_k) = \max_{q \mid D'_k} v_p\!\left(\operatorname{ord}_{q^{v_q(D_k)}}(b)\right) \le \lfloor \log_p k \rfloor.
   ```
3. **Exact $p$-adic grid bound (including the $p = 2, b \equiv 3 \pmod 4$ sign-coset correction):** Set $m_* := \operatorname{lcm}(s_b, T'_k)$. Then $b^{m_*} \equiv 1 \pmod{D'_k}$, and by LTE:
   - if $p$ is odd or ($p = 2$ and $b \equiv 1 \pmod 4$), $\gcd(s_b, p) = 1$, so $v_p(b^{m_*} - 1) = e_0 + v_p(T'_k)$, and $r_k := \max(0,\, e_k - e_0 - v_p(T'_k)) = \max(0,\, v_p(T_p) - v_p(T'_k))$;
   - if $p = 2$ and $b \equiv 3 \pmod 4$, $s_b = 2$ and $4 \mid (b^2 - 1)$, so $v_2(b^{m_*} - 1) = v_2((b^2)^{m_*/2} - 1) = e_0 + \max(0,\, v_2(T'_k) - 1)$, and $r_k := \max(0,\, e_k - e_0 - \max(0,\, v_2(T'_k) - 1)) = \max(0,\, v_2(T_p) - \max(1,\, v_2(T'_k)))$ (the $\max(1, v_2(T'_k))$ removes the $\pm 1$ coset factor in $(\mathbb{Z}/2^e\mathbb{Z})^\times \cong \{\pm 1\} \times \mathbb{Z}/2^{e-2}\mathbb{Z}$ that does not advance along $1 + 4\mathbb{Z}$; e.g., at $b = 3, p = 2, k = 2$, $D_2 = 16$, $T_2 = 4$, the orbit $\{1/16, 3/16, 9/16, 11/16\}$ decomposes into two $2$-point grids of discrepancy $3/8 \le 1/2$, not $1/4$).

   In every case, $b^{m_*} = 1 + u p^{e_k - r_k}$ with $p \nmid u$ (and $p^{e_k - r_k} \ge 4$ whenever $p = 2$), so the subgroup $\langle b^{m_*} \rangle$ partitions the complete orbit of $R_k^{(E)}$ into shifted uniform $p^{r_k}$-point grids while fixing the $D'_k$-component. Averaging over cosets gives
   ```math
   D\big(\mu(R_k^{(E)}; b)\big) \le p^{-r_k} \le p^{e_0 + \lfloor \log_p k \rfloor - e_0 \lfloor k / s_b \rfloor} \le C_b \cdot k \cdot p^{-e_0 k / s_b} \longrightarrow 0. \qquad \square
   ```

### 5.5 The four-rung schedule bridge toward $P_b = 1/E_b$

| Rung | Schedule $(m_k)$ | Growth of $m_k$ | Complete-period $D(\mu(R_k; b))$ | All-prefix normality of $y = 1/x$ | Remaining gap to $P_b = 1/E_b$ |
|---|---|---|---|---|---|
| 1. Phase 22 / Hull–Dobell | $D_{k-1} \mid (b^{m_k}-1)$ or $\operatorname{rad}^*(D_{k-1}) \mid (b^{m_k}-1)$ | Eventual tetration under (HD2) ($m_{k+2} \ge b^{m_k}/2$) | $\le D_{k-1}^{-1}$ (exact grid) | Proved (Phase 22 Thm 2; Thm 4) | Tetration growth required by (HD2) |
| 2. Anchored coprime (Thm 5) | $m_k = s q_k = \omega_{k-1} T_{k-1} + s$ (all $b \ge 2$) | **Doubly exponential** ($\ln m_k \sim \frac{c_*}{2} 2^k$) | $\le M^{-(k-1)}$ (exact grid) | **Proved**, $D_N = O_{b,A}((\ln N)^{-A})$ | Still doubly exponential ($m_k \gg T_{k-1}$) |
| 3. Fully coprime (Thm 6a–b) | $m_k = \omega_{k-1} T_{k-1} + 1$ ($b = 2$) | **Doubly exponential** ($\ln m_k \sim \frac{c_*}{2} 2^k$) | **$O(\exp(-c_0 (\ln T_k)^{1/4}))$** | **Proved** (squaring $E_k(h) \to 0$) | Still requires $m_k \gg T_{k-1}$ |
| 4. Prime / Partition (Thm 6a,c) | $m_k = p_k$ or $m_k = k$ ($P_b = 1/E_b$) | Linear / $k \ln k$ | **Proved:** $\to 0$ ($p_k$), **$\le C_b k p^{-e_0 k / s_b}$** ($R_k^{(E)}$) | **Open** | **Short-orbit gap:** $N \approx m_{k+1} = k + 1 \ll T_k$ (elementary bounds $k \log^2 k \ll \ln T_k \ll k^2$; heuristically super-exponential) |

Heuristically, Rungs 1–4 isolate the principal remaining obstacle for this product-approximation approach to $P_b = 1/E_b = \prod_{j=1}^\infty (1 - b^{-j})^{-1}$: the complete-period measures $\mu(R_k^{(E)}; b)$ are already exponentially equidistributed (Rung 4), and Rungs 2–3 remove both full divisibility ($D_{k-1} \mid (b^{m_k} - 1)$) and tetration growth, while the short-orbit gap $N \approx k + 1 \ll T_k$ (where $P_b$ agrees with $R_k^{(E)}$ for only $O(k)$ steps out of a period $T_k$ with $k \log^2 k \ll \ln T_k \ll k^2$) remains completely open.

---

## 6. Proposed Lean 4 Blueprint (Unformalized — Not Yet in `NormalityChecker/`)

> **Status note:** None of the six theorems below currently exist in `NormalityChecker/` (nor in `NormalityChecker/Phase23Cores.lean`). They are **proposed unformalized blueprint targets** stating exact finite combinatorial and period cores that can be built on top of `NormalityChecker/RadixPowerTower.lean` (`orderOf_mul_pow_sub_one`, `pow_sub_one_dvd_pow_sub_one_iff`, `coprime_rat_cylinder_margin`) without analytic dependencies.

1. **Universal repunit denominator divisibility and band identity (`D1`, proposed):**
   ```lean
   theorem den_mul_repunit_inv_dvd (b m : ℕ) (hb : 2 ≤ b) (hm : 0 < m)
       (X : ℚ) (hX : (X.den : ℕ) ∣ b ^ m - 1) :
       ((X * ((b ^ ((b - 1) * m) * (b ^ m - 1) : ℚ) / (b ^ (b * m) - 1))).den : ℕ) ∣
         b ^ (b * m) - 1
   ```
   Follows in three lines from `(b^m - 1) / X.den ∈ ℤ` cancelling `X.den`.

2. **$Q(1) = 1$ multiplier-excess identity (`D1`, proposed):**
   ```lean
   theorem poly_unit_eval_excess_eq (L : ℕ) (Q A : Polynomial ℤ)
       (hQ1 : Q.eval 1 = 1) (hQA : Q * A = ∑ i ∈ Finset.range L, Polynomial.X ^ i) :
       ∑ i ∈ (Finset.range L).filter (fun i => 2 ≤ A.coeff i), (A.coeff i - 1) =
         (((Finset.range L).filter (fun i => A.coeff i = 0)).card : ℤ) +
         ∑ i ∈ (Finset.range L).filter (fun i => A.coeff i ≤ -1), (1 - A.coeff i)
   ```

3. **Static $L$-normal discrepancy ceiling (`D2`, proposed):**
   ```lean
   theorem disc_le_two_mul_inv_pow_of_exact_L_normal (b L P : ℕ) (hb : 2 ≤ b) (hP : 0 < P)
       (pts : Fin P → ℝ) (h01 : ∀ i, 0 ≤ pts i ∧ pts i < 1)
       (hL : ∀ w : Fin (b ^ L),
         ((Finset.univ.filter (fun i => (w : ℝ) / b ^ L ≤ pts i ∧ pts i < ((w : ℕ) + 1 : ℝ) / b ^ L)).card : ℝ) =
           (P : ℝ) / b ^ L) :
       ∀ u v : ℝ, 0 ≤ u → u < v → v ≤ 1 →
         |(((Finset.univ.filter (fun i => u ≤ pts i ∧ pts i < v)).card : ℝ) / P) - (v - u)| ≤
           2 / (b ^ L : ℝ)
   ```

4. **Refined Markov digraph strict interiority and simultaneous $s r$ $L$-normality (`D2`, proposed):**
   ```lean
   theorem refined_markov_strict_interiority (b L P : ℕ) (hb : 2 ≤ b) (hL : 1 ≤ L) (hP : 0 < P)
       (Q M : ℕ) (hQ : ∀ s ∈ Finset.Ico 1 b, s ∣ Q) (hM : M = Q * b ^ L)
       (u : Fin P → Fin M) (d : Fin P → Fin b)
       (hedge : ∀ n : Fin P, (u (n + 1) : ℕ) = (b * (u n : ℕ) + (d n : ℕ)) % M)
       (hnon0 : ∃ n, d n ≠ 0) (hnonmax : ∃ n, (d n : ℕ) ≠ b - 1) :
       let α : Fin P → ℕ := fun n => (b * (u n : ℕ)) / M
       let A : ℕ := ∑ n : Fin P, α n * b ^ (P - 1 - (n : ℕ))
       ∀ n : Fin P,
         (u n : ℚ) / M < (((b ^ (n : ℕ) * A) % (b ^ P - 1) : ℕ) : ℚ) / (b ^ P - 1) ∧
         (((b ^ (n : ℕ) * A) % (b ^ P - 1) : ℕ) : ℚ) / (b ^ P - 1) < ((u n : ℕ) + 1 : ℚ) / M
   ```

5. **Anchored coprime exact period (`D4`, proposed):**
   ```lean
   theorem orderOf_anchored_coprime_prod (b s : ℕ) (hb : 2 ≤ b)
       (hs : (4 ≤ b ∧ b % 4 ≠ 3 → 1 ≤ s) ∧ (¬(4 ≤ b ∧ b % 4 ≠ 3) → 2 ∣ s ∧ 0 < s))
       (k : ℕ) (hk : 0 < k) (q : Fin k → ℕ)
       (hcopM : ∀ j, Nat.Coprime (q j) (s * (b ^ s - 1)))
       (hpair : Pairwise (fun i j => Nat.Coprime (q i) (q j))) :
       orderOf ((b : ZMod (∏ j : Fin k, (b ^ (s * q j) - 1)))) =
         s * (b ^ s - 1) ^ (k - 1) * ∏ j : Fin k, q j
   ```

6. **Universal $01$-transition Fourier bound (`D4`, proposed):**
   ```lean
   theorem norm_binary_orbit_sum_le (m u : ℕ) (hm : 2 ≤ m) (hu1 : 1 ≤ u) (hu2 : u ≤ 2 ^ m - 2) :
       ‖(1 / (m : ℂ)) * ∑ r ∈ Finset.range m,
         Complex.exp (2 * Real.pi * Complex.I * (((2 ^ r * u) % (2 ^ m - 1) : ℕ) : ℂ) / (2 ^ m - 1))‖ ≤
         1 - (2 - Real.sqrt 2) / m
   ```

---

## 7. Verification Record (Finite Certificates and Finite Measurements)

All finite certificates (exact `int`/`Fraction` algebraic identities, period formulas, Eulerian graph circuits, strict cell interiority checks, exact $L$-word counts, Bang–Zsigmondy rigidity triples, recursive anchored coprime factorizations, and exact `Fraction` rational discrepancies) and separate floating-point finite measurements (IEEE-754 complex exponentials, truncated orbit discrepancies for large $P$, and growth-constant audits) are executed by `scripts/phase23_reciprocals_v2.py` (standard library only). Low-level helper invariants inside `order_mod` and `poly_div_exact` are validated via `internal_assert` and excluded from substantive check counts.

Command executed: `python -B scripts/phase23_reciprocals_v2.py` (exit code `0`, **12,193 substantive exact checks + 510 floating-point finite measurements = 12,703 total**).

| Section | Scope verified | Exact checks (`Finite certificate`) | Float checks (finite measurements, not evidence) |
|---|---|---:|---:|
| `1. D1 Convergent reciprocals` | Exact `Fraction` $D(\mu(r; b))$ across $b \in \{2, 3, 4, 5, 10\}$; exact $+1$-inversion period & subset-sum orbit lock; base-$2$ de Bruijn + $z$ zeros exact `Fraction` $D \in [0.118877, 0.884293]$; universal repunit band identities for $b = 2..6$ including $A > 1$ seeds $(3,5,7), (3,2,5), (4,3,7), (5,2,3)$; $Q(1)=1$ excess on $15$ $P_k$ polynomials & uncapped search over all $1,050$ cyclotomic divisors ($L \le 50$, $|Q(1)| \ge 2$, $|S_i| \le 1$; $562$ with $\deg Q \le \lfloor L/2 \rfloor$); plus §1b float $(X_3, Y_3)$ measurement | 1,482 | 4 |
| `2. D2 Exact D_max(b,L) = 2/b^L` | $G_{b,L}^*$ Eulerian circuits & exact $L$-word counts of $W_R^{\mathrm{exact}}$ for $(b, L) \in \{(2,1), (2,2), (2,3), (3,1), (3,2), (4,1), (5,1)\}$ (exact `Fraction` $D$ for $P \le 120$, float for $P > 120$); base-$2$ exact $2$-normal convergent reciprocals with exact `Fraction` $D \in [0.11888, 0.35417] \subset [0, 1/2]$ | 125 | 17 |
| `3. D2 All-base L-normal reciprocals` | Refined Markov digraph $\mathcal{G}_{b, Q b^L}$ exact strict interiority, exact $L$-normality, & exact integer interval bound $|I_R| - \mu(s r; b)(I_R) \ge \text{proven lb}$ for **all** $s = 1, \dots, b - 1$ across $(b, L) \in \{(2,1), (2,2), (3,1), (3,2), (4,1), (5,1)\}$ (exact `Fraction` $D$ for $P \le 100$, float for $P > 100$); $11$ primitive-root exact convergent $L$-normal reciprocals ($D_\infty = 2/p$); QR obstruction checks for $b \in \{4,5,8,9\}$ ($L \ge 1$) and $b \in \{2,6,10\}$ ($L \ge 3$); prescribed base-$2$ rational $p_0 \in \{1/3, 2/5, 3/7\}$ | 3,732 | 11 |
| `4. D4 Hull-Dobell rigidity & growth` | Bang–Zsigmondy rigidity on $1,542$ grid triples $(2 \le b \le 12)$ + $124$ explicit exception-equivalence triples ($b \in \{3, 7, 15, 31, 63\}$ at $m = 2$, $n \le 20$, and $(2, 6)$ for $n \le 24$); $b \equiv 3 \pmod 4$ parity switch at $k = 3$; $6$ strict Hull–Dobell chains ($D_2 \nmid (b^{m_3} - 1)$) verifying $T_3 = m_3 D_2$, $S_i \equiv i + 1 \pmod{b^{m_2}-1}$, and $d' \mid S_i \iff d' \mid (i + 1)$ | 2,343 | 0 |
| `5. D4 Anchored coprime schedules` | $9$ genuine recursive anchored coprime schedules across $b \in \{2, 3, 4, 5, 10\}$ (all satisfying $q_1 \ge 5$, $\gcd(q_1, s M) = 1$, $s M \mid \omega_1$, $s \mid \omega_{k-1}$, $q_k = \omega_{k-1} (T_{k-1}/s) + 1$; incl. $b=2, s=4, M=15$ and $k=3$ schedules $T_3 = 23,355,090$ and $1,555,920$); exact `Fraction` $D(\mu_k) \le M^{-(k-1)}$ for $T_k \le 1000$ ($4$ schedules) and float Weyl vanishing ($\le 2.3 \times 10^{-16}$); $4,246$ exact LTE band-multiplier tuples; float doubly-exponential audit $\ln T_k / 2^k \to c_*$ | 4,431 | 8 |
| `6. D4 Coprime CRT, primes & 1/E_b` | Exact partial-fraction identity & exact periods on $[2, 5, 31, 621]$, $[2, 21, 421]$, and $[2, 9, 145, 41761]$; exact $p$-adic grid bound $D(\mu(R_k^{(E)}; b)) \le p^{-r_k}$ across $b = 2$ ($p=3, k \le 7$), $b = 3$ ($p=2, k \le 5$), and $b = 5$ ($p=2, k \le 5$); plus float checks of the $01$-transition bound on all $427$ orbits ($2 \le m \le 11$), CRT factorization, non-vacuous $E_k$ squaring inequality on $[2, 21, 421]$ ($7/\omega = 0.70$), tight $|\widehat{C}_k|$ squaring inequality on $[2, 9, 145, 41761]$, and prime-exponent products ($k = 1..5$) | 80 | 470 |
| **Total** | | **12,193** | **510** |

**Exact (`int`/`Fraction`) verification highlights (`Finite certificate`):**
- **Theorem 1 (D1):** Exact convergent discrepancies for $b = 2, 3, 4, 5, 10$ include $D_\infty(1/3; 2) = 2/3$, $D_\infty(1/5; 2) = 2/5$, $D_\infty(1/15; 2) = 11/20$, $D_\infty(1/7; 3) = 2/7$, $D_\infty(3/31; 4) = 54/155$, $D_\infty(1/49; 5) = 2/49$, $D_\infty(1/19; 10) = 2/19$. Base-$2$ order-$4$ de Bruijn + $z$ zeros yields exact `Fraction` discrepancies from $0.118877$ ($z = 0$) to $0.884293$ ($z = 144$). Universal repunit period divisibility and all $b$ band identities verified for $9$ seeds across $b = 2..6$, including $A > 1$ seeds $(3, 5/7), (3, 2/5), (4, 3/7), (5, 2/3)$.
- **Theorem 2 & 3 (D2):** Base-$2$ exact $2$-normal mixtures in §2b yield exact `Fraction` discrepancies $0.11888, 0.13167, 0.17955, 0.23301, 0.31076, 0.35417 \in (0, 1/2]$. Refined Markov digraph $\mathcal{G}_{b, Q b^L}$ verified with exact strict interiority, exact $L$-normality, and exact integer interval bound for all $s < b$ across all $6$ $(b, L, R)$ cases (with exact `Fraction` $D = 0.3021$ for $(2,1,10)$ and $0.1883$ for $(2,2,10)$). Primitive-root convergent $L$-normal examples include $(3, 3, 163)$ ($D_\infty = 2/163$) and $(10, 2, 701)$ ($D_\infty = 2/701$).
- **Theorem 5 (D4):** Genuine recursive schedules verified for exact period $T_k$ and pairwise-coprime factorization include $(b, s, q) = (2, 2, [5, 31])$ ($T_2 = 930$, exact $D = 0.146872 \le 1/3$), $(2, 2, [5, 31, 8371])$ ($T_3 = 23,355,090$), $(4, 1, [5, 16])$ ($T_2 = 240$, exact $D = 0.187867 \le 1/3$), $(4, 1, [5, 16, 2161])$ ($T_3 = 1,555,920$), $(5, 1, [5, 21])$ ($T_2 = 420$, exact $D = 0.151982 \le 1/4$), and $(5, 1, [7, 29])$ ($T_2 = 812$, exact $D = 0.169659 \le 1/4$).
- **Theorem 6 (D4):** Ordinary partition partial products $R_k^{(E)}$: at $b = 2, p = 3, k = 6$, $D_6 = 615195$, $T_6 = 3780$, $3^{r_6} = 9$, exact $D = 0.00208 \le 0.11111$; at $b = 3, p = 2, k = 5$, $D_5 = 8053760$, $T_5 = 3840$, $2^{r_5} = 64$, exact $D = 0.00444 \le 0.01562$; at $b = 5, p = 2, k = 5$, $D_5 = 23205371904$, $T_5 = 30720$, $2^{r_5} = 512$, exact $D = 0.00042 \le 0.00195$.

**Selected finite-scale floating-point measurements (not evidence):**
- **§1b (D1):** On $m = [16, 96, 1536]$, $N = 3072$: $D_N(X_3) = 0.8672 \to 1$, $D_N(Y_3) = 0.6283$ (target $2/3$) for $r = 1/3$; $D_N(X_3) = 0.8555 \to 1$, $D_N(Y_3) = 0.3905$ (target $2/5$) for $r = 1/5$.
- **§3a (D2, $P > 100$):** Truncated 52-bit orbit discrepancies for $\mathcal{G}_{b, Q b^L}$: $(3, 1, 20)$ ($M = 6, P = 360$, float $D \in [0.1033, 0.1458]$), $(3, 2, 8)$ ($M = 18, P = 432$, float $D \in [0.0361, 0.0642]$), $(4, 1, 10)$ ($M = 24, P = 960$, float $D \in [0.0207, 0.0559]$), $(5, 1, 5)$ ($M = 60, P = 1500$, float $D \in [0.0067, 0.0250]$).
- **§5c (D4):** Balanced doubly-exponential constants $\lim_{k\to\infty} \ln T_k / 2^k$: $2.807411$ for $(b, s, q_1) = (2, 2, 5)$ ($\log_2 M = 1.5850$), $5.728742$ for $(2, 4, 7)$ ($\log_2 M = 3.9069$), $4.273538$ for $(3, 2, 5)$ ($\log_2 M = 3.0000$), and $4.272705$ for $(10, 1, 7)$ ($\log_2 M = 3.1699$).
- **§6b (D4):** On $[2, 5, 31, 621]$ ($\omega = (2, 3, 2)$): $|C_4(1)| = 0.00279$, $E_4(1) = 0.00231$ (finite decay measurement; $7/\omega \ge 2.33 > 1$). On $[2, 21, 421]$ ($\omega = (10, 10)$, non-vacuous $7/\omega = 0.70 < 1$): $E_3(1) = 0.02188 \le 0.84025 < 1$. On $[2, 9, 145, 41761]$ ($\omega = (4, 8, 16)$): tight $|\widehat{C}_k|$ squaring inequality at $k = 4$: $|C_4(1)| = 0.00248 \le 0.00277$, $|C_4(3)| = 0.21478 \le 0.21515$, $|C_4(5)| = 0.00026 \le 0.00064$.

---

## 8. Open Problems

1. **Exact convergent irrational reciprocal discrepancies (`Open`):** Theorem 1 establishes that $\mathcal{A}_{\mathrm{conv}}(2)$ is dense in $[0, 1]$ (realizing a dense set of rational periodic-orbit discrepancies) and Proposition 1.3 localizes $[D^-(1/x; b), D^+(1/x; b)] \subseteq [\alpha - \varepsilon, \alpha + \varepsilon]$ for every $b \ge 2, \alpha \in (0, 1), \varepsilon > 0$. Does **every** $\alpha \in (0, 1)$ (including irrational $\alpha$) occur as an **exact** limit $\lim_{N\to\infty} D_N(1/x; b) = \alpha$ for an irrational $x \in K_b$? (Any realization via a single rational orbit $\mu(r; b)$ can produce only rational $\alpha \in \mathbb{Q} \cap (0, 1)$, so realizing irrational $\alpha$ requires either slowly evolving rational seeds $r_k$ inside $x \in K_b$ without breaking $\lim_{N\to\infty} D_N(x; b) = 1$, or a non-product mechanism.)
2. **Dense exact convergent set $\mathcal{A}_{\mathrm{conv}}(b)$ in bases $b \ge 3$ (`Open`):** In base $b \ge 3$, Theorem 1 requires $2 \in \langle b \rangle \pmod D$ (restricting $D$ to divisors of $2 b^L - 1$ rather than all coprime denominators), while Proposition 1.3 gives arbitrarily narrow oscillation intervals via $Q_b(q)$ without collapsing $D^- = D^+$ unless $\mu(s r; b) = \mu(r; b)$. Is $\mathcal{A}_{\mathrm{conv}}(b)$ dense in $[0, 1]$ (and is the exact convergent $L$-normal subset dense in $[0, 2 b^{-L}]$) for every base $b \ge 3$?
3. **Short-orbit gap for $P_b = 1/E_b$ and $R^{(\mathrm{prime})}$ (`Open`):** Theorem 6 proves complete-period equidistribution $D(\mu(R_k^{(E)}; b)) = O_b(k p^{-e_0 k / s_b}) \to 0$ and $D(\mu(R_k^{(\mathrm{prime})}; 2)) \to 0$, and achieves all-prefix normality for doubly-exponential schedules $m_k = \omega_{k-1} T_{k-1} + 1$. Can one bridge the short-orbit gap $N \approx m_{k+1} \ll T_k$ to prove base-$b$ normality (or even $D^+(P_b; b) < 1$ or simple normality) for $P_b = 1/E_b = \prod_{j=1}^\infty (1 - b^{-j})^{-1}$ or $\prod_p (1 - 2^{-p})^{-1}$?
4. **Polynomial discrepancy rate $D_N(1/x; b) = O(N^{-c})$ for $x \in K_b$ (`Open`):** Theorem 5 achieves $D_N(1/x; b) = O_{b, A}((\ln N)^{-A})$ for every fixed $A > 0$, and Theorem 6 breaks the iterated-log barrier on complete periods ($O(\exp(-c_0 (\ln T_k)^{1/4}))$). Does there exist an irrational $x \in K_b$ whose reciprocal $1/x$ satisfies an all-prefix polynomial discrepancy rate $D_N(1/x; b) = O(N^{-c})$ ($c > 0$), or even an all-prefix sub-exponential rate $O(\exp(-c (\ln N)^\theta))$ ($\theta > 0$)?
