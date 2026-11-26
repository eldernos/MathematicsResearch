# Growing-precision cancellation and sharp discrepancy bounds for the mixed Stoneham product

Let $x = \alpha_{2,3}\alpha_{2,5}$, where $\alpha_{2,q} = \sum_{j \ge 1} q^{-j} 2^{-q^j}$, and let $R_n$ be its positive-index shifted rational prefix at binary shift $n \ge 5$, with $K = \lfloor \log_3 n \rfloor$, $L = \lfloor \log_5 n \rfloor$, $P = 3^K$ and $Q = 5^L$.

**Theorem 1 (Ordinary discrepancy bound sharp for the fixed-depth method via multi-depth non-coincidence; paper proof + exact finite certificate).** For the binary extreme interval discrepancy $D_N(x)$,
```math
\limsup_{N\to\infty} D_N(x) \le \frac{4}{11} + 2.85 \times 10^{-10} < 0.363636364 .
```
More generally, every finite non-coincidence certificate at depths $(h, k)$ on the bulk shape grid $1 \le a \le A(\eta)$, $1 \le b \le B(\eta)$ gives $\limsup D_N(x) \le \frac{4}{11} + \frac{11}{4}\eta + \delta$. This slashes Phase 14's $0.37048$ (and paper enclosure $0.37047224$) down to within $2.85 \times 10^{-10}$ of the exact fixed-depth lower barrier $4/11 = 0.363636\ldots$ established in Phase 14 (ordinary normality $D_\infty(x) = 0$ remains open).

**Theorem 2 (Simultaneous ultrametric separation and power-tower spacing; paper proof + Lean core).** Fix a nonrectangular shape $(a, b) \in \mathbb{N}_{\ge 1}^2$. If two distinct active shells $(K_1, L_1) \neq (K_2, L_2)$ of shape $(a, b)$ retain at most $r_i$ ternary layers and $s_i$ quinary layers ($K_i - r_i \ge 1$, $L_i - s_i \ge 1$), then $K_1 \neq K_2$ and $L_1 \neq L_2$, and ordering $K_1 < K_2$, $L_1 < L_2$ gives
```math
L_2 - L_1 \ge 2 \cdot 3^{\min(K_1 - r_1,\, K_2 - r_2) - 1},
\qquad
K_2 - K_1 \ge 4 \cdot 5^{\min(L_1 - s_1,\, L_2 - s_2) - 1}.
```
In particular, for bounded denominators $\operatorname{den}(R_n) \le M$ (and even for linear retained layers $r_i \le \theta K_i, s_i \le \theta L_i$ with $0 \le \theta < 1$), successive exceptional **shell intervals** $[U_j, V_j)$ of shape $(a, b)$ (each carrying one constant prefix $R_n$) satisfy power-tower spacing $U_{j+1} \ge \exp(c_{M} U_j)$ (resp. $U_{j+1} \ge \exp(c_\theta U_j^{1-\theta})$).

**Theorem 3 (Super-exponential sparsity of high-discrepancy cutoffs; paper proof).** For every $\varepsilon > 0$,
```math
\#\bigl\{m \le T : \exists\, N \in [e^m, e^{m+1}) \text{ with } D_N(x) > \varepsilon\bigr\} = O_\varepsilon(\log^* T),
```
and consequently
```math
\sum_{\substack{N \ge 5 \\ D_N(x) > \varepsilon}} \frac{1}{N \log N} < \infty,
\qquad
\sum_{\substack{N \le X \\ D_N(x) > \varepsilon}} \frac{1}{N} = O_\varepsilon(\log^* \log X) .
```
This strengthens Phase 14's logarithmic density zero ($\sum_{D_N > \varepsilon} 1/N = o(\log X)$) to iterated-logarithmic growth and convergent double-logarithmic weight.

**Proposition 4 (Exact Mahler–Newton decay and $p$-adic base-variation derivative; paper proof, exact checks).** For $(p, q, u) \in \{(3, 5, 2), (5, 3, 4)\}$ and block increment $g(z) = S_{u(z+1)} - S_{uz}$, the forward differences satisfy $v_p(\Delta^k g(0)) \ge k + 1$ for all $k \ge 0$, so $S_{uz} \equiv \sum_{k=0}^{D-2} \Delta^k g(0)\binom{z}{k+1} \pmod{p^D}$. Varying the base $\beta = 2 e^{3t} \in 2(1 + 3\mathbb{Z}_3)$ gives $\frac{1}{3}\partial_t G^{(3)}_{a,b}(a + 2z; 2 e^{3t}) \equiv -z \pmod 3$, which is a $3$-adic unit precisely when $\zeta_{3,a,b}(2) \not\equiv 0 \pmod 3$ (e.g. shape $(1, 1)$ where $\zeta_{3,1,1}(2) \equiv 1 \pmod 3$), making $t \mapsto \zeta_{3,1,1}(2 e^{3t})$ a local $3$-adic isometry at $t = 0$. By contrast, half of the shapes have $\zeta_{3,a,b}(2) \equiv 0 \pmod 3$, and at $p = 5$ the analogous base derivative vanishes modulo $5$ for $\beta \equiv 2, 3 \pmod 5$ (being nondegenerate for $\beta \equiv \pm 1 \pmod 5$).

[Phase 14 interpolation](../phase14/mixed-interpolation.md) · [Phase 14 nonrectangular coverage](../phase14/nonrectangular-coverage.md) · [Lean core bounds](../../NormalityChecker/Phase16StonehamBounds.lean) · [Exact certificate script](../../scripts/phase16_mixed_product.py)

## 1. Exact Mahler–Newton decay and fast $p$-adic zero lifting

Recall from Phase 14 that for $(p, q, u) \in \{(3, 5, 2), (5, 3, 4)\}$, $x_j = q^{-j} 2^{-q^j} \in \mathbb{Z}_p$ and $S_m = \sum_{j=1}^m x_j$. Put $A = q^u \equiv 1 \pmod{(p-1)p}$, let $\omega$ be the Teichmüller representative of $2$ in $\mathbb{Z}_p^\times$, write $U = 2/\omega \in 1 + p\mathbb{Z}_p$, and set $\lambda_i = -q^i \log_p U \in p\mathbb{Z}_p$.

**Proposition 1.** For every integer $k \ge 0$, $v_p(\Delta^k g(0)) \ge k + 1$, where $g(z) = S_{u(z+1)} - S_{uz} = \sum_{i=1}^u x_{i + uz}$.

*Proof.* On $z \in \mathbb{Z}_{\ge 0}$, expanding $\exp(\lambda_i A^z) = \exp(\lambda_i) \exp(\lambda_i(A^z - 1))$ separates $x_i = q^{-i}\omega^{-q^i}\exp(\lambda_i)$:
```math
x_{i+uz} = q^{-i} A^{-z} \omega^{-q^i} \exp(\lambda_i A^z)
= x_i \sum_{m=0}^{\infty} \frac{\lambda_i^m}{m!} \sum_{j=0}^{m} (-1)^{m-j} \binom{m}{j} A^{(j-1)z}.
```
Applying the $k$-th forward difference $\Delta^k|_{z=0}$ term by term yields $\Delta^k(A^{(j-1)z})|_{z=0} = (A^{j-1} - 1)^k \in p^k \mathbb{Z}_p$ because $A \equiv 1 \pmod p$. For $m = 0$, summing over $i = 1, \dots, u$ gives $(A^{-1} - 1)^k S_u$, which has valuation at least $k + 1$ since $v_p(S_u) = 1$ ($S_2 \equiv 6 \pmod 9$, $S_4 \equiv 15 \pmod{25}$). For every $m \ge 1$, since $v_p(\lambda_i) \ge 1$ and $v_p(m!) \le \frac{m-1}{p-1}$,
```math
v_p\!\left(\frac{\lambda_i^m}{m!}\right) \ge m - \frac{m-1}{p-1} = \frac{p-2}{p-1} m + \frac{1}{p-1} \ge 1,
```
so every $m \ge 1$ summand also has valuation at least $k + 1$. Thus $v_p(\Delta^k g(0)) \ge k + 1$. $\square$

Since $S_{uz} = \sum_{k \ge 0} \Delta^k g(0) \binom{z}{k+1}$ and $\binom{z}{k+1} \in \mathbb{Z}_p$ for all $z \in \mathbb{Z}_p$, truncation at $k = D - 2$ is exact modulo $p^D$. Together with Phase 14's bijective isometry $G_{a,b}(a + u(z + p^t)) - G_{a,b}(a + uz) \equiv p^t S_u \pmod{p^{t+2}}$, linear Hensel lifting recovers $\zeta_{3,a,b} \pmod{3^{55}}$ and $\zeta_{5,b,a} \pmod{5^{42}}$ in milliseconds. For the primary corner $(1, 1)$, the base-$3$ digits of $\zeta_{3,1,1}$ begin `[1, 1, 1, 1, 2, 2, 2, 0, 1, 0, 1, 0, 1, 1, 2, 1, 2, 0, 2, 1]` and the base-$5$ digits of $\zeta_{5,1,1}$ begin `[2, 2, 3, 4, 1, 1, 0, 2, 0, 4, 1, 0, 2, 2, 2]`, reproducing Phase 14's exact classes $\alpha_{3,1,1} \equiv 27 \pmod{54}$ and $\alpha_{5,1,1} \equiv 349 \pmod{500}$.

## 2. Boundary strip, single-shape maximum, and fixed-axis separation

**Lemma 1 (Boundary-strip upper density).** For $\eta \in (0, 1/2)$, put
```math
B_\eta = \bigl\{n \ge 1 : 3^{\lfloor \log_3 n \rfloor} > (1 - \eta) n \text{ or } 5^{\lfloor \log_5 n \rfloor} > (1 - \eta) n\bigr\}.
```
Then $\overline{d}(B_\eta^{(p)}) = \frac{p}{p-1}\eta$ for $p \in \{3, 5\}$, hence $\overline{d}(B_\eta) \le \frac{3}{2}\eta + \frac{5}{4}\eta = \frac{11}{4}\eta$. Every nonrectangular $n \notin B_\eta$ with $n > 5/\eta$ has deficits $1 \le a \le A(\eta)$ and $1 \le b \le B(\eta)$ where $5^{A(\eta)} > 1/\eta$ and $3^{B(\eta)} > 1/\eta$.

*Proof.* For a single base $p$, a position $n$ satisfies $p^H > (1-\eta)n$ iff $n \in [p^H, p^H/(1-\eta))$. Summing over $H \le H_0 = \lfloor \log_p(N-1)\rfloor$ with $t = p^{H_0}/N \in (1/p, 1]$ gives
```math
\frac{\#(B_\eta^{(p)} \cap [1, N))}{N}
= \min\!\left(1 - t,\, \frac{\eta}{1-\eta} t\right)
+ \frac{\eta}{1-\eta} \sum_{j=1}^{H_0} p^{-j} t + O\!\left(\frac{\log N}{N}\right).
```
This piecewise-linear function of $t$ increases for $t \le 1-\eta$ and decreases for $t \ge 1-\eta$, achieving its exact maximum at $t = 1 - \eta$ with value $\eta + \eta \sum_{j \ge 1} p^{-j} = \frac{p}{p-1}\eta$. For $n \notin B_\eta$ we have $n - P \ge \eta n > \eta Q$ and $n - Q \ge \eta n > \eta P$; thus $5^{L - a + 1} > n - P > \eta 5^L$ gives $5^{a-1} < 1/\eta$, and symmetrically $3^{b-1} < 1/\eta$. $\square$

**Lemma 2 (Single-shape maximum relative length).** Fix a nonrectangular shape $(a, b) \in \mathbb{N}_{\ge 1}^2$ at a shell $(K, L)$ with $r = Q/P \in (1/5, 3)$. The positions of shape $(a, b)$ in shell $(K, L)$ lie in the interval $[U(r) P, V(r) P)$, where
```math
U(r) = \max\!\left(1 + \frac{r}{5^a},\; r + \frac{1}{3^b}\right),
\qquad
V(r) = \min\!\left(1 + \frac{r}{5^{a-1}},\; r + \frac{1}{3^{b-1}},\; 3,\; 5r\right).
```
For every cutoff $N > U(r)P$, the relative length $\frac{\min(N, V(r)P) - U(r)P}{N} \le 1 - \frac{U(r)}{V(r)}$. Its exact supremum over $r \in (1/5, 3)$ is:
- **$\frac{4}{11} = 0.363636\ldots$** for $(a, b) = (1, 1)$, uniquely attained at $r = 5/6$;
- **at most $\frac{2}{13} = 0.153846\ldots$** for every $(a, b) \neq (1, 1)$ (specifically $\frac{2}{13}$ at $(1, 2), r = 10/9$, and $\frac{4}{41}$ at $(2, 1), r = 25/36$).

*Proof.* For $(1, 1)$: on $[1/4, 2]$ we have $V(r) = 1 + r$, so $1 - U(r)/V(r) = \min(\frac{4r}{5}, \frac{2}{3})/(1+r)$, uniquely maximized at $r = 5/6$ with value $4/11$ (kernel-verified in `Phase16StonehamBounds.single_shape_one_one_max`). For $r < 1/4$, $V(r) \le 5r$ and $U(r) \ge 1 + r/5$, so $V > U$ forces $r > 5/24$ and $1 - U/V \le \frac{24}{25} - \frac{1}{5r} < \frac{4}{25} < \frac{4}{11}$; for $r > 2$, $V(r) \le 3$ and $U(r) \ge r + 1/3 > 7/3$, giving $1 - U/V < 2/9 < 4/11$.

For $(a, b) \neq (1, 1)$ and any $r > 0$ with $V(r) > U(r)$, we check $1 - U/V \le 2/13$, equivalently $13U - 11V \ge 0$, in five exhaustive cases:
1. *$b \ge 3$:* $V - U \le (r + 3^{1-b}) - (r + 3^{-b}) = 2 \cdot 3^{-b} \le 2/27$ while $V > U \ge 1 + r/5^a > 1$, so $(V - U)/V < 2/27 < 2/13$.
2. *$b = 2$ and $r \ge 10/9$:* $U \ge r + 1/9$ and $V \le r + 1/3$, so $13U - 11V \ge 2r - 20/9 \ge 0$ (equality at $(1, 2), r = 10/9$).
3. *$b = 2$, $r < 10/9$, and $a = 1$:* $U \ge 1 + r/5$ and $V \le r + 1/3$, so $13U - 11V \ge \frac{28}{3} - \frac{42}{5} r > \frac{28}{3} - \frac{42}{5}\cdot\frac{10}{9} = 0$.
4. *$b = 2$, $r < 10/9$, and $a \ge 2$:* $U \ge 1 + r/5^a$ and $V \le 1 + r/5^{a-1}$, so $13U - 11V \ge 2 - \frac{42r}{5^a} > 2 - \frac{42 \cdot 10/9}{25} = \frac{2}{15} > 0$.
5. *$b = 1$ and $a \ge 2$:* $V > U$ forces $1 + r/5 \ge V > U \ge r + 1/3$, hence $r < 5/6 < 10/9$, and Case 4's bound gives $13U - 11V \ge 2 - \frac{42r}{5^a} > \frac{3}{5} > 0$. $\square$

**Lemma 3 (Analytic fixed-axis separation).** For fixed $a \ge 1$ and $1 \le b_1 < b_2$, $G^{(3)}_{a,b_1}(m) - G^{(3)}_{a,b_2}(m) = (3^{b_1} - 3^{b_2}) x_m$ has exact $3$-adic valuation $b_1$, hence $v_3(\zeta_{3,a,b_1} - \zeta_{3,a,b_2}) = b_1 - 1$. Symmetrically, for fixed $b \ge 1$ and $1 \le a_1 < a_2$, $v_5(\zeta_{5,b,a_1} - \zeta_{5,b,a_2}) = a_1 - 1$. For fixed $b$ and $a_1 < a_2$ with $2 \mid (a_2 - a_1)$, $v_3(G^{(3)}_{a_1,b}(m) - G^{(3)}_{a_2,b}(m)) = 1 + v_3((a_2 - a_1)/2)$, precluding same-shell coincidences. Moreover $\zeta_{p,a,b} \notin \mathbb{Z}_{\ge 0}$ because $G_{a,b}(m) > 0$ as a real rational for every integer $m \ge a$.

## 3. Proof of Theorem 1: certified multi-depth non-coincidence ladder

Recall from Phase 14 that for any fixed depths $h, k \ge 1$, the binary discrepancy satisfies $D_\infty(x) \le \overline{d}(F_{h,k})$, where $F_{h,k}$ consists of nonrectangular positions losing at least $h$ ternary layers and at least $k$ quinary layers. Indeed, by Phase 14's bounded-denominator criterion, $D_\infty(x) \le \sup_{M \ge 1} \overline{d}(\{n : \operatorname{den}(R_n) \le M\})$; since full rectangles satisfy $\operatorname{den}(R_n) \ge 3^{K - 1 - \lfloor \log_3 L \rfloor} \to \infty$ (Phase 14 `ProductThreeFiveRectangleValuation`), every bounded-denominator set $\{n : \operatorname{den}(R_n) \le M\}$ is contained in $F_{h,k}$ up to finitely many positions. Write $\alpha_3(a,b) = a + 2\zeta_{3,a,b} \in \mathbb{Z}_3$ and $\alpha_5(b,a) = b + 4\zeta_{5,b,a} \in \mathbb{Z}_5$; a position of shape $(a, b)$ at shell $(K, L)$ lies in $F_{h,k}$ iff
```math
L \equiv \alpha_3(a, b) \pmod{2 \cdot 3^{h-1}}
\qquad\text{and}\qquad
K \equiv \alpha_5(b, a) \pmod{4 \cdot 5^{k-1}}.
```

Fix $\eta \in (0, 1/2)$ and $\delta \in (0, 1)$. For any large cutoff $N$, split $[0, N)$ into:
1. the initial prefix $[0, \delta N)$ (proportion $\le \delta$);
2. the boundary strip $B_\eta \cap [\delta N, N)$ (upper density $\le \frac{11}{4}\eta$ by Lemma 1);
3. the bulk region $W = ([\delta N, N) \setminus B_\eta) \cap F_{h,k}$, where every position has shape $(a, b)$ in the finite grid $\mathcal{G} = \{1, \dots, A(\eta)\} \times \{1, \dots, B(\eta)\}$.

Any two positions $n_1, n_2 \in [\delta N, N)$ satisfy $n_1/n_2 \in (\delta, 1/\delta)$, so their shell indices satisfy $|K_1 - K_2| \le \lfloor \log_3(1/\delta) \rfloor + 1$ and $|L_1 - L_2| \le \lfloor \log_5(1/\delta) \rfloor + 1$. Conservatively, our certificate uses
```math
R_K := \lfloor \log_3(1/\delta) \rfloor + 2,
\qquad
R_L := \lfloor \log_5(1/\delta) \rfloor + 2
```
(certified strictly larger than $\log_3(1/\delta) + 1$ and $\log_5(1/\delta) + 1$ via exact integer power tests $3^{R_K - 1} > 1/\delta$ and $5^{R_L - 1} > 1/\delta$).
Choose depths $(h, k)$ such that:
- $2 \cdot 3^{h-1} > R_L$ and $4 \cdot 5^{k-1} > R_K$ (so no single shape $(a, b)$ can occur in $F_{h,k}$ at two distinct shells in $[\delta N, N)$);
- for every pair of distinct shapes $(a_1, b_1) \neq (a_2, b_2)$ in $\mathcal{G}$, there is no pair $(d_L, d_K)$ with $|d_L| \le R_L$ and $|d_K| \le R_K$ satisfying simultaneously
```math
\alpha_3(a_1, b_1) - \alpha_3(a_2, b_2) \equiv d_L \pmod{2\cdot 3^{h-1}},
\qquad
\alpha_5(b_1, a_1) - \alpha_5(b_2, a_2) \equiv d_K \pmod{4\cdot 5^{k-1}}.
```
Then $W$ can intersect **at most one shape $(a, b) \in \mathcal{G}$ at at most one shell $(K, L)$**. By Lemma 2, $\#W / N \le 4/11 + O(1/N)$. Summing the three pieces gives
```math
\limsup_{N\to\infty} D_N(x) \le \overline{d}(F_{h,k}) \le \frac{4}{11} + \frac{11}{4}\eta + \delta.
```

The script `scripts/phase16_mixed_product.py` certifies zero collisions on three progressively sharper grids:

| Tier | $\eta$ | $\delta$ | Bulk grid $\mathcal{G}$ | $(R_K, R_L)$ | Certified $(h, k)$ | Unconditional upper bound on $D_\infty(x)$ |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| Tier 1 | $10^{-3}$ | $10^{-4}$ | $5 \times 7$ (35 shapes) | $(10, 7)$ | $(7, 5)$ | $0.3664863636$ ($4/11 + 2.85 \times 10^{-3}$) |
| Tier 2 | $10^{-6}$ | $10^{-7}$ | $9 \times 13$ (117 shapes) | $(16, 12)$ | $(9, 6)$ | $0.3636392136$ ($4/11 + 2.85 \times 10^{-6}$) |
| Tier 3 | $10^{-10}$ | $10^{-11}$ | $15 \times 21$ (315 shapes) | $(25, 17)$ | $(9, 7)$ | **$0.3636363639$ ($4/11 + 2.85 \times 10^{-10}$)** |

*Remark on exact $4/11$.* Every fixed tolerance $\varepsilon > 0$ is finitely certifiable by the same procedure. Removing $\varepsilon$ completely to prove $\lim_{h,k\to\infty} \overline{d}(F_{h,k}) = 4/11$ is equivalent to ruling out simultaneous exact integer differences $\alpha_3(a_1, b_1) - \alpha_3(a_2, b_2) \in \mathbb{Z}$ and $\alpha_5(b_1, a_1) - \alpha_5(b_2, a_2) \in \mathbb{Z}$ across all infinitely many pairs of distinct shapes.

## 4. Proof of Theorems 2 and 3: simultaneous ultrametric separation and super-exponential sparsity

**Proof of Theorem 2.** Suppose $(K_1, L_1) \neq (K_2, L_2)$ are active shells of shape $(a, b)$ retaining at most $r_i$ ternary and $s_i$ quinary layers, so $h_i := K_i - r_i \ge 1$ ternary layers and $k_i := L_i - s_i \ge 1$ quinary layers are lost. By Phase 14's exact valuation formula,
```math
L_i \equiv \alpha_3(a, b) \pmod{2 \cdot 3^{h_i - 1}},
\qquad
K_i \equiv \alpha_5(b, a) \pmod{4 \cdot 5^{k_i - 1}}.
```
If $L_1 = L_2 = L$, then since $(K_i, L)$ are both active nonrectangular shells, $3^{K_i}$ lies in $(5^L/3, 5^{L+1})$, so $|K_1 - K_2| \le 2$; yet $K_1 \neq K_2$ implies $4 \mid (K_2 - K_1)$, contradiction. Symmetrically $K_1 = K_2$ implies $|L_1 - L_2| \le 1$, contradicting $2 \mid (L_2 - L_1)$. Hence $K_1 \neq K_2$ and $L_1 \neq L_2$, and active overlap $5^L \asymp 3^K$ forces them to be ordered together: $K_1 < K_2$ and $L_1 < L_2$. Subtracting the two congruences gives
```math
2 \cdot 3^{\min(h_1, h_2) - 1} \mid (L_2 - L_1),
\qquad
4 \cdot 5^{\min(k_1, k_2) - 1} \mid (K_2 - K_1),
```
yielding the displayed lower bounds. For linear retained layers $r_i \le \theta K_i$, $s_i \le \theta L_i$ ($0 \le \theta < 1$), we have $h_2 = (1-\theta)K_2 > (1-\theta)K_1 = h_1$ and $k_2 > k_1$, so $K_2 \ge 4 \cdot 5^{(1-\theta)L_1 - 1}$ and $L_2 \ge 2 \cdot 3^{(1-\theta)K_1 - 1}$. Because every position in a shell interval $[U_i, V_i)$ of shape $(a, b)$ at shell $(K_i, L_i)$ shares the same prefix $R_n$ and satisfies $\log U_i = K_i \log 3 + O(1) = L_i \log 5 + O(1)$ with $V_i / U_i \le 3$, this implies $\log U_2 \ge c_\theta \, U_1^{1-\theta}$, i.e., $U_2 \ge \exp(c_\theta U_1^{1-\theta})$. For bounded denominators $\operatorname{den}(R_n) \le M$, $r_i \le \log_3 M$ and $s_i \le \log_5 M$ give $K_{j+1} > \frac{4}{25M} 3^{K_j}$ and $U_{j+1} \ge \exp(c_M U_j)$. $\square$

**Proof of Theorem 3.** Fix $\varepsilon > 0$. By Phase 14's clean-block bounded-denominator criterion, there exist $M = M(\varepsilon)$ and $N_0(\varepsilon)$ such that for all $N \ge N_0(\varepsilon)$,
```math
D_N(x) \le \frac{\varepsilon}{2} + \frac{1}{N} \#\{n < N : \operatorname{den}(R_n) \le M\}.
```
Choose $\eta = \varepsilon / 16$, so the boundary strip $B_\eta$ contributes at most $\frac{11}{4}\eta + o(1) < \frac{\varepsilon}{4}$ eventually. On full rectangles, Phase 14 proves $\operatorname{den}(R_n) \ge 3^{K - 1 - \lfloor \log_3 L \rfloor} \to \infty$, so only finitely many full-rectangle positions satisfy $\operatorname{den}(R_n) \le M$. Let $\mathcal{G} = \{1, \dots, A(\eta)\} \times \{1, \dots, B(\eta)\}$ be the finite set of bulk nonrectangular shapes. Put $\delta = \varepsilon / 8$. If $D_N(x) > \varepsilon$ at a large cutoff $N$, then at least one bulk shape $(a, b) \in \mathcal{G}$ must have an exceptional shell interval $[U_j, V_j)$ with $\operatorname{den}(R_n) \le M$ intersecting $[\delta N, N)$.

By Theorem 2, for each fixed $(a, b) \in \mathcal{G}$, the logarithms $m_j = \log U_j$ of successive exceptional shell intervals $[U_j, V_j)$ (each of logarithmic width $\log(V_j / U_j) \le \log 3$) satisfy $m_{j+1} \ge c_M e^{m_j}$ for all large $j$, so there are at most $O_{M,\mathcal{G}}(\log^* T)$ integers $m \le T$ for which any $[U_j, V_j)$ intersects $[\delta e^m, e^{m+1})$. Summing over the finitely many shapes in $\mathcal{G}$ gives $\#\{m \le T : \exists\, N \in [e^m, e^{m+1}) \text{ with } D_N(x) > \varepsilon\} = O_\varepsilon(\log^* T)$. Since each bad integer $m$ contributes at most $O(1)$ to $\sum_{N \in [e^m, e^{m+1})} 1/N$ and $O(1/m)$ to $\sum_{N \in [e^m, e^{m+1})} 1/(N \log N)$, and the bad $m$'s grow as a power tower $m_{j+1} \ge c e^{m_j}$, $\sum 1/m_j < \infty$ and $\sum_{N \le X, D_N > \varepsilon} 1/N = O_\varepsilon(\log^* \log X)$. $\square$

Similarly, for any $\theta \in [0, 1)$, the set $E_\theta$ of positions retaining at most $\theta K$ ternary and $\theta L$ quinary layers has iterated-logarithmic density zero: $\frac{1}{\log\log X} \sum_{n \in E_\theta, n \le X} \frac{1}{n\log n} \to 0$.

## 5. Local $p$-adic base-variation derivative and actual shell scan

Varying the binary base $\beta = 2 e^{3t} \in 2(1 + 3\mathbb{Z}_3)$ in $x_j(\beta) = 5^{-j} \beta^{-5^j}$ produces an exact cancellation of the $5^{-j}$ factor upon differentiation:
```math
\partial_t x_j(2 e^{3t}) = -3 \cdot 5^{-j} \cdot 5^j (2 e^{3t})^{-5^j} = -3 (2 e^{3t})^{-5^j}.
```
Modulo $9$, $(2 e^{3t})^{-5^j} \equiv 2^{-5^j} \pmod 3$, which is $2 \pmod 3$ for every $j \ge 1$. Summing over $1 \le j \le 2z$ gives $\partial_t S_{2z}(2 e^{3t}) \equiv -3 \cdot 2z \cdot 2 \equiv -3z \pmod 9$, hence (since the extra terms in $G^{(3)}_{a,b}$ are divisible by $9$)
```math
\frac{1}{3} \partial_t G^{(3)}_{a,b}(a + 2z; 2 e^{3t}) \equiv -z \pmod 3
```
for every shape $(a, b)$. At $\beta = 2$ ($t = 0$), $\partial_t \zeta_{3,a,b}(2 e^{3t})|_{t=0}$ is a $3$-adic unit precisely when $\zeta_{3,a,b}(2) \not\equiv 0 \pmod 3$. For the primary corner $(1, 1)$, $\zeta_{3,1,1}(2) \equiv 1 \pmod 3$, so $t \mapsto \zeta_{3,1,1}(2 e^{3t})$ is a local $3$-adic isometry around $t = 0$ (whereas $\beta \equiv 5 \pmod 9$ is degenerate with $S_2(5) \equiv 0 \pmod 9$). However, this local unit-derivative property is not uniform across shapes or primes: among $1 \le a, b \le 8$, $32$ of the $64$ shapes have $\zeta_{3,a,b}(2) \equiv 0 \pmod 3$ (e.g. $(1, 2)$ and $(2, 1)$), and for $p = 5$ the analogous sum $\sum_{j=1}^{4z} 2^{-3^j} \equiv 2z(2 + 3) \equiv 0 \pmod 5$ vanishes identically for $\beta \equiv 2, 3 \pmod 5$ (the nondegenerate residue classes at $p = 5$ are $\beta \equiv \pm 1 \pmod 5$). Consequently, base variation around $\beta = 2$ yields a local $3$-adic isometry on the primary corner $(1, 1)$ (and half of all shapes), not a uniform metric normality theorem on $(2 + 9\mathbb{Z}_3) \times (2 + 25\mathbb{Z}_5)$.

In an exact scan of all $336{,}518$ overlapping shell pairs $(K, L)$ with $K \le 200{,}000$ for the primary corner $(1, 1)$:
- $2{,}799$ pairs satisfy $h \ge 2$ and $k \ge 2$; $185$ pairs satisfy $h \ge 3$ and $k \ge 3$;
- the deepest balanced joint loss is $(h, k) = (6, 5)$ at $(K, L) = (9{,}849,\, 6{,}723)$;
- the largest joint loss sum $h + k$ (with $h, k \ge 1$) is $(11, 1)$ at $(K, L) = (25{,}513,\, 17{,}415)$.

## 6. Residual limits and reproduction

Ordinary binary normality of $\alpha_{2,3}\alpha_{2,5}$ remains open: ruling out bounded denominators at all late shells requires excluding simultaneous super-exponential $3$-adic and $5$-adic integer approximations $v_3(L - \alpha_3(a,b)) \ge K - O(1)$ and $v_5(K - \alpha_5(b,a)) \ge L - O(1)$ for the specific base $\beta = 2$.

```sh
python3 -B scripts/phase16_mixed_product.py
```
