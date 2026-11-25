# Specialist Reviewer Packet: Exceptional Orbits and Discrepancy of Stoneham Products (v1.0)

**Author:** Christopher Anderson (Independent Researcher)  
**Pinned commit:** `e4809cf561573aef588e6ffc491a35cdb79fd9ec` (`research-checkpoint-18`)  
**Status:** AI-assisted preprint draft; cross-model audited, no independent human specialist review yet.

This packet extracts the main claims, shortest complete proof outlines, evidence labels, external inputs, reproduction links, and the specific steps where specialist scrutiny is most valuable.

---

## 1. Empirical-mixture law and scalar discrepancy convergence (Theorem 2.1)

- **Statement:** Let $p < q$ be distinct odd primes coprime to $B \ge 2$, $x = \alpha(B,p)\alpha(B,q)$, and $R_n = \sum_{p^i+q^j \le n} p^{-i}q^{-j} B^{n-p^i-q^j}$. Partition each $(K,L)$-shell into constant-prefix plateaus $I = [U,V)$ carrying $\{p,q\}$-smooth rational $B$-cycles $c(I)$. Let $w_{c,N} = N^{-1}\sum_{c(I)=c} |I \cap [0,N)|$ and $\mathcal{W}$ be all coordinatewise subsequential limits of $(w_{c,N})_c$. Along every sequence with $w_{c,N} \to w_c$ for all $c$, $\mu_N(x) \to \sigma(w) = (1 - \sum_c w_c)\lambda + \sum_c w_c \nu_c$ weakly on $\T$ and $D_N(x) \to \Delta(\sigma(w))$. In particular, $D^+(x) = \max_{w \in \mathcal{W}} \Delta(\sigma(w))$.
- **Evidence:** **Lean-supported paper proof** (`SmoothOrbit.fixed_support_orbit_estimate` at [SmoothOrbit.lean#L207](https://github.com/eldernos/MathematicsResearch/blob/e4809cf561573aef588e6ffc491a35cdb79fd9ec/NormalityChecker/SmoothOrbit.lean#L207); `CircleDiscrepancy.disc_sub_tendsto` at [CircleDiscrepancy.lean#L137](https://github.com/eldernos/MathematicsResearch/blob/e4809cf561573aef588e6ffc491a35cdb79fd9ec/NormalityChecker/CircleDiscrepancy.lean#L137)).
- **External inputs:** None (Vandehey 2019, Cor. 1.2 is precedent; the qualitative short-orbit bound is proved internally in Lean).
- **Proof sketch:** Split $[0,N)$ into blocks of length $L_N = \lfloor \sqrt{N} \rfloor$. At most $O(1 + \log^2 N)$ plateau boundaries cost $O(N^{-1/2}(1+\log^2 N))$. On clean blocks, $m_I \le N^2 \le L_N^5$ eventually; `SmoothOrbit` gives uniform arc error $\le \varepsilon L_N$ for $m_I > M$, while for $m_I \le M$ incomplete cycles cost $\le M$ per block, totaling $O(M/\sqrt{N})$ over $\lceil N/L_N \rceil$ blocks. Hence the rational empirical measure $\widetilde{\mu}_N$ converges *uniformly over all arcs* to $\sigma(w)$, giving $\Delta(\widetilde{\mu}_N) \to \Delta(\sigma(w))$. Because $0 \le B^n x - R_n = O(1/n)$, uniform continuity gives weak convergence $\mu_N(x) \to \sigma(w)$, and `CircleDiscrepancy.disc_sub_tendsto` (arc enlargement by $t+\eta$, $\eta\downarrow 0$) transfers $\Delta(\widetilde{\mu}_N) \to \Delta(\sigma(w))$ directly to $D_N(x) \to \Delta(\sigma(w))$ without testing an indicator at an atom endpoint.
- **Review requested on:** Uniformity of the $O(M/\sqrt{N})$ incomplete-cycle sum across blocks and the circle-enlargement transfer across atomic endpoints.

---

## 2. Local $p$-adic isometry, Eisenstein non-integrality, and $O_\varepsilon(\log^* T)$ scale sparsity (Propositions 3.1–3.2, Theorem 3.3)

- **Statements:**
  - **Prop. 3.1** (**Lean-supported paper proof**): The $p$-layers lost from $p^K$ in $\den(R_n)$ equal $\min(K, v_p(G_{a,d}(L)))$. Under the simple-zero conditions ($q^u \equiv 1 \bmod p$, $\omega^{q^{j+u}} = \omega^{q^j}$, $p \nmid S_i$ for $1 \le i < u$, $v_p(S_u)=1$), $G_{a,d}(a+uz)/p$ is a bijective isometry of $\Z_p$ with unique root $\zeta_{p,a,d}$ ($\zeta_{p,0,0}=0$), so $v_p(G_{a,d}(a+uz)) = 1 + v_p(z - \zeta_{p,a,d})$. Infinitely many radices $B \ge 2$ satisfy these conditions at both primes for every distinct odd prime pair $(p,q)$.
  - **Prop. 3.2** (**Paper proof**): For $(B,p,q) = (2,3,5)$ or $(2,5,3)$ and all $a,d \ge 1$, $\zeta_{p,a,d} \notin \Z$.
  - **Thm. 3.3** (**Lean-supported paper proof**): Under simple-zero conditions on both axes, joint $(h,k)$-loss logarithmic density is $1/(uv p^{h-1} q^{k-1})$ (also conditional on fixed shapes); bad logarithmic bins $m \le T$ with $\exists N \in [e^m, e^{m+1}), D_N(x) > \varepsilon$ number $O_{B,p,q,\varepsilon}(\log^* T)$; $\sum_{D_N > \varepsilon} 1/(N\log N) < \infty$; $\{B^n x\}$ is logarithmically equidistributed; and $D^-(x) = 0$.
- **Lean building blocks:** [ProductThreeFiveInterpolation.lean#L123](https://github.com/eldernos/MathematicsResearch/blob/e4809cf561573aef588e6ffc491a35cdb79fd9ec/NormalityChecker/ProductThreeFiveInterpolation.lean#L123), [#L168](https://github.com/eldernos/MathematicsResearch/blob/e4809cf561573aef588e6ffc491a35cdb79fd9ec/NormalityChecker/ProductThreeFiveInterpolation.lean#L168), [#L182](https://github.com/eldernos/MathematicsResearch/blob/e4809cf561573aef588e6ffc491a35cdb79fd9ec/NormalityChecker/ProductThreeFiveInterpolation.lean#L182); [Phase16StonehamBounds.lean#L248](https://github.com/eldernos/MathematicsResearch/blob/e4809cf561573aef588e6ffc491a35cdb79fd9ec/NormalityChecker/Phase16StonehamBounds.lean#L248), [#L291](https://github.com/eldernos/MathematicsResearch/blob/e4809cf561573aef588e6ffc491a35cdb79fd9ec/NormalityChecker/Phase16StonehamBounds.lean#L291).
- **External inputs:** None (Mahler 1958 / Robert 2000 cited for context; the exact decay $v_p(\nabla^k g(0)) \ge k+1$ is proved directly).
- **Proof sketch:** For Prop. 3.1, expanding $\exp(-q^i\ell A^z) = \exp(-q^i\ell)\exp(-q^i\ell(A^z-1))$ gives $v_p(\nabla^k g(0)) \ge k+1$, and Chu–Vandermonde gives $F(z+y)-F(z) \equiv y S_u \pmod{p^{t+2}}$ for $v_p(y)=t$ (using $k+1-\lfloor\log_p(k+1)\rfloor \ge 2$ for odd $p$ and $k \ge 1$). For Prop. 3.2, extending $S_j - S_{j-1} = x_j$ backwards yields $x_{-h} = q^h 2^{-1/q^h}$ with compatible roots in $\Z_p^\times$; when $m \le a-2$, the minimal negative index $-H$ carries nonzero coefficient ($p-1$ or $p^d-1$) on $\theta = 2^{-1/q^H}$ in the $\Q$-basis $\{1,\theta,\dots,\theta^{q^H-1}\}$ (Eisenstein at $2$). For Thm. 3.3, subtracting the two residue congruences gives power-tower spacing $\log U_2 \gg U_1$ on each fixed bulk shape, hence $s_{j+2} > \exp(s_j)$ eventually, yielding $O_\varepsilon(\log^* T)$ bad bins and logarithmic equidistribution by summation by parts.
- **Review requested on:** (1) The $v_p(\nabla^k g(0)) \ge k+1$ bound and Vandermonde increment in Prop. 3.1 (including $p \mid u$); (2) the Teichmüller check $\omega^{q^{u(-z)}} = \omega$ and backward analytic continuation in Prop. 3.2; (3) the empty-fibre boundary cases $a=L$ and $d=K$.

---

## 3. Threshold $4/11 + 2.85 \times 10^{-10}$, certified examples, and zero-slack equivalence (Theorem A, Propositions 4.1–4.2, Corollary 4.3)

- **Statement:** For $x = \alpha(2,3)\alpha(2,5)$, $D^+(x) \le 4/11 + 2.85 \times 10^{-10}$ and $D^+(x) \le 4/11 \iff C_0 \le 4/11$ (if either fails, $D^+(x) = C_0$). Exact multi-depth zero-collision certificates also give $D^+ \le 11250083/30000000$, $720004991/1860000000$, and $720004379/1740000000$ for $(2,3,7)$, $(2,3,13)$, and $(36,5,7)$, respectively. Ordinary binary normality remains open.
- **Evidence:** **Lean-supported paper proof** (Theorem A, Prop. 4.1, Cor. 4.3) + **Finite certificate** (Prop. 4.2). Lean verifies $M_{p,q}$ ([Phase17DiscrepancyBounds.lean#L184](https://github.com/eldernos/MathematicsResearch/blob/e4809cf561573aef588e6ffc491a35cdb79fd9ec/NormalityChecker/Phase17DiscrepancyBounds.lean#L184), [#L232](https://github.com/eldernos/MathematicsResearch/blob/e4809cf561573aef588e6ffc491a35cdb79fd9ec/NormalityChecker/Phase17DiscrepancyBounds.lean#L232)). Scripts: [phase16_mixed_product.py](https://github.com/eldernos/MathematicsResearch/blob/e4809cf561573aef588e6ffc491a35cdb79fd9ec/scripts/phase16_mixed_product.py), [phase17_mixed_product_orbits.py](https://github.com/eldernos/MathematicsResearch/blob/e4809cf561573aef588e6ffc491a35cdb79fd9ec/scripts/phase17_mixed_product_orbits.py).
- **Proof sketch:** On $[\delta N, N)$ outside the two $\eta$-boundary strips, zero collisions on $[1,A]\times[1,D]$ at depths $(h,k)$ permit at most one bulk shape and one shell, bounding $\sum_c w_c \le S = M_{p,q} + (\frac{p}{p-1}+\frac{q}{q-1})\eta + \delta$. For $(2,3,5)$, every nontrivial cycle $c \ne 0$ of denominator $m = 3^r 5^s > 1$ has $\Delta(\nu_c) \le 2/3$ and period $\ge 4m/15$, giving $-\frac{11}{4}(1-t) \le \nu_c([0,t)) - t \le \frac{11}{4}t$. If $\Delta(\sigma(w)) > 4/11$, convexity $w_0 + \frac{2}{3}w' \le 4/11 + \gamma - \frac{1}{3}w'$ forces $w' < 3\gamma$ and $w_0 > 4/11 - 2\gamma \ge \frac{11}{4}w'$, which traps $F_{\sigma(w)}(t) \in [0, w_0]$ and forces $\Delta(\sigma(w)) = w_0$.
- **Review requested on:** The endpoint grid-point counts $\lceil mt \rceil - 1 < mt$ and $m - \lceil mt \rceil \le m(1-t)$ and the dominance step $w_0 \ge \frac{11}{4}w' \implies \Delta(\sigma(w)) = w_0$.

---

## 4. Independent integer parameters and dyadic ($c=2$) quadratic plateaus (Theorems 6.1, 6.3, 7.1; Propositions 7.2–7.3; Corollary 7.4)

- **Theorem 6.1** (**Kernel-verified**): $\alpha(2,3)\alpha(2,5)$ is irrational and $D^+ \le 43/45$ ([ProductThreeFive.lean#L77](https://github.com/eldernos/MathematicsResearch/blob/e4809cf561573aef588e6ffc491a35cdb79fd9ec/NormalityChecker/ProductThreeFive.lean#L77), [#L93](https://github.com/eldernos/MathematicsResearch/blob/e4809cf561573aef588e6ffc491a35cdb79fd9ec/NormalityChecker/ProductThreeFive.lean#L93)).
- **Theorem 6.3** (**Lean-supported paper proof**; external input: Ridout 1957, Thm., p. 125): For multiplicatively independent $c,d \ge 2$ with $\gcd(B,cd)=1$, $\alpha(B,c)\alpha(B,d)$ is transcendental and $D^+ < 1$.
- **Theorem 7.1 & Proposition 7.2** (**Kernel-verified**): All-prefix plateau law, $D^+(y) = \frac{1}{4}\limsup_k \Delta_b(y_k)$, $D^-(y)=0$, logarithmic equidistribution, normality iff $q_k \to \infty$, exact $q_k = 2^{[k-v_2(2A)-s-v_2(k-\kappa)]_+}$, algebraicity sufficiency, and two-class resonant-radix classification ([QuadraticPlateauSpectrum.lean#L116](https://github.com/eldernos/MathematicsResearch/blob/e4809cf561573aef588e6ffc491a35cdb79fd9ec/NormalityChecker/QuadraticPlateauSpectrum.lean#L116), [ParameterTwoQuadraticOrbits.lean#L16](https://github.com/eldernos/MathematicsResearch/blob/e4809cf561573aef588e6ffc491a35cdb79fd9ec/NormalityChecker/ParameterTwoQuadraticOrbits.lean#L16), [ResonantRadixClasses.lean#L114](https://github.com/eldernos/MathematicsResearch/blob/e4809cf561573aef588e6ffc491a35cdb79fd9ec/NormalityChecker/ResonantRadixClasses.lean#L114)).
- **Proposition 7.3 & Corollary 7.4** (**Lean-supported paper proof**): Exact dyadic cycle discrepancies for $D=1$ ($D^+(y) = 2^{-2-[H-s]_+}$ for $b \equiv 1 \bmod 4$; singleton criterion for $1/4$; sub-quarter bound for $b \equiv 3 \bmod 4$; explicit $Z_k$ plateau points via [Phase16StonehamBounds.lean#L68](https://github.com/eldernos/MathematicsResearch/blob/e4809cf561573aef588e6ffc491a35cdb79fd9ec/NormalityChecker/Phase16StonehamBounds.lean#L68)) and unconditional bounds $D^+((\alpha^2-2\alpha+C)/3) \le \frac{1}{4}(1 - 1/(3\cdot 2^{v_2(b+1)}))$ ($b \equiv 2 \bmod 3$ odd, $C \not\equiv 1 \bmod 3$) and $D^+((\alpha^2-2\alpha)/9) \le 5/72$ ($b=5$).
- **Review requested on:** Application of Ridout (1957) in Theorem 6.3 (including when $\gcd(c,d) > 1$), and the modulo-$3$ / modulo-$9$ cycle-discrepancy bounds in Proposition 7.3 and Corollary 7.4.

## Reproduction

```sh
wsl -d Ubuntu -- bash papers/wsl-build.sh 08-stoneham-product-orbits
python -B scripts/phase16_mixed_product.py
python -B scripts/phase17_mixed_product_orbits.py
python -B scripts/phase17_dyadic_stoneham.py
```
