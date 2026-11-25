# Independent audit: the distinct-prime polynomial-normal algebra

Target: [notes/phase19/independent-axes.md](../independent-axes.md), working tree on top of `0d54868`. I read the note, the Phase 18 fixed-support criterion ([principal.md](../../phase18/principal.md#a-fixed-support-criterion-for-all-prefixes)) and the kernel statement `SmoothOrbitEstimate` in `NormalityChecker/SmoothOrbit.lean`, and the single-series shell argument in [nonlinear.md](../nonlinear.md) §2–3. I edited no author file and no manuscript. I also ran an exact-arithmetic check of the central pole formula (scratch script, not committed; see "Numerical check").

**Verdict.** I found no counterexample and no mathematical gap. Every step I re-derived goes through as stated. The objections below concern presentation: the Liouville paragraph is loose (O1), the application of the Phase 18 criterion is not spelled out (O2), notation is undefined (O3), and the role of the two independence notions deserves a sentence (O4).

## What I re-derived

**Ordering of the choices.** The order is consistent and acyclic. First `C` (depends only on the primes), then `E_k` (depends on `n_k` and `C`), then the tuples `θ_{ij}` (depend only on `p_i`), then `A_{j,k}` by recursion in `k`. Nothing depends on `P`; only the threshold `k_0(P)` does. So one sequence serves every `P`.

**Reduction and CRT.**
* `p_i` are distinct and coprime to `b`, so `p_j`, `b` are units mod `p_i^k` and the moduli `p_j` and `p_i^k` (`i≠j`) are pairwise coprime. `U_{j,k-1}` has denominator `p_j^a b^c`, so it is `p_i`-integral and the right-hand side of the congruence is defined mod `p_i^k`.
* Dividing the congruence by the unit `p_j^{E_k} b^{n_k}` gives `V_{j,k} ≡ θ_{ij} − U_{j,k-1} (mod p_i^k)`, hence `U_{j,k} ≡ θ_{ij} (mod p_i^k)` and `v_{p_i}(V_{j,k}) ≥ k−1` for `k≥2`.
* The least positive representative of `A_{j,k}` is `<p_j∏_{i≠j}p_i^k ≤ p_j^{Ck} ≤ p_j^{E_k}`, so the weights lie in `(0,1]`. `A_{j,k}≡1 (mod p_j)` gives the exact denominator `p_j^{E_k}`. For `m=1` the moduli are `p_1` and `A=1`.
* `E_k` is strictly increasing, and `Δ_k=E_k−E_{k−1}=C+⌊log₂n_k⌋−⌊log₂n_{k−1}⌋ ≥ C+log₂(n_k/n_{k−1})−2 → ∞`. This is exactly where `n_{k+1}/n_k→∞` is needed. `E_k=O(k+log n_k)=O(log n_k)` since `n_k ≥ 2^k` eventually.
* For the explicit schedule `n_k=∏_{h≤k}(2+⌈log₂(h+1)⌉)`: `n_k/n_{k−1}→∞` slowly, and `log n_k ≤ k log(2+⌈log₂(k+1)⌉) = O(k log log(k+2))`. Correct.

**Computable algebraically independent tuples.** A nonzero `F∈ℤ[x_1,…,x_{m−1}]` cannot vanish on a product of infinite sets, so the search succeeds. If the ball is refined about `a` to depth `d>v_p(F(a))`, then `F≡F(a) (mod p^d)` on the ball, so `v_p(F(θ))=v_p(F(a))<∞`. Depths strictly increase, so `θ mod p^k` is available after finitely many steps. Correct, including the empty tuple for `m=1`.

**Shell analysis (n_k ≤ n < n_{k+1}).**
* A tuple with `h` newest indices has exponent in `[hn_k, hn_k+(r−h)n_{k−1}]`. Outside the windows `[jn_k, jn_k+rn_{k−1}]`, `1≤j≤r`, exactly the tuples with `h≤⌊n/n_k⌋` are present, and all tuples of old indices are present for large `k`. Hence the prefix is the `z`-degree-`≤ℓ` truncation of `P(U_{k−1}+zV_k)` at `z=1`. The windows are disjoint from each other and from the next shell once `rn_{k−1}<n_k`. The case `⌊n/n_k⌋≥r` gives `ℓ=r` and starts after the last window.
* Because the newest exponent `n_k` is shared by all axes, one variable `z` suffices. This is the point where a common schedule is essential and where the note's single `z` is right.
* Pole comparison at `p_i`. A term has `a_i` factors of axis `i`, `s_i` of them new, and `σ` new factors on other axes. Its pole depth is at most `a_iE_{k−1}+s_iΔ_k−(k−1)σ`, because the integer coefficient adds a nonnegative valuation, `U_{j,k−1}` (`j≠i`) is integral and `V_{j,k}` has valuation `≥k−1`. Since `s_i≤min(a_i,ℓ)≤t`, the cases are exhaustive and each loses a quantity tending to infinity relative to `qE_{k−1}+tΔ_k`:
  - `a_i<q`: loses `≥E_{k−1}`.
  - `a_i=q`, `s_i<t`: loses `≥Δ_k`.
  - `a_i=q`, `s_i=t`, `σ≥1`: loses `≥k−1`.
  - `a_i=q`, `s_i=t`, `σ=0`: this is the grouped term `binom(q,t)U_{i,k−1}^{q−t}V_{i,k}^t f(U_{−i,k−1})`.
  The monomials with `a_i=q` are exactly `X_i^q f(X_{−i})`, so the grouped term is the whole of the last case. Its valuation is `−(qE_{k−1}+tΔ_k)+g+v_p(binom(q,t))` with `g=v_p(f(θ))`, because `f(U_{−i,k−1})≡f(θ) (mod p_i^{k−1})`. The ultrametric inequality then gives the exact pole. Taking `k` beyond `g+max_t v_p(binom(q,t))` and large enough for all three losses makes the bound uniform in the finitely many `t`.
* Windows have total length `O_r(Σ_{a≤k}(n_{a−1}+1))=o(n_k)`, also at a cutoff inside a window.

**Application of the Phase 18 criterion.** With `c=∏p_i` (coprime to `b`):
1. The coefficient `a_m` is a sum of at most polylog-many products of weights `≤1` with integer multipliers, so `|a_m|≤C(m+1)^A`, and `I(N)=O((log N)^r)`.
2. `R_n=b^n·prefix` has denominator dividing `∏p_i^{rE_k}` (the `b`-parts cancel since all exponents are `≤n`). This is `≤n^{O(1)}` and divides a power of `c`.
3. `q_n≥p_i^{D}` where `D` is the exact pole, and `D→∞` off the windows. So `#{n<N: q_n<M}=o(N)` for each `M`.
The kernel estimate `SmoothOrbitEstimate b c` is stated and proved for every `c>1` coprime to `b`, not only prime powers, so the composite support `∏p_i` is covered. The rational dilation is Wall's theorem (multiplication of a normal number by a nonzero rational preserves normality). A relation `P(X)=0` or `P(X)=const` would make a nonconstant polynomial constant, contradicting normality, so the `X_i` are algebraically independent.

**Liouville.** `|X_j−U_{j,k}| ≤ Σ_{l>k}b^{−n_l} ≤ 2b^{−n_{k+1}}` and all prefixes and limits lie in `[0,1]^m`, so the error is `O_P(b^{−n_{k+1}})`. The denominator is at most `D_P·(b^{n_k}∏p_i^{E_k})^r ≤ b^{2rn_k}` for large `k`. Hence `error ≤ den^{−n_{k+1}/(2rn_k)}` with exponent `→∞`. Reducing the fraction only helps.

## Numerical check

I built the construction exactly with Python fractions, with `b=2`, primes `{3,5}` through `k=8` and `{3,5,7}` through `k=7`, random `θ_{ij}` mod `p^{40}`, the schedule above, and `C` the least admissible constant. I verified the weight bounds and the congruences `U_{j,k}≡θ_{ij} (mod p_i^k)`. For nine polynomials (`X1±X2`, `X1X2`, `X1²−X2`, `X1X2−3X2²+X1`, `2X1²X2+X1³−5`, `X1X2X3`, `X1+X2+X3`, `X1²X2−X3²+7X1X3`) and every occurring variable, I computed the exact `p_i`-adic valuation of the true prefix of `P(X)` at one cutoff per support interval in shells `k=4,…,K−1`, and compared it with `qE_{k−1}+tΔ_k−g−v_p(binom(q,t))` outside the windows. Zero mismatches in about 700 cutoffs. This tests the pole formula, including the choice of `t=min(q,⌊n/n_k⌋)`, but is of course asymptotic only in spirit. It tests neither the criterion nor the Liouville estimate.

## Objections (presentation and scope, none affects correctness)

**O1. The Liouville paragraph is not a proof as written.** "The log ratio of successive insertion positions … is governed by `n_{k+1}/n_k→∞`" does not state the inequality. Replace by: for large `k` the reduced denominator `q_k` of `P(U_k)` satisfies `q_k≤b^{2rn_k}`, the error lies in `(0,2‖∇P‖b^{−n_{k+1}}]`, hence error `<q_k^{−ω}` once `n_{k+1}/n_k>2rω+`const; the error is nonzero by irrationality, and the `q_k` are unbounded since distinct nonzero errors tend to `0` while `x` is irrational. State that Liouville is invariant under nonzero rational dilation, in addition to normality.

**O2. The criterion application is compressed into one sentence ("The growing pole off a density-zero set now gives all-prefix normality").** The reader has to guess which of the three hypotheses each fact serves. I recommend one line each: coefficient bound and `I(N)=O((log N)^r)`; `c=∏p_i` and `q_n≪n^D` for a constant `D` depending on `r`, `C` and the primes; and `q_n≥p_i^{D_k(n)}` for hypothesis 3. Also say that the kernel estimate is for arbitrary `c` coprime to `b` (verified in `SmoothOrbit.lean`), since the previous families used `c=p`.

**O3. Notation.** `θ_{ij}` is the target for axis `j` at the prime `p_i` (a limit of `U_{j,k}` in `ℤ_{p_i}`). This is only deducible from the congruence. `U_{−i,k−1}` and `θ_{i,−i}` are undefined, and the note should say that `θ_{ij}` for different `i` are unrelated (no cross-prime independence is needed, because each `P` uses one prime). Also state that the theorem is for the closed family `{n_k: n_{k+1}/n_k→∞}` and that the threshold `k_0` depends on `P` through `g`, which is computable from the computable `θ`, while the series does not.

**O4. Algebraic independence versus rational combinations.** Two different notions appear and the note should separate them. The `p_i`-adic algebraic independence of the tuple `θ_{i,·}` is an *input* and is used only through `f(θ)≠0` for the coefficient polynomial `f` of one chosen variable. It is sufficient, not shown necessary. The real algebraic independence of `X_1,…,X_m` is an *output* of normality. No hypothesis of real `ℚ`-linear independence of constants is needed, unlike the `γ_a` of [nonlinear.md](../nonlinear.md#3-several-generators-with-separated-pole-growth), and rational linear combinations `Σ c_iX_i` are covered by the degree-one case (each is normal, so `1,X_1,…,X_m` are `ℚ`-linearly independent). A reader might expect the real constants to matter because earlier generators were separated by `γ`-rates; here the separation is by prime.

**O5 (minor).** The remark that the original mixed Stoneham product lacks the cross-prime congruences is accurate. Since the criterion places no cross-prime hypothesis on `q_n`, a one-line note that the congruences are used only to control the pole at one prime when several variables interact would make the contrast precise.

Nothing is left unchecked in the claims of the note beyond the criterion and kernel estimate, which I took from Phase 18 and the verified Lean statement.
