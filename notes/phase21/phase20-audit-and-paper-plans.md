# Phase 21 Tracks F1–F2: Phase 20 audit closure, Paper XI blueprint and novelty review, Paper VII v2.0 plan

Audit date: 25 November 2026. Worktree branch `research/phase-21-radix-boundaries`, starting from Phase 20 commit `be4a160`. **Read-only audit.** This note and `site-and-alphaxiv-audit.md` are the only files written. No shared file (`docs/registry/GF.toml`, `NormalityChecker/EulerPentagonal.lean`, `scripts/*`, `papers/*`), release or tag was touched. Where a shared file needs a change, the exact replacement text is given in §1.6 for the coordinator.

Nothing here claims peer review. Cross-model review is not independent human peer review. A failed search is recorded only as a failed search and never as evidence of novelty. Evidence labels follow [literature.md](../phase20/literature.md): **[R]** read in the primary text today, **[A]** abstract or bibliographic record only, **[S]** stated by a secondary source I read, **[M]** my own deduction, **[U]** unverified.

## 0. Summary of verdicts

| Item | Verdict | What must change |
| --- | --- | --- |
| **GF-05** | The mathematics I re-derived is consistent. The scope text is too brief on radix and on what is Lean. | State "base 2 only"; say that for odd radices only an upper bound exists; say which parts are written proofs; delete the unproved "(and powers of 2)" in the note. §1.1 |
| **GF-06** | **Overstated.** The statement lists "a matching lower bound" and bundles five extensions with different hypotheses; the scope never says the lower bound is a proof outline. | Replace statement and scope; extend `inputs`. §1.2 |
| **GF-10** | Registry scope is accurate for what it names. Two Lean docstrings overclaim ("every prime"; "feeding directly"). `shifted_prefix_aux_prime_dvd_den` covers only the newest prime. | Reword scope; fix two docstrings. §1.3 |
| **GF-11** | All three Major findings (`C3-M1`, `C3-M2`, `C3-M3`) and all minor items are integrated. Residual: review-status wording, internal "brief" language, no re-review of the repaired text. | Reword scope; strip process language before any manuscript. §1.4 |
| **EulerPentagonal.lean** | The file defines **series**, never the product or its cube. Euler's and Jacobi's identities are not formalized, the signs are never used, nothing about `E_b²` exists, and the sharp √(2/3) upper bound is not instantiated in Lean. Three docstring errors. | Replacement docstrings, registry wording for GF-03 and GF-04, optional sign lemmas. §1.5 |
| **Paper XI** | Blueprint and novelty ledger in §2. | Gate rule for Phase 21 material in §2.3. |
| **Paper VII v2.0** | Plan in §3: new directory, new release tag, never edit `papers/07-synthetic-expansions/`. | Re-review GF-11 before it enters a manuscript. |

## 1. F1: Phase 20 audit closure

### 1.1 GF-05: the exact leading constant for multiplicative Lambert series

Files read in full: `docs/registry/GF.toml` (lines 73–89), [lambert-leading-constant.md](../phase20/lambert-leading-constant.md), the Lean files named by the entry.

**Re-derived and consistent.**

- $L_{\chi_4}=\sum c(n)2^{-n}$ with $c=r_2/4$, and $\Theta_3(1/2)^2=1+4L_{\chi_4}$.
- $\rho\log_2(1/\rho)$ with $\rho\sim K/\sqrt{\log N}$ equals $\frac{K}{2\ln 2}\frac{\log\log N}{\sqrt{\log N}}(1+o(1))$. The upper and lower bounds in §§2–3 carry the same leading term; the parameters $R,H_V,H,\zeta,\Delta^+,\eta,\lambda_\eta$ are mutually consistent ($\lambda_\eta=\log_2(1/\rho)-O(\log\log\log N)$ and $\zeta+\Delta\le\rho+\Delta^+<\eta$).
- $C_\chi$: from $F(s)^2=\zeta(s)L(s,\chi)\prod_{\chi(p)=-1}(1-p^{-2s})^{-1}\prod_{p\mid q}(1-p^{-s})^{-1}$ I recomputed the residue and the factor $\Gamma(1/2)^2=\pi$. This gives $C_\chi=\bigl(\tfrac{L(1,\chi)}{\pi}\prod\cdots\bigr)^{1/2}$, and for $\chi_4$ it reduces to $K=\tfrac1{\sqrt2}\prod_{p\equiv3\,(4)}(1-p^{-2})^{-1/2}$.
- Uniform pair sieve (E3). A prime $q\equiv3\ (4)$ with $q\nmid h$ divides exactly one of $n,n+h$, so for both in the sum-of-two-squares set $q^2$ divides it. The residual sieve has $\omega(q)=2$, $|R_d|\le\omega(d)$, dimension $\kappa=2\cdot\tfrac12=1$, sifting range $(z_0,z]$ with $z_0=(\log x)^2$, $z=\sqrt x$, and the hypotheses of Halberstam–Richert Theorem 2.2. The bound is uniform in $|h|\le H=O(\log\log N)$: discarding the primes $q\mid h$ costs at most $(1-2/z_0)^{-\log_2 x}\to1$. The sum over $|h|\le H$ is $O(x(\log\log x)^2/\log x)=o(x/\sqrt{\log x})$.
- (E1) uses $2^{V(n)}\le c(n)$ and Gauss; (E5) uses $A(t)=2^{-R}A(t+R)$ and the mean tail $\ll N/(\log N)^{3/2}$. Both check.
- Shiu's theorem applies to $f=U\cdot\mathbf 1_{c>0}$: $f(p^e)\le e+1$, $f(p)=1$ if $\chi(p)=1$ and $0$ if $\chi(p)=-1$, so $\sum f(p)/p=\tfrac12\log\log x$ and $\sum_{n\le x}U(n)\ll x/\sqrt{\log x}$.

**Findings.**

1. **(Scope, must fix) "base 2 (and powers of 2)" is unproved.** [lambert-leading-constant.md §6](../phase20/lambert-leading-constant.md) says the constant is specific to base 2 "and powers of 2". Every proof in §§2–3 is written for $b=2$ (displacement $t(n)=n-V(n)$ with $V=v_2$; Lemma 3.1; (G1)–(G5)). For $b=2^k$, $k\ge2$, the displacement is $\lfloor V/k\rfloor$ and the odd-part residue changes, so $K/(2\ln b)$ is a conjecture. Registry and manuscript must say "base 2" only. The registry statement already does.
2. **(Scope, must fix) odd radices.** Only the upper bound $O_b((\log\log N)/\sqrt{\log N})$ is established, from Corollary 2 and Theorem 7 of [theta-and-modular.md](../phase20/theta-and-modular.md). No lower bound of that order exists in any odd radix for $L_\chi$ (CC-48 is binary) and none for $\Theta_Q$ except the outline in §1.2. The heuristic factor $1+\ln2$ for $m^2+n^2$ in base 3 is a heuristic, not a theorem, and the sentence "typical digit widths grow like $\frac12\log_b(2)\log\log m$" is a typical-size statement, not a bound on $1-D_N$.
3. **(Precision) Section 3 uses a count that Section 2 does not state.** The lower bound needs "at least $1-\Delta^+$ of the points lie within $\zeta=\rho$ of 0". That is the far-count bound $F(\rho)/N\le\rho(\log_2(1/\rho)+O(1))$ from the proof of Theorem 2.2 (Markov at $\varepsilon=\rho$ plus the shadow term), not the discrepancy bound. State it as a displayed inequality in Section 2 and in the manuscript.
4. **(Scope) which parts are Lean.** Lean has the sharp translation identity (for each fixed $N>0$), the composite-radix displaced factorization and Lemma 3.3. The displaced-width transfer (Theorem 2.2), Lemma 3.1, (E1)–(E5), the Landau/Wirsing/Selberg–Delange counts and the final asymptotic are written proofs. The registry says this only implicitly.
5. **(Hygiene) process language.** "critical check of Track B4" (line 26) and "as noted in the B4 brief" (line 119) must not reach a manuscript.
6. **(Caution) "General Phase 17 class" paragraph (§4).** It is a sketch ("the changes to the proof are…"): a pair sieve of dimension $2\kappa$, a Rankin/Shiu bound for $2^{V}\mathbf 1_{c>0}$, and the assumption $S(N)\gg N/(\log N)^\kappa$. It must not be advertised as a theorem in the registry or in Paper XI beyond a remark.
7. **(Honesty of numerics, already stated)** ratio $1.483$ at $N=2^{18}$ against a proven relative error $O(\log\log\log N/\log\log N)$. Keep the sentence "These are finite measurements, not evidence for the constant".

### 1.2 GF-06: theta values and weight-one modular forms

Files read: `GF.toml` lines 91–106, [theta-and-modular.md](../phase20/theta-and-modular.md), [euler-product.md](../phase20/euler-product.md) §8.

**Re-checked and sound.** Lemma 1 (finite coefficient transfer) and Corollary 2; Lemma 3 (lattice points); the anisotropy argument for the upper bound in Lemma 4; Theorem 5; the Eisenstein computation ($\omega(-1)=-1$, so $\omega$ has even order $m$, and $\sigma(p^{2e+1})=0$ where $\omega(p)=-1$); the support bound $x/(\log x)^{\alpha_f}$ by Halberstam–Richert for the multiplicative indicator; $|a_f(n)|\le C_f\tau(n)$ giving $A_f\ll X\log X$.

**Findings.**

1. **Overstatement (must fix).** The statement says $1-D_N\ll(\log\log N)/\sqrt{\log N}$ "(and a matching lower bound)". The matching lower bound is Proposition 6, which the note itself labels "paper proof outline". It needs (a) a pair-sieve bound $\#\{j\le N:r_Q(j)r_Q(j+h)>0\}\ll_hN/\log N$ with polynomial dependence on $h$, and (b) a multiplicative majorant $r^*$ for $r_Q$ with Shiu's theorem for $\sum r^*(j)^\lambda$. For (a) the only written source is Lemma 9.5 of Bailey–Borwein–Crandall–Pomerance and it covers $m^2+n^2$ only. For (b), the class-summed representation number is cleanly multiplicative (a divisor sum $\sum_{d\mid j}\chi_D(d)$) for fundamental discriminants; for non-fundamental $\Delta_0$ the conductor primes need a separate argument **[M]**. So the lower bound is rigorous only for $Q=m^2+n^2$ in base 2 (GF-05) and an outline otherwise. For weight-one forms the matching lower bound is the note's own open problem 3.
2. **Hypotheses conflated.** The sentence "extending to imprimitive forms, shifted lattices, congruence subsums, bounded weights, and degree-≤ 2 polynomials in unary quadratic-polynomial series" merges extensions with different hypotheses:
   - *shifted lattices*: **integral** linear terms $l_1,l_2,l_0$ only (§2.2.1);
   - *rational translates*: not $\Theta_Q(1/b)$ but the congruence subsum $\sum_{x\equiv(r,s)\,(D)}b^{-Q(x)}$ of the scaled series (§2.2.2);
   - *bounded weights*: integer-valued $\chi$ with $|\chi|\le B$. Harmonic polynomial weights of degree $\nu\ge1$ give cusp forms of weight $1+\nu$ with $A(X)\asymp X^{1+\nu/2}$ and the method fails (§2.2.3);
   - *degree ≤ 2 polynomials*: Theorem 9 of euler-product.md §8, for finitely many unary quadratic series with $\mathbb Z[1/b]$ coefficients. Degree 3 is not covered ($\Theta_3(1/b)^3$ has support of density $5/6$). Rates differ: linear terms $O(\log N/\sqrt N)$, products $O(\log\log N/\sqrt{\log N})$.
3. **Weight-one hypotheses.** The theorem needs *all* coefficients $a(n)$, **including $a(0)$**, in $\mathbb Z$. For rational $f$ with denominator $d$ only $d\,f(1/b)\in K_b$ follows, and $f(1/b)$ itself falls to the Phase 19 residue test. The exponent is $\alpha_f=\min$ over constituents of (trace-zero Frobenius density for newforms, $1/m$ for Eisenstein constituents), so it can be as small as $1/4$ (types $A_4$, $A_5$). "covering … exotic $A_4/S_4/A_5$" is non-vacuous only through integer-coefficient combinations such as the trace form over the Hecke field of an exotic newform (its coefficients are algebraic integers by Deligne–Serre, so the rational trace is an integer) **[M]**; say so.
4. **"Failure at weight ≥ 2" is a statement about the method.** Lemma 1 is vacuous for $r\in\{4,6,8,10,14,26\}$. No distributional claim about $E_b^r$ follows, and numerically $E_2^r$ looks equidistributed (conjectured normal, unproved). Add this to the scope so the sentence is not read as non-membership.
5. **`inputs` incomplete.** Add Halberstam–Richert's mean-value bound and Shiu (1980) for multiplicative functions, the Brun/Selberg pair sieve, Diamond–Shurman Theorems 4.8.1 and 5.8.3 for the basis of $M_1(\Gamma_1(M))$, effective Chebotarev for the splitting field, and Bailey–Borwein–Crandall–Pomerance Lemma 9.5. Bernays (1912) is needed only for the lower-bound outline; the upper bound is elementary.
6. **Lean scope.** Lean has only the generic transfer, which gives $K_b$ membership once $S(X)=o(X)$ and $A(X)\le CX$ are supplied. The rate comes from Corollary 2 (paper). The registry says "Lean verifies the linear-mass sparse coefficient transfer theorem underlying the $\Theta_Q$ case"; add that Corollary 2 (logarithmic mass, rates) is not in Lean, and that $A_f(X)\ll X\log X$ for weight-one forms is *not* $O(X)$ for Eisenstein constituents with $m\ge4$, which is why `finite_sparse_logmass_transfer` (still unformalized) would be needed.

### 1.3 GF-10: all-prime polynomial normality and `ProtectedPole.lean`

Files read: `GF.toml` lines 149–166, [all-prime-polynomials.md](../phase20/all-prime-polynomials.md), `NormalityChecker/ProtectedPole.lean` (statements and docstrings; the 538 lines contain no `sorry`).

| Lean declaration | Exact content | GF-10 / note claim | Gap |
| --- | --- | --- | --- |
| `shifted_prefix_aux_prime_dvd_den` | Hypotheses: $\ell_k$ prime, $\ell_k\nmid b$, $\ell_k\nmid p$, $\ell_k\nmid\ell_j$ for $1\le j<k$, $n_j\le N$ for $j\le k$. Conclusion: $\ell_k\mid\operatorname{den}(b^NU_k)$ for the single truncation $U_k$. | "auxiliary-prime survival of $\ell_k$" | Covers the **newest** prime at its own truncation only. Persistence of $\ell_i$, $i<k$, inside $U_{k'}$ for $k'>k$, simultaneous divisibility by $\ell_1\cdots\ell_k$, and the exact formula $\operatorname{den}=p^{k^2}\ell_1\cdots\ell_k$ are written proofs ([all-prime-polynomials.md §3](../phase20/all-prime-polynomials.md)). |
| `shifted_prefix_protected_prime_pow_dvd_den` | $p$ prime, $p\nmid b$, $p\nmid\ell_j$, $e_j<e_k$ for $j<k$, $n_j\le N$. Conclusion: $p^{e_k}\mid\operatorname{den}$ and $p^{e_k+1}\nmid\operatorname{den}$. | "exact $p$-adic valuation of shifted prefixes of $W$" | Accurate. It is for $W$ ($r=1$) only, and $p$ need not be odd in Lean. |
| `truncated_poly_pole_dvd_den` | $U=u/(p^{e_1}Q_1)$, $V=v/(p^{e_2}Q_2)$, $p\nmid uvQ_1Q_2$; $a_r\ne0$; $1\le l\le r$; $g=v_p(\lvert a_r\rvert\binom rl)<e_1$ and $<e_2-e_1$. Conclusion: $p^{le_2+(r-l)e_1-g}\mid\operatorname{den}(F_l(U,V))$. | "truncated-polynomial protected-pole lower bound" | It is a statement about the rational expression $F_l(U,V)$, not about the reduced denominator of the shifted prefix of $P(W)$. The bridge $b^{-n}R_n=F_l(U_{k-1},V_k)$, the window rule and the representation of $U_{k-1}$ with exact $p$-depth $(k-1)^2$ are written. It is a lower bound only; that suffices because the grid size $p^{\max(0,e-w)}$ is nondecreasing in $e=v_p(q_n)$. |
| `SurvivingGrid.stride_order` | Phase 19 grid core | "Phase 19 surviving-grid core" | none |

**Findings.**

1. Docstring lines 16–17 of `ProtectedPole.lean` say that "the reduced denominators of the shifted prefixes of $W$ eventually contain every prime coprime to $b$" as a consequence of `shifted_prefix_aux_prime_dvd_den`. The theorem proves less (the newest prime at its truncation). The note's statement is true for $W$ and is a written proof. Fix the docstring (§1.6).
2. Docstring lines 31–32 say the pole depth is "feeding directly into `SurvivingGrid.stride_order` and `PrimePowerGrid.crt_period_count`". Directly is too strong; the window combinatorics and Taylor identity lie between. Reword.
3. The registry scope should itemize the four Lean items as above and say which are **not** Lean. The all-prime persistence is a statement about $W$ (degree 1). For $P(W)$ with $r\ge2$ only $p$ and, when $l=r$, the newest prime $\ell_k$ are controlled. The note says this ("no persistence is claimed for them in $P(W)$ when $r\ge2$"); the registry should too.
4. Rate constants re-derived: the window and early-shell term gives $\exp(-3(\ln2)^{1/3}(\ln N)^{2/3})$ and the mesh term $p^{-r(K-2)^2}$ gives $\exp(-r\ln p\,(\ln2)^{-2/3}(\ln N)^{2/3})$, matching $c<\min\bigl(3(\ln2)^{1/3},\,r\ln p/(\ln2)^{2/3}\bigr)$ with $r=\deg P$.
5. **Literature positioning needed for Paper VII v2.0 (new).** Manai, *Transcendence Meets Normality: Construction of Transcendentally Normal Numbers*, arXiv:2508.09319 [A: abstract via arXiv API], constructs explicit numbers $x$ with $p(x)$ (absolutely) normal for every non-constant integer-valued polynomial $p$. The theorem $P(W)$ normal for every rational polynomial in a fixed base $b$, with $W$ Liouville, is different (one base, all rational polynomials, Liouville, rate $\exp(-c(\log N)^{2/3})$), but a reader will ask. Cite and compare; I did not read the theorem.

### 1.4 GF-11: higher-degree polynomial normality on power schedules

Files read: [cubic-power-schedule.md](../phase20/cubic-power-schedule.md) in full and [track-c-review.md](../phase20/reviews/track-c-review.md).

**Integration of the repairs (checked against the current text).**

| Finding | Where it is now | Result |
| --- | --- | --- |
| `C3-M1` ($B=0$ coincidences) | §5, paragraph "Rows with $B=0$": rational separation $|x-z|\ge p^{-\max(v,v')}\ge p^{-H-\lfloor e_r/s\rfloor}$ forces $x=z$, hence $v'=v$ and $k'=k+(H'-H)\le k+\lfloor e_r/s\rfloor$; the peeling step uses $k'_j<2h_j$ for large $H$; the exponent $k-(\tfrac12-\epsilon'd)h_j$ is displayed. | Integrated. |
| `C3-M2` (all $r$, all $\beta\le1$) | §5, "Choosing $q$": exponents $E_1/H,E_2/H$, windows for $q=4,\dots,r+1$, the three regimes, and $\sigma_r=1/(r(2^{r+1}-2))$. | Integrated. I recomputed every displayed value: $E_1/H=1-\frac{1}{42}$ at $(q,\alpha)=(4,\tfrac13)$; $E_2/H=1-\frac1{28}$ at $(4,1)$; the window endpoints $\frac1{(q-1)(2K_q-2)}$ and $\frac{2-4/K_q}{(q-2)(2K_q-2)}$; the $\alpha$-coefficients in regime 3; $1-E_2/H=\frac{3-4/K_{r+1}}{r(2^{r+1}-2)}$; $\sigma_3,\dots,\sigma_7=\tfrac1{42},\tfrac1{120},\tfrac1{310},\tfrac1{756},\tfrac1{1778}$. |
| `C3-M3` (analytic gaps) | §5: drop $p\nmid m'$ at cost $p/(p-1)$; Titchmarsh 5.13 on pieces of length $\le pT$, $T=p^{v'}\ge1$; harmonic sums $L^{1/(2K_q-2)}$ and $O_q(1)$; disjoint pieces give $O(H^{r-3}p^H)$; the box-packing lattice-count proof. | Integrated. |
| minor `C3-m1`–`C3-m6` | §4 "Assume $r\ge3$"; $\kappa<1/2$ and distinct centres; $\lfloor(L-1)/s\rfloor$; "for a fixed pair of loss tuples"; $\kappa<1/(2r)$ and $x^d+B\in[\tfrac14,p^d+1]$; `scripts/phase20_normality.py` now scans `range(4, r + 2)` (line 573) and no longer contains the `1200` grid. | Integrated. |

**Residual items.**

1. **Review status wording.** The scope says the proof was "audited by an independent cross-provider review with all three major findings … repaired". The repaired text has had no second review; [verification.md](../phase20/verification.md) says only that the script asserts $\sigma_r$ for $r=3,\dots,8$. Say "reviewed once; repairs integrated by the author and not re-reviewed; no human specialist has read it". I verified exponent algebra and the logic of Lemma 2, not the whole analytic estimate.
2. **Process language** in the note: "as the brief predicted" (§7, first bullet) and the heading "Corrections to the proposed strategy"; in all-prime-polynomials.md "every case raised in the brief" and the table "Checklist for the proposed proof" ("Stronger than the brief"). Remove before a manuscript.
3. **Status.** Keep `paper` and consider `principal = false` until a re-review. Do not claim the boundary $d=r$ (for example cubes on $tk^3$), mixed orders $X_a=C(b,p,a,d)$, or any rate.
4. **Consequences stated in GF-11 check out.** Non-algebraicity of degree $<d$ follows because $P(C)=0$ cannot be normal; joint uniform distribution of $(C,\dots,C^{d-1})$ follows from Weyl and normality of every nonzero $\sum h_jC^j$ (degree $\le d-1=r$ is allowed).
5. Paper VII v1.0 Question 1 asks "Is $\xi^3$ normal?" for the cubic schedule $d=3$. That is $d=r$, still open. GF-11 answers it only for $d\ge4$ (for example $C(2,3,1,4)$). Update the question, do not claim it solved.

### 1.5 The formalization boundary in `EulerPentagonal.lean`

**What the file defines** (the names are `eulerPentagonalSum` and `eulerCubeSum`, not `eulerPentagonal` and `eulerCube`):

- `pentCoeff : ℕ → ℤ`: `1` at `0`; `(-1)^h.choose` if `h : ∃ k ≥ 1, pentMinus k = m ∨ pentPlus k = m`; else `0`.
- `eulerPentagonalSum b := coeffSeries b pentCoeff = ∑' m, (pentCoeff m : ℝ) / b^m`. This is the **series**, by definition.
- `jacobiCubeCoeff`, `eulerCubeSum b := coeffSeries b jacobiCubeCoeff`: the **triangular series** $\sum_{k\ge0}(-1)^k(2k+1)b^{-k(k+1)/2}$.

**What it proves.** $|\mathtt{pentCoeff}|\le1$; $\mathtt{absMass}\le M$; $\mathtt{supportCount}\le2(\lfloor\sqrt{2M}\rfloor+1)$; $D_N\to1$ and translation preservation for the pentagonal series; $|\mathtt{jacobiCubeCoeff}(T_k)|=2k+1$, support $\le\lfloor\sqrt{2M}\rfloor$, mass $\le4M$, $D_N\to1$ and preservation for the triangular series; the finite gap bound `eulerPentagonal_finite_gap_upper`; and `cauchyConv_absMass_le`.

**What it does not prove.**

1. $\mathtt{eulerPentagonalSum}\,b=\prod_{k\ge1}(1-b^{-k})$ (Euler), and $\mathtt{eulerCubeSum}\,b=(\prod(1-b^{-k}))^3$ (Jacobi). Both are external, classical identities.
2. The signs. `pentCoeff (pentMinus k) = (-1)^k` is never proved, although `pentMinus_strictMono`, `pentPlus_strictMono` and `pentMinus_ne_pentPlus` make it immediate. No proof uses the signs: every Lean theorem holds for **any** coefficients with the same support and $|a|\le1$ (resp. $|a(T_k)|=2k+1$).
3. Anything about $E_b^2$. The only relevant declaration is the generic `cauchyConv_absMass_le`; there is no support count, no $K_b$ statement, and no definition of the square.
4. Digit formulas, word frequencies, non-disjunctivity, disjunctivity of the cube, and every lower bound.
5. The **sharp** upper constant $\sqrt{2/3}$. [euler-product.md §3 and §9](../phase20/euler-product.md) call the finite inequality $1-D_N(E_b)\le4b^{-w}+wP(N+w)/N$ "kernel-checked". Only the general lemma `Phase18Synthetic.sparse_farCount_le` (hypotheses `StrictMono m` and $|A_k|\le B$) and `discrepancy_deficit_le` are; their instantiation to the pentagonal positions is a paper step. Lean's `eulerPentagonal_finite_gap_upper` has the weaker form $2\varepsilon+2L(\sqrt{2(N+L)}+1)/N+(N+L+2)/(N\varepsilon b^L)$, which has the right order but, with the natural choice $Lpprox\log_bN$, $arepsilonpprox N^{-1/2}$, the leading constant $2\sqrt2$ instead of $\sqrt{2/3}$ (a factor $2\sqrt3$) **[M]**.
6. The worst-translation identity is Lean (`SharpTranslation.sharp_translation_isGreatest`) for each fixed $N>0$, and is correctly attributed; it is not stated in `EulerPentagonal.lean`.

**Docstring defects found (exact list).**

| Line | Problem |
| --- | --- |
| 5–32 | Header calls the series $E_b$ and $E_b^3$ without saying the identification is not proved; lists `pentagonal_absMass_le` (the theorem is `pentCoeff_absMass_le`) and `cauchy_absMass_le` (the theorem is `cauchyConv_absMass_le`); claims `eulerPentagonal_finite_gap_upper` bounds "$1-D_N(E_b;b)$ and $|D_N(x+E_b;b)-D_N(x;b)|$" but it states only the first. |
| 123 | `eulerPentagonalSum` documented as "the pentagonal generating series $E_b=\dots$". |
| 249–250 | "**Maximal discrepancy of Euler's infinite product**": the theorem is about the series. |
| 263–264 | "Universal discrepancy preservation by Euler's infinite product": same. |
| 278 | Section title "Jacobi's cube identity $E_b^3=\dots$". |
| 302 | "Jacobi's cube series $E_b^3=\dots$". |
| 410–411, 421–422 | "Jacobi's cube series $E_b^3$" in two theorem docstrings. |

The replacement text is in §1.6, items L1–L8.

### 1.6 Exact replacement text for the coordinator

None of the following has been applied. Line numbers refer to commit `be4a160`; other Phase 21 edits may have shifted them, so match on the quoted keys. After editing `docs/registry/GF.toml` run `python3 scripts/portal.py build` and then `python3 scripts/portal.py check --strict`; after editing Lean statements run `lake build` and `NORMALITY_UPDATE_THEOREM_INDEX=1 lake env lean scripts/readme_theorems.lean` (AGENTS.md). Identifiers are permanent; only text changes. Registry text uses Unicode and no TeX macros.

**R1. GF-03 `scope` (line 41), replace by:**

```toml
scope = "Convention. Lean's eulerPentagonalSum b is the pentagonal series 1 + Σ_{k ≥ 1} (−1)^k (b^{−k(3k−1)/2} + b^{−k(3k+1)/2}) by definition. Euler's pentagonal number theorem, which identifies it with the product E_b = ∏_{k ≥ 1} (1 − b^{−k}), is classical and is not formalized; the statements about the product follow from that identity. For the series Lean verifies D_N → 1 and D_N(x + ·) − D_N(x) → 0 for every real x and every radix b ≥ 2, the support bound (at most 2(⌊√(2M)⌋ + 1) nonzero coefficients up to M), and an explicit finite upper bound on 1 − D_N with a non-sharp constant. The proofs use only the support and |a(m)| ≤ 1, never the signs. The exact block digit formula, the all-prefix word bounds, non-disjunctivity, the sharp √(2/3) asymptotic (upper bound: the general kernel-checked inequality sparse_farCount_le instantiated on paper; lower bound: written) are written proofs."
```

**R2. GF-04 `scope` (line 60), replace by:**

```toml
scope = "Convention as for GF-03. Lean's eulerCubeSum b is Jacobi's triangular series Σ_{k ≥ 0} (−1)^k (2k + 1) b^{−k(k+1)/2} by definition; Jacobi's identity ∏ (1 − q^m)^3 = Σ (−1)^k (2k + 1) q^{k(k+1)/2}, which identifies it with E_b^3, is classical and not formalized. For this series Lean verifies |a(T_k)| = 2k + 1 at the triangular numbers T_k, the support bound, the linear mass bound A(M) ≤ 4M, D_N → 1 and translation preservation, and, for arbitrary integer sequences, the Cauchy convolution mass bound. Nothing about E_b^2 (coefficients, support or K_b-membership) is formalized. The disjunctivity of E_b^3, the exact √2 constant, the analysis of E_b^2 through η(12τ)^2 (which uses the cited Hecke-eigenform input; its elementary O((log log N)/√(log N)) upper bound needs only a Landau-type count), the degree ≤ 3 polynomial theorem and the rational scalar theorem are written proofs."
```

and in the GF-04 `statement` (line 59) replace "The square E_b^2 corresponds to the weight-one Klein-four CM eigenform η(12τ)^2, giving support count ≍ X/(log X)^{3/4}" by "The coefficients of E_b^2 are the coefficients c(12n + 1) of the weight-one CM eigenform η(12τ)^2 with Klein-four projective image, so its support count is ≍ X/(log X)^{3/4}".

**R3. GF-05 `scope` (line 80), replace by:**

```toml
scope = "Base 2 only. Lean verifies the sharp translation identity (sup over x of |D_N(x + z) − D_N(x)| equals 1 − D_N(z) for each N ≥ 1), the composite-radix displaced-source factorization and the circle-separation lower bound. The displaced-width transfer, the source decomposition, the exceptional-set estimates (including a pair sieve uniform in shifts |h| ≤ O(log log N)) and the asymptotic itself are written proofs that use the external inputs listed here. The relative error is O((log log log N)/(log log N)), so finite computations (ratio ≈ 1.48 at N = 2^18) are not evidence for the constant. In base 2 the 2-adic valuation absorbs the powers of 2 in c(n) = r_2(n)/4, so the residual odd part has bounded mean. In an odd radix such as 3 the powers of 2 are not absorbed and typical digit widths grow like ½ log_b(2) log log m: only the upper bound O_b((log log N)/√(log N)) is established there, no exact constant and no lower bound of that order is claimed, and the factor 1 + log 2 suggested for m^2 + n^2 in base 3 is heuristic. Radices 2^k with k ≥ 2 are not treated."
```

Also in [lambert-leading-constant.md §6](../phase20/lambert-leading-constant.md) delete "(and powers of 2)".

**R4. GF-06 `statement` (line 97) and `scope` (line 98), replace by:**

```toml
statement = "For every positive definite integral binary quadratic form Q and every integer radix b ≥ 2, Θ_Q(1/b) = Σ_{(m,n) ∈ ℤ^2} b^{−Q(m,n)} lies in K_b with 1 − D_N(Θ_Q(1/b); b) ≪_{Q,b} (log log N)/√(log N). The same upper bound holds for imprimitive forms, integral shifted lattices, congruence subsums, integer-valued weights bounded by a constant, finite ℤ[1/b]-combinations, and polynomials of total degree at most 2 in finitely many unary quadratic-polynomial series (degree 3 is out of reach: Θ_3(1/b)^3 has support of density 5/6). A lower bound of the same order is proved for Θ_3(1/2)^2 in base 2 (GF-05) and only outlined for other forms and radices. More generally, every holomorphic weight-one modular form f(q) = Σ_{n ≥ 0} a(n) q^n on Γ_1(M) with all a(n) ∈ ℤ, including a(0), satisfies f(1/b) ∈ K_b with 1 − D_N(f(1/b); b) ≪_{f,b} (log log N)/(log N)^{α_f}, where α_f > 0 is the least density of primes with vanishing coefficient among the newform and Eisenstein constituents of f; this covers dihedral CM, exotic A_4/S_4/A_5 (α_f as small as 1/4) and weight-one Eisenstein constituents. The coefficient-transfer method fails structurally for Serre's lacunary even η-powers η^r (r ∈ {4, 6, 8, 10, 14, 26}); no distributional conclusion is drawn for them."
scope = "Lean verifies only the generic linear-mass sparse coefficient transfer, which gives K_b-membership once S(X) = o(X) and A(X) ≤ CX are supplied. Everything specific to Θ_Q and to modular forms is a written proof: the lattice-point and support counts (the elementary anisotropy argument gives the upper bound that is needed), the logarithmic-mass rate (any A(X) ≪ X (log X)^β), the Deligne–Serre, Chebotarev and Eisenstein lacunarity deductions with A_f(X) ≪ X log X, the shifted-lattice, congruence-subsum, bounded-weight and ℤ[1/b]-combination extensions under the hypotheses stated above, and the degree ≤ 2 polynomial extension. The matching lower bound is a proof outline for general Q and b: it needs a pair-sieve bound uniform in the shift and a multiplicative majorant of the representation numbers, and both are written only for m^2 + n^2. Matching lower bounds for weight-one forms are open. A rational form with denominator d only gives d·f(1/b) ∈ K_b. Only the failure of the method is shown for weight ≥ 2; the distribution of E_b^r for r ≥ 4 is open."
```

and in `inputs` (line 104) append: "Halberstam–Richert mean-value bound and Shiu (1980) for multiplicative functions; Brun/Selberg sieve for pair counts; Diamond–Shurman Theorems 4.8.1 and 5.8.3; effective Chebotarev density theorem; Bailey–Borwein–Crandall–Pomerance (2004), Lemma 9.5."

**R5. GF-10 `scope` (line 156), replace by:**

```toml
scope = "Lean verifies (i) the exact p-adic valuation of the shifted prefixes of W (p^{e_k} divides the reduced denominator of b^N U_k and p^{e_k + 1} does not); (ii) survival of the newest auxiliary prime only (ℓ_k divides that denominator for N ≥ n_k); (iii) the lower bound p^{l e_2 + (r − l) e_1 − g} dividing the denominator of the truncated Taylor expression F_l(U, V) for rational U, V of exact p-adic depths e_1 < e_2; and (iv) the Phase 19 surviving-grid core. Written proofs: persistence of every earlier ℓ_i in later shells and the exact denominator p^{k^2} ℓ_1 ⋯ ℓ_k of the shifted prefixes of W; the window rule and the identity b^{−n} R_n = F_l(U_{k−1}, V_k); the bound log q_n = O(k^2); the prefix discrepancy rate; the Liouville property; and the general C2a–C2c extensions. These were checked by exact scripts and one independent cross-provider review (with the fixed-r versus all-r quantifier in C2b corrected). The all-prime persistence statement is for W (degree 1); for P(W) with r ≥ 2 only p and, when l = r, the newest prime ℓ_k are controlled."
```

**R6. GF-11 `scope` (line 175), replace by:**

```toml
scope = "Extends OP-14 (r = 2, d ≥ 3) to all r ≥ 3 and d ≥ r + 1 without an effective discrepancy rate; the boundary d = r (for example cubes on t k^3) and mixed orders are open. Written proof only, with no Lean content: constant-measure dominant-anchor level-H isolation, reverse Fatou and Lebesgue density, the B = 0 rational-separation and peeling argument, and Titchmarsh's q-th derivative test (orders q = 4, …, r + 1, exact uniform margin σ_r = 1/(r(2^{r+1} − 2))). One independent cross-provider review found three major gaps (rational separation and peeling, the all-r exponent margin, and the lattice-counting and Titchmarsh reduction steps); the author repaired them, the repaired text has not been re-reviewed, and no human specialist has read it. Finite exact checks illustrate the mechanism and do not prove the estimates."
```

**L1–L8. `NormalityChecker/EulerPentagonal.lean` docstrings** (text only; no declaration changes; none compiled here because this worktree has no Lean build):

- **L1.** Replace the module docstring, lines 5–32, by:

```lean
/-! # The pentagonal series, Jacobi's triangular series and a convolution mass bound (Tracks A1 and A2)

**Convention.** Both series are defined directly by their coefficients. No identity between a series and
an infinite product is proved in this file.

* `eulerPentagonalSum b` is the pentagonal series
  `1 + ∑_{k ≥ 1} (-1)^k (b^(-k(3k-1)/2) + b^(-k(3k+1)/2))`. Euler's pentagonal number theorem identifies it
  with `E_b = ∏_{k ≥ 1} (1 - b^(-k))`; that classical identity is not formalized, so the theorems below are
  statements about the series and transfer to the product through Euler's identity.
* `eulerCubeSum b` is Jacobi's triangular series `∑_{k ≥ 0} (-1)^k (2k + 1) b^(-k(k+1)/2)`. Jacobi's identity
  `∏ (1 - q^m)^3 = ∑ (-1)^k (2k + 1) q^(k(k+1)/2)` identifies it with `E_b³`; it is not formalized either.

The proofs use only the support of the coefficients and bounds on their absolute values
(`|pentCoeff m| ≤ 1`, `|jacobiCubeCoeff (triNum k)| = 2k + 1`); the signs are never used. Nothing here concerns
`E_b²`, digits, word frequencies, disjunctivity or lower bounds on the discrepancy.

1. **Pentagonal series.**
   - `pentagonal_supportCount_le`: `supportCount pentCoeff M ≤ 2 * (Nat.sqrt (2 * M) + 1)`.
   - `pentCoeff_absMass_le`: `absMass pentCoeff M ≤ M`.
   - `eulerPentagonal_discrepancy_tendsto_one`: `D_N(eulerPentagonalSum b; b) → 1` for every radix `b ≥ 2`.
   - `eulerPentagonal_preserves_discrepancy`: `D_N(x + eulerPentagonalSum b; b) - D_N(x; b) → 0` for every
     radix `b ≥ 2` and every real `x`.
   - `eulerPentagonal_finite_gap_upper`: an explicit finite upper bound, with a non-sharp constant, on
     `1 - D_N(eulerPentagonalSum b; b)` for every `N ≥ 1`, `L` and `ε > 0`.

2. **Jacobi's triangular series.**
   - `jacobiCube_supportCount_le`: `supportCount jacobiCubeCoeff M ≤ Nat.sqrt (2 * M)`.
   - `jacobiCube_absMass_le`: `absMass jacobiCubeCoeff M ≤ 4 * M`.
   - `eulerCube_discrepancy_tendsto_one` and `eulerCube_preserves_discrepancy`: the same two conclusions
     for `eulerCubeSum b`.

3. **Convolution mass bound (`cauchyConv_absMass_le`).** For integer sequences `a`, `c`,
   `absMass (cauchyConv a c) M ≤ (|a 0| + absMass a M) * (|c 0| + absMass c M)`. If both factors have
   `O(√M)` mass the convolution has linear mass, which is the input to `CoefficientTransfer` for `E_b²` and for
   products of unary quadratic series (Tracks A2 and B5). No theorem in this file applies it to a specific series.
-/
```

- **L2.** Line 123: `/-- The pentagonal series `1 + ∑_{k ≥ 1} (-1)^k (b^(-k(3k-1)/2) + b^(-k(3k+1)/2))`; equal to `E_b = ∏ (1 - b^(-k))` by Euler's pentagonal number theorem, which is not formalized here. -/`
- **L3.** Lines 249–250: `/-- **Maximal discrepancy of the pentagonal series (Track A1).** For every integer radix `b ≥ 2`, `D_N(eulerPentagonalSum b; b) → 1`; by Euler's pentagonal number theorem this is the statement for `∏ (1 - b^(-k))`. -/`
- **L4.** Lines 263–264: `/-- **Universal discrepancy preservation by the pentagonal series (Track A1).** For every integer radix `b ≥ 2` and every real `x`, `D_N(x + eulerPentagonalSum b; b) - D_N(x; b) → 0`. -/`
- **L5.** Line 278: `/-! ### Part 2: Jacobi's triangular series `∑_{k ≥ 0} (-1)^k (2k+1) b^(-k(k+1)/2)`, equal to `E_b³` by Jacobi's identity -/`
- **L6.** Line 302: `/-- Jacobi's triangular series `∑_{k ≥ 0} (-1)^k (2k + 1) b^(-k(k+1)/2)`; equal to `E_b³` by Jacobi's identity, which is not formalized here. -/`
- **L7.** Lines 410–411: `/-- **Maximal discrepancy of Jacobi's triangular series (Track A2).** For every integer radix `b ≥ 2`, `D_N(eulerCubeSum b; b) → 1`. -/` and lines 421–422 likewise with "**Universal discrepancy preservation by Jacobi's triangular series (Track A2).**".
- **L8.** `ProtectedPole.lean` lines 16–17: replace "Hence the reduced denominators of the shifted prefixes of `W` eventually contain every prime coprime to `b`." by "(Only the newest prime `ℓ_k` of the prefix `U_k` is covered; that every earlier `ℓ_i` persists in later prefixes is a written argument.)". Lines 31–32: replace "feeding directly into" by "the arithmetic core for".

**L9 (optional, makes the `pentCoeff` docstring true; untested).** Add after `pentMinus_ne_pentPlus`:

```lean
theorem pentCoeff_zero : pentCoeff 0 = 1
theorem pentCoeff_pentMinus {k : ℕ} (hk : 1 ≤ k) : pentCoeff (pentMinus k) = (-1 : ℤ) ^ k
theorem pentCoeff_pentPlus {k : ℕ} (hk : 1 ≤ k) : pentCoeff (pentPlus k) = (-1 : ℤ) ^ k
```

Proof route: `unfold pentCoeff`, discharge `m ≠ 0` (`pentMinus k ≥ 1` for `k ≥ 1`), take the witness `k`, and let `h.choose_spec` give `j` with `pentMinus j = m ∨ pentPlus j = m`. Then `pentMinus_strictMono.injective` and `pentPlus_strictMono.injective` force `j = k`, and `pentMinus_ne_pentPlus` rules out the mixed case. After adding these, the `pentCoeff` docstring ("`(-1)^k` at `m = pentMinus k` or `pentPlus k`") is a theorem. Euler's identity itself is not in Mathlib as far as I know **[U]**; formalizing it would be a separate project and is not needed for any current claim.

## 2. F2: Paper XI

### 2.1 Blueprint: *Digit Distribution of Arithmetic Generating Functions: Euler Products, Theta Values and Sparse Coefficient Transfer*

Target: one self-contained manuscript in the strict publication contract (`paper.tex`, `references.bib`, `paper.pdf`, `metadata.toml`, `VERIFICATION.md`, `LEDGER.md`, `submission/`) in a **new** directory `papers/11-generating-functions-digits/`, registry ids GF-01 to GF-09, evidence labels exactly as in the other wave-2 papers (Kernel-verified, Lean-supported paper proof, Paper proof, Finite certificate, Conditional, External input). Sources are the Phase 20 notes. Lean files: `CoefficientTransfer.lean`, `EulerPentagonal.lean`, `SharpTranslation.lean`, `CharacterLambertTransfer.lean`.

**Abstract (draft, ≤ 190 words).** We study the base-*b* digits of values of arithmetic generating functions at *q* = 1/*b*. For a series with integer coefficients of linear mass and density-zero support we prove a finite coefficient-to-discrepancy transfer inequality, valid in every integer radix, with sharp constants and a displacement mechanism for composite radices. It places Euler's product *E_b*, its cube, every binary-quadratic-form theta value and every integer-coefficient weight-one modular form in the numerical translation kernel *K_b*. For *E_b* we give the exact digit blocks, all-prefix word frequencies and the sharp deficit √(2/3)(log_b *N*)/√*N*; *E_b*³ is disjunctive with deficit √2 (log_b *N*)/√*N*. In base 2 we obtain the exact leading constant *K*/(2 log 2) for the multiplicative Lambert series of the character χ₄ and for Θ₃(1/2)², where *K* is the Landau–Ramanujan constant. We show where the method stops: weight ≥ 2, dense *q*-series and the partition constant remain open, and *K_b* is closed under neither squaring nor inversion. Lean 4 verifies the transfer core; the arithmetic is written proofs.

**Section plan.**

| § | Content | Statements and proofs | Source notes | Lean / evidence | Do not claim |
| --- | --- | --- | --- | --- | --- |
| 1 | Introduction | Notation ($D_N$, $K_b$, translation identity); main Theorems A–F below; positioning; what is not claimed | [publication-assessment.md](../phase20/publication-assessment.md) §1 | — | no transcendence novelty (Nesterenko, Hamieh–Murty are cited); no normality of any classical constant; no statement on $E_b^r$ ($r\ge4$), $P_b$, $\Theta_3^3$, $\Theta_3^4$, $E_{2,4,6}(1/b)$, $\Delta(1/b)$ |
| 2 | General sparse coefficient transfer; composite-radix displacement | Finite transfer (GF-01) with lookahead bound $L\,S(N+L)/N$ in Lean and the non-lookahead $L(1+S(N-1))$ in text; linear-mass rate with sharp constant 2 (GF-02); $b^{V}U$ factorization and constant 1 under bounded mean of $|U|$; isolated-source law (statement with hypotheses); counterexamples: density-zero support is not enough | [coefficient-transfer.md](../phase20/coefficient-transfer.md) | `CoefficientTransfer.*` (GF-01 list); GF-02 is `paper` | the non-lookahead bound and the rate are paper statements, not Lean |
| 3 | $E_b$, $E_b^3$, $E_b^2$ | Thm 1 digit blocks; Thm 2 word frequencies; Thm 3 deficit $\sqrt{2/3}\log_bN/\sqrt N$; Thm 7 cube (**disjunctive**, deficit $\sqrt2\,\log_bN/\sqrt N$); Thm 6 square (support $\asymp X/(\log X)^{3/4}$); Thms 8–9 polynomials, rational scalars $(a/d)E_b\in K_b\iff a/d\in\mathbb Z[1/b]$; subsection "Series versus product" (§1.5) | [euler-product.md](../phase20/euler-product.md) | `EulerPentagonal.*` for series only; Euler and Jacobi identities are external inputs | do not call the Lean statements statements about the product; $E_b$ is never disjunctive; $E_b$ not simply normal for $b\ge3$ |
| 4 | Isolated-source law; exact constant | Thm 4.1 ($K/(2\log2)$, $C_\chi/(2\log2)$), proof architecture (E1)–(E5), the far-count inequality (§1.1 item 3), $\Theta_3(1/2)^2$, single $\Theta_3(1/2)$; remark on base 2 versus odd radices | [lambert-leading-constant.md](../phase20/lambert-leading-constant.md) | `one_sub_discrepancy_ge_of_bulk_and_far`, `displaced_term_eq`, `sharp_translation_isGreatest` | base 2 only; no $2^k$; no odd-radix constant |
| 5 | Theta values and weight one | Thm 5.1 $\Theta_Q(1/b)\in K_b$; Prop 5.2 lower bound (outline, or prove it for $m^2+n^2$ only); Thm 5.3 weight-one forms; the $\mathbb E|{\rm tr}|$ table; arithmetic nature (irrational by digits; transcendence cited) | [theta-and-modular.md](../phase20/theta-and-modular.md) | transfer core only | no matching lower bound for general $Q$, $b$ or for weight-one forms |
| 6 | Carry windows, dense $q$-series, obstructions, Lambert transfers | $P_b$, $\Theta^3$, $\Theta^4$, $E_{2,4,6}$, Serre's $\eta^{2r}$; the weight-2 overlap footprint; $K_b$ not closed under squaring; sumset criterion; reciprocal criterion; lacunary $z$ with $1-z\in K_2$; residue-class Lambert transfers (GF-07); logarithmic Euler-product Möbius collapse (GF-09, remark) | [dense-and-partitions.md](../phase20/dense-and-partitions.md), [classical-transfers.md](../phase20/classical-transfers.md) | `CharacterLambertTransfer.*` (mod 8) | no distribution claim for any dense object; nothing for $E$, $E_{\rm odd}$ individually |
| 7 | Open problems; verification map; ledger | Problems from the Phase 20 notes; one row per theorem in `VERIFICATION.md`; `LEDGER.md` for priority and literature | [verification.md](../phase20/verification.md), §2.2 below | — | — |

**Main theorems for §1** (statements to be copied from the registry after §1.6 is applied): A = GF-01 + GF-02; B = GF-03; C = GF-04; D = GF-05; E = GF-06; F = GF-08 + GF-07. Paper VI v1.0 (alphaXiv) is cited for the Lambert order result (CC-48), so Theorem D is an upgrade of a cited result, not a double claim.

### 2.2 Fresh primary-source and public-repository review (25 November 2026)

**Method and honesty.** Searches used the harness `WebSearch` tool in *standard* mode; direct reads used `curl`, the arXiv API (`export.arxiv.org`), `ar5iv`, and the GitHub REST API through `gh api` (read-only, public data). No search engine index was claimed to be exhaustive. I did not search MathSciNet, zbMATH, Google Scholar or Crossref in this pass. Every query is listed.

| # | Tool and query (verbatim) | Result | Bearing |
| --- | --- | --- | --- |
| Q1 | WebSearch: `Mira-Cult math github normal numbers notes` | no Mira-Cult hit; generic normal-number pages | none |
| Q2 | WebSearch: `CaptainSude github generalized Lambert disjunctivity nonnormality` | no hit (R `LambertW` packages) | none |
| Q3 | WebSearch: `discrepancy of binary expansion of Lambert series Σ χ(m)/(2^m-1) non-normal digit distribution` | no paper on character-weighted Lambert digit discrepancy; hit arXiv:2605.24160 (see below) | (a) not located |
| Q4 | WebSearch: `q-digamma function value q=1/2 binary expansion normality digits Lambert series` | Wolfram `QPolyGamma`, Berg–Petersen arXiv:1111.0250; no digit statement | (b) not located |
| Q5 | WebSearch: `base-b digits of Euler's pentagonal number product ∏(1-b^{-k}) normal number` | Bell's survey and general normal-number pages; nothing on digits of $E_b$ | (c) not located |
| Q6 | WebSearch: `Bergelson Downarowicz "On preservation of normality and determinism under arithmetic operations"` | arXiv:2506.12929 | (d) |
| Q7 | WebSearch: `Bell "Euler and the pentagonal number theorem" arXiv math/0510054` | arXiv:math/0510054 | (e) |
| Q8 | WebSearch: `Jacobi Fundamenta nova theoriae functionum ellipticarum 1829 Königsberg cube of product identity` | Wikipedia (1829; Borntraeger, Königsberg); Bell (1828 note) | (e) |
| Q9 | WebSearch: `Campbell "binary digits of the Erdős-Borwein constant" 11 occurs infinitely often Crandall problem` | confirms arXiv:2605.24160; MathWorld notes the claim and a separate authorless 2026 claim that every finite binary word occurs (not examined) | context for GF-07 |
| Q10 | WebSearch: `Rauzy "Nombres normaux et processus déterministes" Acta Arithmetica 29 1976 211-225` | IMPAN, EuDML and Numdam records; Manai arXiv:2609.24665 | (d) |
| Q11 | WebSearch: `normal numbers theta function value Θ_3(1/2) binary digits discrepancy sum of two squares 2026 arXiv` | nothing on $\Theta_3$ digits; arXiv:2607.06773 (Becher–Lew Deveali) | (d), radix |
| Q12 | WebSearch: `"Dot" AI mathematics normal numbers discrepancy 2026 research agent Stoneham` | nothing. I could not identify what "Dot" denotes; **no finding is recorded** | — |
| Q13 | WebSearch: `alphaXiv AI track Stoneham numbers normality polynomial images preprint 2026` | nothing relevant (arXiv:2508.09319 appears) | — |
| Q14 | WebSearch: `Hardy Wright Theorem 357 Jacobi (1-x^n)^3 = Σ (-1)^n (2n+1) x^{n(n+1)/2} Jacobi 1829 Fundamenta nova` | a summary of Glaisher (1889) placing the cube identity in *Fundamenta Nova*, p. 185 | (e) **[S]** |
| Q15 | WebSearch: `partition generating function Σ p(n) 2^{-n} binary expansion digits normal number` | nothing on digits of $P_b$ | (c) |
| Q16 | WebSearch: `Dayan Ganguly Weiss normality preserving multiplication rationals probabilistic proof` | arXiv:2609.24665 restating it; DGW's own paper is arXiv:2002.00455 | (d) |
| D1 | arXiv API ids `2605.24160, 2506.12929, math/0510054, 2609.24665, 2607.06773, 2603.04396, 2508.09319` | titles, dates, abstracts, comments, no `journal_ref` for 2506.12929 | **[A]** |
| D2 | `ar5iv` text of arXiv:math/0510054 | dates of Euler's work | **[R]** |
| D3 | `gh api repos/Mira-Cult/math` tree at commit `cf9e57f` (2026-11-25T11:06:36Z): 16,416 files | no file name containing *theta, partition, Lambert, pentagonal, modular-form, q-series, digamma, discrepancy* outside unrelated Bol-loop notes; `notes/number-theory/normal-numbers/` has 24 files (`0001-joint-digit-switches.md`, `0002-erdos-borwein-positive-word-density.md`, `normal-dovetails/`, `stoneham-joint-normality.md`, `erdos-borwein-positive-word-density/`) | **[R]** for the listing |
| D4 | the same 24 files fetched raw and grepped for *pentagonal, theta function, partition function, Euler product, quadratic form, Lambert series, q-series, digamma, Landau, Ramanujan, sum of two squares, modular form* | one relevant hit: "positive Euler product and Mertens" inside `erdos-borwein-positive-word-density/adaptive-marker-count.md` (an Erdős–Borwein density argument); no hit on Euler's $\prod(1-b^{-k})$, theta values or modular forms. The pattern `eta(` (Dedekind eta) matched only substrings of `theta(` and `beta(` in unrelated formulas (checked in `normal-dovetails/EXTENSIONS.md`) | keyword scan only; the notes were not read in full |
| D5 | `gh api users/CaptainSude/repos`: 20 public repositories | related names: `erdos-borwein-disjunctivity`, `erdos-borwein-disjunctivity-elementary`, `generalized-Lambert-disjunctivity-and-nonnormality` ("Lean verified result about the digit distribution of $L_{b,r}$ for $b,r>1$ … $b$-disjunctive and $b$-nonnormal", pushed 2026-09-13), `Stoneham-sum-normal`, `stoneham-prime-support`, `reciprocal-Fermat-constant-Nonnormal`; none concerns theta values, $E_b$, partitions or sums of two squares | **names and descriptions only; contents not read** |

**Findings by question.**

**(a) Base-*b* discrepancy of $L_\chi(b)$, power-of-2 versus other radices.** No source located that states the discrepancy asymptotic, an exact constant, or the radix dependence of $1-D_N(L_\chi;b)$. The closest published items are Bailey–Borwein–Crandall–Pomerance (2004), Thm 9.4 (a one-bit count in base 2, constant $C_0\approx0.7996$ for $\Theta_3(1/2)^2$) [R, from [literature.md](../phase20/literature.md) §3], and the public repository `CaptainSude/generalized-Lambert-disjunctivity-and-nonnormality` whose description concerns $L_{b,r}$ in general base. **Action before any priority statement:** read that repository's statement and compare it with Paper VI (CC-48) and with GF-05. Do not write "no source treats other radices" until then. For Phase 21 (radix boundaries) the comparison between base 2 and odd radices should cite BBCP's separation of the one-bit count from discrepancy and Becher–Lew Deveali (arXiv:2607.06773, July 2026) as context only: it gives the first numbers deterministic in base 2 but normal in every odd base, which concerns normality across radices, not $K_b$.

**(b) $q$-digamma and antisymmetric Lambert series.** Not located (Q4). The Wolfram `QPolyGamma` page gives a Lambert-series representation; that is an identity, not a digit result. No claim.

**(c) Rational scalings of Euler's pentagonal series; digits of $E_b$ and $P_b$.** Not located (Q5, Q15). Classical background that must be cited: multiplication by a nonzero rational preserves normality (Wall 1949, Chang 1976, as quoted in the 2014 Airey–Mance paper and in Manai) **[S, via a search summary]**. That concerns normal $x$; the Phase 20 theorem "$(a/d)E_b\in K_b\iff a/d\in\mathbb Z[1/b]$" concerns non-normal $x$ in $K_b$ and is a different statement. No source located for it.

**(d) Reciprocals and products of deterministic and $K_b$ numbers.** Existing citations stand: Rauzy, *Nombres normaux et processus déterministes*, Acta Arith. **29** (1976), no. 3, 211–225, DOI 10.4064/aa-29-3-211-225 [A: IMPAN and EuDML records seen]; short version Astérisque **24–25** (1975), 263–265 [A]. Bergelson–Downarowicz, arXiv:2506.12929, 15 June 2025, math.DS, 67 pages, 14 figures, no journal reference in the arXiv record [A]. **New to the record:** C. Manai, *On Normality Preserving Operations*, arXiv:2609.24665 (21 September 2026, 24 pages) [A: abstract], which restates the probabilistic proof, revisiting Dayan–Ganguly–Weiss, that the nonzero rationals are exactly the multiplicative normality-preserving numbers in a fixed integer base, and extends Rauzy's additive characterization to absolutely normal numbers. Paper XI §6 (non-closure of $K_b$ under squaring; reciprocal criterion) must cite these and say that its objects are limiting-discrepancy-one numbers, not normality preservers. I did not read the theorems.

**(e) Euler and Jacobi dates and bibliography.** From the ar5iv text of Bell, arXiv:math/0510054v2 (submitted 3 October 2005, revised 17 August 2006, 21 pages) **[R]**:

- the first mention in Euler's correspondence is a letter from Daniel I. Bernoulli to Euler of 28 January 1741; Euler's paper E158, presented 6 April 1741 and published 1751, mentions the theorem;
- Euler gave a proof in a letter to Goldbach of **9 June 1750** (Euler–Goldbach correspondence, letter 144);
- the same proof is given in more detail in E244, *Demonstratio theorematis circa ordinem in summis divisorum observatum*, Novi commentarii academiae scientiarum imperialis Petropolitanae, published **1760**;
- E541, *Evolutio producti infiniti $(1-x)(1-xx)(1-x^3)\cdots$ in seriem simplicem*, presented to the St. Petersburg Academy on 14 August 1775 and published **1783** in the Acta academiae scientiarum imperialis Petropolitanae, pp. 47–55, gives a further proof.

So "1750/1783" in earlier briefs corresponds to the 1750 proof in the letter and the 1783 publication of E541. The manuscripts should cite: communicated proof 1750; published proofs E244 (1760) and E541 (1783). I did not read the originals.

*Jacobi.* *Fundamenta nova theoriae functionum ellipticarum*, Regiomonti (Königsberg), Borntraeger, 1829 (Wikipedia; Cambridge University Press listing for the reprint) **[S]**. The cube identity $\prod(1-q^m)^3=\sum(-1)^n(2n+1)q^{n(n+1)/2}$ is placed in the *Fundamenta nova* at p. 185 by a summary of Glaisher (1889) **[S, one search summary; Glaisher not read]**. Bell, per a search summary, says Jacobi discussed Euler's theorem in an 1828 note *Note sur les fonctions elliptiques* **[S]**. Citations must stay "Jacobi (1829)" with the page marked unverified until the book is read (Gesammelte Werke vol. 1 reprint). The Hardy–Wright theorem number was not confirmed.

**New items worth recording in `LEDGER.md` for Paper XI.**

| Item | Relevance | Label |
| --- | --- | --- |
| J. M. Campbell, *On the binary digits of the Erdős–Borwein constant*, arXiv:2605.24160 (submitted 22 May 2026; "Submitted for publication"; AI assistance disclosed: GPT-5.5 Pro). Abstract: the string 11 occurs infinitely often in the binary expansion of $E=\sum1/(2^n-1)$, resolving a 2012 question of Crandall. | GF-07 and Paper IX concern the same constant. GF-07 claims nothing about $E$, $E_{\rm odd}$ individually; the claim stands, but cite this preprint when mentioning $E$. | [A] |
| V. Becher and S. Lew Deveali, *Normal numbers in sparse Cantor sets*, arXiv:2607.06773 (7 July 2026) | first numbers deterministic in base 2 yet normal in every odd base; context for radix-boundary questions | [A] |
| C. Manai, arXiv:2609.24665 and arXiv:2508.09319 | see (d) and §1.3 item 5 | [A] |
| Public repository `Mira-Cult/math` (commit `cf9e57f`) and `CaptainSude` repositories | existing ledger entries unchanged; scan only | see D3–D5 |

**Classification (cautious).** Digits of $E_b$, $E_b^3$, the exact deficits, $E_b^2$ via $\eta(12\tau)^2$ and the exact constant $K/(2\log2)$: "not located in the sources examined". Landau–Bernays, Serre, Deligne–Serre, Nesterenko, BBCP, Rauzy, Bergelson–Downarowicz: known and must be cited as in §2.1. The check is unfinished for the contents of two public repositories; see the action in (a).

### 2.3 Slot rule for Phase 21 material

I did not receive the Phase 21 track briefs; the track names A1–A4, B1–B4, D1, D4 reached me only as labels. Phase 20 used A for Euler products and theta/modular forms, B for transfer and exact constants, D for dense series and obstructions ([publication-assessment.md](../phase20/publication-assessment.md) §1). If Phase 21 keeps that grouping, the insertion points are: A-tracks to §3 (new subsection after the cube) or §5; B-tracks to §2 (a "radix-dependent refinements" subsection) and §4; D1 and D4 to §6. **This mapping is an assumption for the coordinator to correct.**

A Phase 21 result enters Paper XI only if all of the following hold:

1. **G1.** A registry entry exists with an identifier, evidence label, scope and `proof` path, and passes `portal.py check --strict`.
2. **G2.** The proof has been read independently of its author by a model from a different provider than the author, with every Major finding repaired *and* the repaired text re-read.
3. **G3.** Every finite computation is reproduced by an exact script that exits 0 and is named in `VERIFICATION.md`.
4. **G4.** The literature ledger records the searches (§2.2 format) and states what was not read.
5. **G5.** Statements that rest on a Lean theorem say whether Lean speaks about the series or the product, the object, the radix, and for which $N$.

Material that fails a gate stays in a Phase 21 note and is listed under "open problems" or omitted.

## 3. Paper VII v2.0 revision plan: *Synthetic Arithmetic Expansions and Prescribed Discrepancy*

Constraints. Version 1.0 is published on alphaXiv and sits in `papers/07-synthetic-expansions/`, release `manuscripts-v2.0.0`, with its PDF digest in `papers/SHA256SUMS` and checked by `papers/check_release.py --verify-history`. **Nothing under that directory, that tag, or the recorded digest may change.** Version 2.0 is a new directory, as for `01-stoneham-polynomials-v2`.

**Current v1.0 structure** (`paper.tex`): §1 Introduction; §2 Discrepancy on the circle and orbits of rationals; §3 A worked example: the binary cubic number; §4 Valuation-weighted expansions (the switch, SY-02); §5 Prescribing the discrepancy limit; §6 Lower and upper discrepancies and invariant measures; §7 Quadratic images (OP-14); §8 Infinite sums; §9 Questions; §10 Formal verification; §11 Use of AI tools. Registry ids in `metadata.toml`: SY-01, 02, 03, 06, 07, 11, 13, 16, 19, OP-08, OP-09, OP-14.

| v2.0 component | Material | Placement | Status and conditions |
| --- | --- | --- | --- |
| Theorem on retaining every prime | GF-10: $W=\sum 1/(p^{k^2}\ell_kb^{2^{k^3}})$; every nonconstant $P\in\mathbb Q[x]$ gives $P(W)$ normal and Liouville with rate $\exp(-c(\log N)^{2/3})$; every prime coprime to $b$ divides all shifted prefix denominators of $W$ eventually | New section after §7, building on OP-08 (grid) and OP-09 (all-prime series with rate $O(1/\log N)$, which is for the series itself) | Written proof, one review (ACCEPT with polish, Gemini 4 Neon). Lean: four declarations of §1.3 with the corrected scope. Add the Manai comparison (§1.3 item 5). |
| Protected-pole algebras | C2a–C2c | Same section, as a theorem with the C2b quantifier stated correctly (fixed-$r$ conclusion versus all-$r$ conclusion) | Written, reviewed with one Major fix applied |
| Power schedules below the degree | GF-11: $C(b,p,s,d)$, $r<d$ | Replaces the case "$r=2$, $d\ge3$" in §7 by "all $r<d$", keeping the quadratic proof as the model case | **Paper proof, not re-reviewed.** Gate: a second independent review of the repaired §5 and, ideally, a specialist, before it is stated as a theorem; otherwise move it to a companion note and keep OP-14 in v2.0 |
| Questions (§9) | Q1 ($\xi^3$ normal?), Q2 (transcendence, Liouville) | Rewrite | Q1: for $d=3$ it is the boundary $d=r$ and stays open; GF-11 gives normality of $\xi^3$-type numbers for $d\ge4$. Q2: $C(b,p,s,d)$ is not algebraic of degree $<d$; Liouville is specific to the sparse schedule of GF-10 and is not claimed for dense schedules. Q3 unchanged |
| Metadata | `id = "VII"`, `version = "2.0"`, `supersedes = "papers/07-synthetic-expansions"`, `registry_ids` + GF-10, GF-11, `lean_commit` updated only if the Lean tree changes | New directory `papers/07-synthetic-expansions-v2/` with `paper.tex`, `references.bib`, `paper.pdf`, `metadata.toml`, `CHANGES.md` (table of old §/new §, as for Paper I v2), `VERIFICATION.md`, `LEDGER.md`, `submission/` | Follow `papers/WAVE2-CONTRACT.md` |
| Phase 21 Track C extensions | not known to me | Per the gate in §2.3 | Candidates the Phase 20 notes already name as open: mixed orders $X_a=C(b,p,a,d)$ (cubic note §8), the boundary $d=r$, explicit rates for GF-11 |

**Release and publication steps (owner decisions).** (1) New release tag for the new directory (for example `manuscripts-v2.1.0`; the name is the owner's choice) with `papers/manifest.toml` and `docs/registry/papers.toml` entries; `papers/manifest.toml` marks `07-synthetic-expansions` as superseded only in the release that carries v2. (2) Append, never edit, digests in `papers/SHA256SUMS`. (3) `papers/alphaxiv-records.toml`: append a `versions` entry to record VII after the web-form or API post; `scripts/alphaxiv_publish.py` posts a revision with `new_version_of` and refuses to resubmit a recorded version. (4) **Licence:** on 25 November 2026 the public alphaXiv record of VII still shows the default alphaXiv submission-policy licence while VI, I and X show CC BY 4.0 ([site-and-alphaxiv-audit.md](site-and-alphaxiv-audit.md) §3). The licence is a web-form choice, not an API parameter; choose CC BY 4.0 for the new version and settle the existing record on alphaXiv. (5) Regenerate `docs/results.md` with `portal.py build`.

**Risk register.** (i) GF-11 is the longest and least reviewed argument; a defect would invalidate a headline theorem of a published manuscript's successor. (ii) The page budget: GF-10, C2a–C2c and GF-11 together are about 400 lines of dense text in the notes; split into a companion if v2.0 exceeds the length of v1.0 by more than half. (iii) Every statement of kernel verification must name the Lean declaration and say it is the finite divisibility core, not the prefix estimate, the rate or the Liouville property.
