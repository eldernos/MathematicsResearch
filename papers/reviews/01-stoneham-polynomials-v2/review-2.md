# Independent Referee Report: *Polynomial Images of Stoneham Numbers* (Version 2.0)

- **Reviewer model:** Gemini 4 Argon, Antigravity
- **Date:** 2026-11-25
- **Reviewed commit:** `0a19fe4` (`0a19fe42b85a8d0038f9f17a4c60c0a68423e747`, branch `publication/wave-2`; pinned Lean checkpoint `e4809cf561573aef588e6ffc491a35cdb79fd9ec`)
- **Notice:** AI model review; not independent human peer review.

---

## Verdict

**Accept with minor revisions.**

The manuscript is mathematically sound, clearly structured, and compiles cleanly to an 11-page PDF with no undefined references or citations. All six audit areas pass verification:

1. **Primary sources and bibliography:** Every cited external result (Stoneham 1973, A. N. Korobov 1990, Kano 1993, Kano–Shiokawa 1993, Wagner 1995, N. M. Korobov 1956, Nakai–Shiokawa 1997, Bailey–Crandall 2002, Bailey–Borwein 2012, Bugeaud 2012, Coons 2013/2014, Vandehey 2016/2019, and Mira Cult's September/October 2026 archives) has been checked against its primary source and bibliographic metadata (Crossref, arXiv e-print TeX/PDF, Osaka University OUKA, Keio University KSTS, and Math-Net.ru). Theorem numbers, page numbers, and hypotheses match their uses in the manuscript.
2. **Mira Cult and public overlaps:** Mira Cult's 7 October 2026 working archive (`S08`, Theorem 1.1 and Corollary 1.2, Gist `79be9a5d4aa54a9df41e702c4f3113ea` at revision `41b5a780f79f7bdd275cd96e7e310b000a897d35`) states base-$b$ normality for every nonconstant rational polynomial in $x(b;c,q) = \sum_{k\ge1} q^{-k} b^{-c^k}$ when $q>2$ and some prime $p \mid \gcd(c,q)$ does not divide $b$, together with a power-saving synchronized star-discrepancy bound for $(x,x^2,\ldots,x^m)$. The manuscript credits this overlap prominently in the second sentence of the Abstract (`paper.tex:15-17`), in the Antecedents section (`paper.tex:70-80`), in `LEDGER.md`, `CHANGES.md`, `metadata.toml`, and across all six files in `submission/`, accurately identifying Theorem A as the $q=c$ specialization and Theorem B as its coordinate projection while contrasting the high/low guard-interval decomposition of `S08` with the reflected upper-set inclusion–exclusion proof formalized in Lean.
3. **Lean 4 correspondence:** Every claim bearing the `[Kernel-verified]` label (Theorems A, B, 3.1, 3.2, 4.1, Proposition 2.1, the radix-48 nonnormality of $\alpha_{2,3}^2$, the one-axis unique-leading-monomial sum, the binary square shell profile of $\alpha_{2,3}^2$, and the upper-shell denominator formula $q_k = 2^{\max(0,2k-1-v_2(Z_k))}$ for $X^2-2X$) matches the full mathematical statement and definitions of the cited Lean declaration at commit `e4809cf561573aef588e6ffc491a35cdb79fd9ec`. There is no overstatement.
4. **Scope at parameter two:** The manuscript carefully distinguishes resolved cases at $c=2$ from open problems, explicitly stating in the Abstract (`paper.tex:21-26`), Section 3 (`paper.tex:309-313`), and Section 5 (`paper.tex:551-555`) that normality of the resonant quadratic $\alpha_{b,2}^2 - 2\alpha_{b,2}$ remains open for every fixed odd radix $b\ge 3$ and that nonvanishing of $M_d(t)$ on the whole shell $[1,2)$ remains open for general $d\ge 3$. Proposition 4.2 is properly labelled `[Finite certificate]`, and Theorems 4.3, 6.1, Corollary 4.4, and test (2) are properly labelled `[Lean-supported paper proof]`.
5. **Mathematical soundness:** Independent algebraic and numerical verification of the proofs in Sections 2–6 uncovered no mathematical gaps.
6. **Build verification:** `wsl -d Ubuntu -- bash papers/wsl-build.sh 01-stoneham-polynomials-v2` succeeds cleanly (exit code 0, 11 pages).

No critical or major issues were found. Below is the detailed audit followed by numbered minor and editorial findings.

---

## Task 1: Primary-Source and Bibliography Audit

Every entry in `references.bib` (`lines 1-95`) and every external citation in `paper.tex` was verified against primary records:

| BibTeX key (`references.bib`) | Citation in `paper.tex` | Primary-source verification |
| --- | --- | --- |
| `stoneham` (`lines 1-6`) | `line 58` | R. G. Stoneham, *On absolute $(j,\varepsilon)$-normality in the rational fractions with applications to normal numbers*, Acta Arith. **22** (1973), no. 3, 277–286, `doi:10.4064/aa-22-3-277-286`. Verified via Crossref. Proves base-$b$ normality of $\alpha_{b,c}$ for odd prime $c$ and $b$ a primitive root modulo $c^2$ (including $\alpha_{2,3}$ on pp. 282–284). |
| `korobov` (`lines 8-12`) | `line 59` | A. N. Korobov, *Continued fractions of certain normal numbers*, Math. Notes **47** (1990), no. 2, 128–132 (transl. from Mat. Zametki **47** (1990), no. 2, 28–33), `doi:10.1007/BF01156821`. Verified via Crossref and Kano [3, pp. 909–910, 919]. |
| `kano` (`lines 14-18`) | `line 59` | H. Kano, *General constructions of normal numbers of Korobov type*, Osaka J. Math. **30** (1993), no. 4, 909–919, `doi:10.18910/10356`. Verified directly from the Osaka University institutional repository PDF (`ojm30_04_15.pdf`). Credits Stoneham (Theorem 1, p. 909) and A. N. Korobov (Theorem 1, p. 910) for $\sum a^{-\lambda_n} b^{-\mu_n}$ with $\mu_n \ge a^{\lambda_n}$, and gives the discrepancy estimate (13) on p. 914 and Remark 2 on pp. 914–915. |
| `bc` (`lines 20-24`) | `lines 60, 88-89, 630` | D. H. Bailey and R. E. Crandall, *Random generators and normal numbers*, Exp. Math. **11** (2002), no. 4, 527–546, `doi:10.1080/10586458.2002.10504704`. Verified via Crossref and author PDF (`bcnormal-em.pdf`). Theorem 2.2 spans pp. 529–530, with item (9) on p. 530 giving the Erdős–Turán discrepancy bound $D_N < C(m^{-1} + \sum_{h=1}^m h^{-1} |N^{-1} \sum_{n=0}^{N-1} e^{2\pi i h \alpha_n}|)$ (whose unnormalized form multiplies by the sample count). Theorem 4.8 and the $O(\log^2 N / \sqrt{N})$ rate for $m_i = c^i, n_i = i$ appear on p. 535. Corollary 4.9(i) on p. 536 gives $b$-normality of $\alpha_{b,c}$ for all coprime $b,c > 1$. |
| `wagner` (`lines 26-30`) | `line 63` | G. Wagner, *On rings of numbers which are normal to one base but non-normal to another*, J. Number Theory **54** (1995), no. 2, 211–231, `doi:10.1006/jnth.1995.1114`. Verified via Crossref and Kano [3, p. 910]. |
| `ks` (`lines 32-37`) | `lines 63-65` | H. Kano and I. Shiokawa, *Rings of normal and nonnormal numbers*, Israel J. Math. **84** (1993), no. 3, 403–416, `doi:10.1007/BF02760950`; institutional preprint KSTS/RR-91/006 (`91006.pdf`). Verified via Crossref and the Keio preprint PDF. Conditions (15)–(16) in the preprint require $\lambda_n / \mu_{n-1} \to \infty$ and $(\log \mu_n)/\lambda_n \to \infty$; for $\lambda_j = j, \mu_j = c^j$, these ratios are $j/c^{j-1} \to 0$ and $\log c$, confirming `paper.tex:63-65`. (See Finding 1 on labelling the preprint equation numbers in `paper.tex:63`.) |
| `vandehey` (`lines 39-44`) | `lines 81, 190-191, 600-618` | J. Vandehey, *Differencing methods for Korobov-type exponential sums*, J. Anal. Math. **138** (2019), no. 1, 405–439, `doi:10.1007/s11854-019-0038-2`; `arXiv:1606.07911`. Verified via Crossref and the `arXiv:1606.07911v1` TeX source and PDF. In the preprint, Corollary 1.2 (p. 2) is the short-orbit power-saving bound for $N \ge m^\epsilon$; Proposition 4.1 (p. 8) and equation (12) (p. 10) define the auxiliary divisor $m'$ in the iterative step; Theorem 5.1 (pp. 13–14) gives the all-length recursive bound $\le (A_k m^{\alpha_k} N^{\gamma_k} + B_k m^{-\alpha_k} N^{\nu_k})(1+\log m)^{2^{-k}}$ with $\alpha_k = (2^{k+2}-2)^{-1}$, $\gamma_0 = 0, \nu_0 = 1$, and the exact recurrences used on `paper.tex:605-608, 645-648`. The support-restriction remark on `paper.tex:610-618` accurately repairs equation (12) of the preprint when $q = Q/\gcd(h,Q)$ drops a prime factor from the ambient support. |
| `bb` (`lines 46-50`) | `lines 82-83` | D. H. Bailey and J. M. Borwein, *Nonnormality of Stoneham constants*, Ramanujan J. **29** (2012), no. 1–3, 409–422, `doi:10.1007/s11139-012-9417-3`. Verified via Crossref and author PDF (`nonnormality.pdf`). Theorem 2 (p. 414 / PDF p. 8) proves $B$-nonnormality of $\alpha_{b,c}$ in bases $B = b^p c^q r$ under $D < 1$ (with Example 1 listing base 48 for $\alpha_{2,3}$). |
| `coons` (`lines 52-57`) | `line 53` | M. Coons, *An arithmetical excursion via Stoneham numbers*, J. Aust. Math. Soc. **96** (2014), no. 3, 303–315, `doi:10.1017/S1446788713000682`; `arXiv:1212.3449v2` (28 Nov 2013), Appendix A. Verified via Crossref and the `arXiv:1212.3449v2` TeX source and PDF. Appendix A (pp. 10–11) contains Theorem A.1 (Nishioka 1985), Theorem A.2 (Mahler), and Corollary A.3 (p. 11), proving transcendence of $\alpha_{b,c}$ for all integers $b,c \ge 2$. |
| `jointkorobov` (`lines 59-64`) | `line 68` | N. M. Korobov, *On completely uniform distribution and conjunctly normal numbers*, Izv. Akad. Nauk SSSR Ser. Mat. **20** (1956), no. 5, 649–660 (`https://www.mathnet.ru/eng/im3836`). Metadata verified. |
| `mira` (`lines 67-73`) | `lines 79-80` | Mira Cult (`Mira-acc`), *Normality research*, working research archive v1.0, 23 September 2026 (`17:18:05Z`), Gist `ea2791119de611279237096e35cbc976` at revision `d699a69c2037ee4420bfb8e1e0ad0b310bbc8eb0`. Verified directly via GitHub Gist API: `S07` treats the generalized single series $\sum_{j\ge1} D^{-j} B^{-C^j}$ and `S09` treats smooth-support series and joint normality of $L_{p,s}(b) = \sum_{j\ge0} p^{-sj} b^{-p^j}$ across distinct pairs $(p,s)$. |
| `ns` (`lines 75-80`) | `lines 66-67` | Y. Nakai and I. Shiokawa, *Normality of numbers generated by the values of polynomials at primes*, Acta Arith. **81** (1997), no. 4, 345–356, `doi:10.4064/aa-81-4-345-356`. Verified via Crossref. |
| `bugeaud` (`lines 81-85`) | `lines 61, 88-89` | Y. Bugeaud, *Distribution Modulo One and Diophantine Approximation*, Cambridge Tracts in Mathematics **193**, Cambridge University Press, 2012, `doi:10.1017/CBO9781139017732`. Verified via Crossref. Section 5.1 ("Korobov's and Stoneham's normal numbers") surveys the radix-orbit discrepancy of $\alpha_{b,c}$. |
| `mira2` (`lines 86-90`) | `lines 15, 70-78` | Mira Cult (`Mira-acc`), *Normality research #2*, public working notes, 7 October 2026 (`16:31:31Z`), Gist `79be9a5d4aa54a9df41e702c4f3113ea` at revision `41b5a780f79f7bdd275cd96e7e310b000a897d35`. Verified directly via GitHub Gist API (`S08`, `sources/notes/stoneham_polynomial_normality.tex`). |
| `archive` (`lines 91-95`) | `lines 216, 228` | *Polynomial images of Stoneham numbers with an odd prime-power parameter*, version 1.1 (2026), pinned to `e4809cf561573aef588e6ffc491a35cdb79fd9ec/papers/01-stoneham-polynomials`. Verified in repository tree: Theorem 2 (`papers/01-stoneham-polynomials/paper.tex:75`) and Theorem 7 (`papers/01-stoneham-polynomials/paper.tex:340`) match the citations on `paper.tex:216, 228`. |

---

## Task 2: Mira Cult and Other Public Overlaps

1. **Inspection of Mira Cult's 7 October 2026 Gist (`79be9a5d4aa54a9df41e702c4f3113ea/41b5a780f79f7bdd275cd96e7e310b000a897d35`):**
   - Note `S08` (*Polynomial normality and cyclotomic rank criteria for Stoneham-type values*, lines 11591–12376 of `gistfile1.txt`, synthesized in Program Result P01 on lines 89–103 and 616–741) proves:
     - **Theorem 1.1:** For integers $b,c,q \ge 2$ with $q > 2$ and a prime $p$ satisfying $p \mid c$, $p \mid q$, $p \nmid b$, every nonconstant $P \in \Q[T]$ has $P(x(b;c,q))$ normal in base $b$ where $x(b;c,q) = \sum_{k\ge1} q^{-k} b^{-c^k}$, and for each fixed $m$ the synchronized vector $(x,x^2,\ldots,x^m)$ satisfies an effective power-saving discrepancy bound $D_N^*(x,x^2,\ldots,x^m) \le C N^{-\kappa}$.
     - **Corollary 1.2:** Specializing to $q=c \ge 3$ with $\gcd(b,c)=1$ gives joint base-$b$ normality of $(\alpha_{b,c},\alpha_{b,c}^2,\ldots,\alpha_{b,c}^m)$ and base-$b$ normality of every nonconstant rational polynomial in $\alpha_{b,c}$ (explicitly naming $\alpha_{2,3}^2$ and $\alpha_{2,3}^3 - 7\alpha_{2,3} + 1$).
     - **Corollary 1.3:** Under Theorem 1.1, $(P_1(x),\ldots,P_d(x))$ is jointly base-$b$ normal if and only if the classes of $P_1,\ldots,P_d$ in $\Q[T]/\Q$ are $\Q$-linearly independent.
     - **Boundary at $q=2$:** `S08` (`lines 656, 11699-11701`) explicitly states that $q>2$ is required by its nonintegrality lemma because the algebraic tail $C_t$ can be integral at $q=2$, and claims no polynomial normality result at $q=2$.
2. **Inspection of other Mira Cult and Captain Sude artifacts:**
   - Mira Cult's 23 September 2026 Gist (`ea2791119de611279237096e35cbc976/d699a69c2037ee4420bfb8e1e0ad0b310bbc8eb0`, Notes `S07`, `S09`, `S19`) and 24 November 2026 repository note (`Mira-Cult/math`, `357d26a23f`, `stoneham-joint-normality.md`) treat linear combinations and joint normality of $L_{p,s}(b)$ across distinct $(p,s)$, smooth-support series $\Theta_{b,S,s}$, and the three-parameter single series $S_{B,C,D}$; the 24 November note explicitly remarks (`Scope and references`, bullet 2) that its Theorem 1 controls linear projections and makes no nonlinear polynomial claim.
   - Captain Sude's September 2026 repositories (`Stoneham-sum-normal` at `f4d3d1f0`, `xi-family` at `f0f99121`, `stoneham-prime-support` at `5919ad4e`) treat two-generator sums $\alpha_{b,c}+\alpha_{b,d}$, localized $\xi$-families, and prime-support criteria for single Stoneham series.
3. **Broader literature search:**
   - Searches across equivalent formulations (`"polynomial in a Stoneham number normal"`, `"normality of P(alpha_{b,c})"`, `"algebraic functions of normal numbers Stoneham"`, `"Korobov numbers polynomial"`, normal-number rings) identify Kano–Shiokawa (1993) and Wagner (1995) for specially separated lacunary generator rings, Davenport–Erdős (1952) and Nakai–Shiokawa (1997) for digit concatenations of polynomial values, and Rauzy (1976) / Bergelson–Downarowicz (2025, `arXiv:2506.12929`) for deterministic additive/multiplicative operations. None of the published literature examined establishes polynomial normality for the classical Stoneham series $\alpha_{b,c}$, nor does any prior source treat the dyadic parameter $c=2$ (Sections 3–5).
4. **Assessment of credit in the manuscript:**
   - The credit to Mira Cult's 7 October 2026 notes is accurate, prominent (featured in the second sentence of the Abstract on `paper.tex:15-17`, detailed in `paper.tex:70-80`, and repeated in `metadata.toml`, `LEDGER.md`, `CHANGES.md`, and all `submission/` files), and fair in delineating what is prior in `S08` (the $c>2$ polynomial and joint-power theorems and qualitative power saving via nonintegrality of the periodic cyclotomic tail) versus what is new here (the complete Lean 4 kernel formalization of the $q=c>2$ theorems via reflected upper-set inclusion–exclusion, the explicit scalar discrepancy exponents $\delta_d = \frac{1}{2(2^{d+1}-2)}$ from Vandehey's Theorem 5.1, and the entire $c=2$ theory in Sections 3–5). See Finding 2 for a minor suggestion to also cite `S08, Cor. 1.3` in `paper.tex`.

---

## Task 3: Lean 4 Correspondence Audit

All fourteen `\lean{File}{line}{label}` links in `paper.tex`, all four `\repo{path}{label}` links, all links in `VERIFICATION.md`, and `check.lean` were audited against `git show e4809cf561573aef588e6ffc491a35cdb79fd9ec:<path>`:

| Manuscript claim & label | Cited Lean declaration at `e4809cf` | Statement & definition match |
| --- | --- | --- |
| **Theorem A** (`paper.tex:37-40, 50`) `[Kernel-verified]` | `PeriodicPolynomialNormal.lean:145` (`coprime_polynomial_normal`) and `:166` (`coprime_polynomial_statement_checked`); `StonehamStatements.lean:31` (`CoprimePolynomialNormality`) | **Exact match.** Proves `∀ {b c : ℕ}, 2 ≤ b → 2 < c → b.Coprime c → ∀ P : ℚ[X], 0 < P.natDegree → NormalIn b (P.eval₂ (algebraMap ℚ ℝ) (stoneham b c))`. `stoneham b c` sums $1/(c^{j+1} b^{c^{j+1}})$ over $j \in \N$ (i.e. $j \ge 1$), and `check.lean:12` verifies `stoneham = alpha := rfl`. |
| **Theorem B** (`paper.tex:41-51`) `[Kernel-verified]` | `PeriodicPolynomialNormal.lean:170` (`coprime_joint_powers`) | **Exact match.** Takes `2 ≤ b`, `2 < c`, `b.Coprime c`, `r : Fin d → ℕ` with `∀ i, 0 < r i` and `Function.Injective r`, and $0 \le u_i \le v_i \le 1$, proving `rectangleFrequency` of `fun n i => shift b (alpha b c ^ r i) n` tends to $\prod_i (v_i - u_i)$. |
| **Base-48 nonnormality of $\alpha_{2,3}^2$** (`paper.tex:83-86`) `[Kernel-verified]` | `AlternateBaseStoneham.lean:385` (`square_nonnormal_48`) | **Exact match.** Proves `¬NormalIn 48 (alpha 2 3 ^ 2)`. |
| **Proposition 2.1** (`paper.tex:126-130, 152`) `[Kernel-verified]` | `PeriodicPolynomialMass.lean:174` (`periodic_upper_mass_nonzero`) and `:28` (`periodicGeometricValue_not_isIntegral`) | **Exact match.** For a number field $K$, complete normed field $E$ (taking $E = \Q_p$ where $p \mid c \implies \|c\|_p < 1$), embedding $\varphi : K \to+* E$, $c > 2$, $h > 0$, $h$-periodic root-of-unity sequence $u : \N \to K$, and nonempty upper set $U \subseteq \N^d$, proves the truncated box masses converge in $E$ to a nonzero limit $z \ne 0$. |
| **Fixed-support short-orbit estimate** (`paper.tex:186-187`) (supporting step inside Proof of Theorem A) | `SmoothOrbit.lean:207` (`fixed_support_orbit_estimate`) | **Exact match.** Proves `SmoothOrbitEstimate b c` for $1 < b, 1 < c, \gcd(b,c)=1$. |
| **One-axis unique-leading-monomial sum** (`paper.tex:213-217`) `[Kernel-verified]` | `StonehamPolynomial.lean:107` (`same_prime_sum_normal`) | **Exact match.** Proves `NormalIn b` for any rational linear combination of products $\prod_i \alpha_{b^{m_i}, p^{e_i}}$ ($p \ge 3$ prime, $p \nmid b$, $m_i, e_i \ge 1$) with a unique nonzero leading monomial of positive degree strictly exceeding all other degrees. |
| **Binary square shell profile for $\alpha_{2,3}^2$** (`paper.tex:223-226`) `[Kernel-verified]` | `StonehamSquare.lean:251` (`exact_profile`) | **Exact match.** Proves for $3^{k+4} \le n < 3^{k+5}$ (i.e. shell index $\ge 4$) that `(pre n).den` has 3-adic exponents $2(k+4)-2, 2(k+4)-3, 2(k+4)-1, 2(k+4)$ on the four intervals cut by $3^{k+4}+3^{k+2}$, $3^{k+4}+3^{k+3}$, and $2\cdot 3^{k+4}$. |
| **Theorem 3.1** (`paper.tex:236-247, 259, 262`) `[Kernel-verified]` | `ParameterTwoSquare.lean:20` (`square_normal`) and `ParameterTwoSquareProfile.lean:155` (`exact_profile`) | **Exact match.** `ExactDenominatorProfile` (`ParameterTwoSquareProfile.lean:38-44`) states that for all $b \ge 3$ odd, `(pre b n).den = 1` for $n < 4$, and on $2^k \le n < 2^{k+1}$ ($k \ge 2$), `(pre b n).den` equals $2^{2k-2}$ if $n < 3\cdot 2^{k-1}$ and $2^{k-1}$ otherwise; `SquareNormality` (`:46-47`) states `NormalIn b (alpha b 2 ^ 2)` for all odd $b \ge 3$. |
| **Theorem 3.2** (`paper.tex:265-271, 285`) `[Kernel-verified]` | `ParameterTwoQuadraticOrbits.lean:16` (`normal_iff_upper_denominator`) | **Exact match.** For $b \ge 3$ odd, $D > 0$, $A \ne 0$, proves `NormalIn b (value b A B C₀ / D) ↔ Tendsto (fun j : ℕ => («prefix» b (3*2^j) A B C₀).den) atTop atTop` (with $j = k-1$). |
| **Exact denominator for $X^2-2X$** (`paper.tex:305-308`) `[Kernel-verified]` | `Phase16StonehamBounds.lean:126` (`quadratic_upper_den_eq_quadZ`) | **Exact match.** Proves for $b \ge 3$ odd and $3\cdot 2^j \le n < 2^{j+2}$ that `(prefix b n 1 (-2) C₀).den = max 1 (2^(2*j+1) * ‖quadZ b j‖₂)`, which equals $2^{\max(0, 2k-1-v_2(Z_k))}$ with $k = j+1$. |
| **Theorem 4.1** (`paper.tex:345-359`) `[Kernel-verified]` | `StonehamOddDegree.lean:63` (`odd_prime_power_degree_polynomial_normal`), `DyadicQuartic.lean:109` (`quartic_polynomial_normal`), `DyadicMassCells.lean:151` (`quartic_grid_profile`) | **Exact match.** `odd_prime_power_degree_polynomial_normal` covers all $P \in \Q[X]$ of degree $q^r$ for odd prime $q > 2$ and $r \in \N$ (including $r=0$, degree $1$), and `quartic_polynomial_normal` covers degree $4$, for every odd $b \ge 3$. |
| **Supporting Lean declarations for `[Finite certificate]` and `[Lean-supported paper proof]` claims** | `Phase17DiscrepancyBounds.lean:563, 579` (`descent31Check_true`, `descent31_all_words_nonzero`), `:311` (`jointUniform_of_echelon_degrees`), `DyadicQuartic.lean:80` (`binary_polynomial_normal_of_retention`), `QuantitativeCompositeDenominators.lean:52`, `QuantitativeStonehamTail.lean:104`, `QuantitativeStonehamGaps.lean:86`, `QuantitativeStonehamSupport.lean:49`, `QuantitativeStonehamExponents.lean:12`, `QuantitativeStonehamDiscrepancy.lean:237` | **Accurately scoped.** In every partial formalization, both `paper.tex` and `VERIFICATION.md` state precisely which step is kernel-checked and which step is a finite script computation, paper transfer, or external analytic hypothesis. |

---

## Tasks 4, 5, and 6: Parameter-Two Scope, Mathematical Soundness, and Build

- **Parameter-two scope (Task 4):** Confirmed. Neither the Abstract nor Sections 3–5 claim that all degrees or all quadratics at $c=2$ are resolved. The resonant quadratic $\alpha_{b,2}^2 - 2\alpha_{b,2}$ (`paper.tex:25-26, 309-310`) and whole-shell nonvanishing of $M_d(t)$ for arbitrary $d \ge 3$ (`paper.tex:553-554`) are explicitly flagged as open problems. Proposition 4.2 carries `[Finite certificate]` (`paper.tex:366`).
- **Mathematical soundness (Task 5):** All proofs were checked step by step, supported by independent exact rational Python verification of:
  - the $c=35, b=2$ periodic mass $S = \omega/36$ at $p=5$ and cut mass $S^2 - \omega^2 = 1295/1296$ with $v_5(1295) = 1$ (`paper.tex:205-210`);
  - the two-piece denominator profile of $\alpha_{b,2}^2$ (`paper.tex:236-263`), the upper-half congruence (2) for general quadratics (`paper.tex:288-304`), the recurrence $Z_1 = 2-2b^2$, $Z_{k+1} = 2+2b^{2^k}(Z_k-1)$ for $X^2-2X$, and the value $R_2(12) - 2R_1(12) = 7315/4 - 2(249399/8) = -60521$ at $b=3$ (`paper.tex:305-312`);
  - the topological closure/well-ordering argument for cuts of $d$ powers of two approached from below (`paper.tex:333-344`), the digit-automaton recurrence (`paper.tex:387-389`), and the cyclic-descent congruence $M_{ep^r}(t) \equiv M_e(t/p^r) \equiv 2^{ej} M_e(y) \pmod p$ (`paper.tex:437-450`);
  - the slack decomposition $\Phi(c) - G = \sum_{D\ge0} [\min(d-N_D, 2^{D+1}-1-N_D) - S_D] \ge 0$ and the uniqueness of the one ($j=0$) or two ($j>0$) minimizing orbits in Theorem 5.1 (`paper.tex:492-550`);
  - the piece-length moment bound (3), the reduced-frequency divisor sum $\sum_{h\le H} \gcd(h,Q)^{a_k}/h \le (1+\log H)\prod_{p\mid cD_0}(1-p^{a_k-1})^{-1}$, and Vandehey's recursive exponents $(a_k, \gamma_k, \nu_k, s_k, t_k)$ yielding $\delta_d = \frac{1}{2(2^{d+1}-2)}$ and the refined bounds $O(N^{-1/2}L_N^2)$, $O(N^{-1/6}L_N^{3/2})$, $O(N^{-1/14}L_N^{5/4})$ in degrees $1,2,3$ (`paper.tex:560-663`).
- **Compilation (Task 6):** Running `wsl -d Ubuntu -- bash papers/wsl-build.sh 01-stoneham-polynomials-v2` succeeds with exit code 0, producing `papers/01-stoneham-polynomials-v2/paper.pdf` (11 pages, 409,623 bytes) with no undefined references or citations and only one `amsmath` warning on line 387 (Finding 6).

---

## Numbered Findings

### Critical

None.

### Major

None.

### Minor

1. **Specify preprint equation numbering in the citation of Kano–Shiokawa [6]**
   - **Severity:** Minor
   - **Location:** `paper.tex:63`
   - **Problem:** `paper.tex:63` writes `"The hypotheses (15)--(16) of \cite{ks} require two growth ratios to diverge."` Unlike `paper.tex:53` (`\cite[preprint, Cor.~A.3]{coons}`) and `paper.tex:600-601` (`"Vandehey's preprint Theorem~5.1, pp.~13--14 \cite{vandehey}"`), this citation does not mention in the main text that `(15)--(16)` is the equation numbering of the linked Keio University institutional preprint (`KSTS/RR-91/006`, pp. 5–6, Theorems 4–5), as documented in `LEDGER.md:10`.
   - **Concrete fix:** Change `\cite{ks}` on `paper.tex:63` to `\cite[Theorems~4--5; preprint, (15)--(16)]{ks}`.

2. **Cite `S08`, Corollary 1.3 of Mira Cult [12] for $c>2$ polynomial-vector independence**
   - **Severity:** Minor
   - **Location:** `paper.tex:70-79` and `paper.tex:453-461`
   - **Problem:** In Mira Cult's 7 October 2026 archive (`S08`), Corollary 1.3 states that under Theorem 1.1 ($q>2$), a vector $(P_1(x),\ldots,P_d(x))$ of rational polynomial values is jointly normal in base $b$ if and only if the classes of $P_1,\ldots,P_d$ in $\Q[T]/\Q$ are linearly independent over $\Q$ (noted in `LEDGER.md:13, 112`). `paper.tex:70` cites only `S08, Thm.~1.1 and Cor.~1.2`, and Corollary 4.4 (`paper.tex:453-461`) states the echelon-pivot criterion at $c=2$ without noting that for $c>2$ the full linear-independence equivalence modulo constants holds immediately by applying Theorem A to each nontrivial integer combination. In addition, up to reversing the periodic index order ($u_j = \eta_{t+T-j}$), the one-dimensional sum $S = (\sum_{j=0}^{h-1} c^j u_j)/(1-c^h)$ in Proposition 2.1 (`paper.tex:132`) is identical to $-C_t$ of `S08` Eq. (3) at $q=c$.
   - **Concrete fix:** On `paper.tex:70`, cite `\cite[S08, Thm.~1.1 and Cors.~1.2--1.3]{mira2}`, and add a clause on `paper.tex:74-75` (or before Corollary 4.4) noting that for $c>2$, linear independence in $\Q[X]/\Q$ is necessary and sufficient for joint normality of polynomial images.

3. **State the local-unit precision threshold $1+a(k-v_i) \ge L$ at its first use in Congruence (1)**
   - **Severity:** Minor
   - **Location:** `paper.tex:113, 118-124` (cf. `paper.tex:670`)
   - **Problem:** To justify Congruence (1) modulo $p^L$, `paper.tex:122-124` states: `"Indeed, with |v|=\sum_i v_i, all terms of a|v|\ge L vanish at this precision. On the remaining finite set the indices k-v_i are positive and in the periodic range once k is sufficiently large."` Applying $b^{-c^j} \equiv \omega^{c^j} \pmod{p^{1+aj}}$ (`line 113`) at $j = k-v_i$ modulo $p^L$ also requires $1 + a(k-v_i) \ge L$ (i.e. $k - v_i \ge \lceil (L-1)/a \rceil$) for all retained $v$ with $a|v| \le L-1$, a condition that is stated explicitly only later on `paper.tex:670`.
   - **Concrete fix:** On `paper.tex:123-124`, write: `"On the remaining finite set the indices $k-v_i$ are positive, lie in the periodic range, and satisfy $1+a(k-v_i)\ge L$ once $k$ is sufficiently large."`

4. **Note how the four grid cells in `DyadicMassCells.lean:151` combine into the three quartic valuation intervals**
   - **Severity:** Minor
   - **Location:** `paper.tex:353-356`
   - **Problem:** In the proof of Theorem 4.1, `paper.tex:353-356` links `\lean{DyadicMassCells}{151}{finite grid calculation}` (`quartic_grid_profile`) and states that after removing $2^4$, the 2-adic valuation loss is `"8,7,8 on [1,3/2),[3/2,7/4),[7/4,2), respectively."` In `DyadicMassCells.lean:151-154`, the shell $2048 \le q < 4096$ ($t = q/2048 \in [1,2)$) is split into *four* subintervals at $3072, 3328, 3584$ with residues $4096, 2048, 6144, 4096 \pmod{2^{13}}$; the two middle subintervals $[3/2, 13/8)$ and $[13/8, 7/4)$ have residues $2^{11}$ and $3\cdot 2^{11}$, which share the same 2-adic valuation $11 = 4+7$.
   - **Concrete fix:** Add a parenthetical explanation on `paper.tex:355-356`: `"it is $8,7,8$ on $[1,3/2),[3/2,7/4),[7/4,2)$, respectively (the middle interval combining the two grid cells $[3/2,13/8)$ and $[13/8,7/4)$ with residues $2^{11}$ and $3\cdot2^{11}\bmod2^{13}$)."`

5. **Distinguish "pivot" from "pivot degree" and make the exclusion of degree $0$ explicit in Corollary 4.4**
   - **Severity:** Minor
   - **Location:** `paper.tex:454-465`
   - **Problem:** Corollary 4.4 defines `"distinct leading degrees (the pivot degrees)"` (`line 455`), then writes `"Assume each pivot belongs to Theorem 4.1 or 4.3, or is 2"` (`line 456`). In the proof (`line 464`), `"If the degree is two, no lower pivot exists"` relies on the fact that degree $0$ is not among the degrees covered by Theorem 4.1 ($p^r \ge 1$) or Theorem 4.3 ($d \ge 3$). Using `"pivot degree"` consistently and noting that all allowed pivot degrees are positive makes the degree-2 step in the proof immediate.
   - **Concrete fix:** On `paper.tex:455-457`, write: `"Assume each pivot degree belongs to Theorem~\ref{special} or \ref{degrees} (so every pivot degree is positive), or is $2$. If $2$ is a pivot degree, assume there is no pivot of degree $1$ and that the quadratic basis element..."`

### Editorial

6. **Replace TeX primitive `{a\choose m}` with `\binom{a}{m}`**
   - **Severity:** Editorial
   - **Location:** `paper.tex:387`
   - **Problem:** `{a\choose m}` triggers an `amsmath` warning during compilation (`Package amsmath Warning: Foreign command \atopwithdelims; \frac or \genfrac should be used instead on input line 387`).
   - **Concrete fix:** Replace `{a\choose m}` with `\binom{a}{m}` on `paper.tex:387`.

7. **Format the DOI in `references.bib` entry `ns` consistently with `\nolinkurl`**
   - **Severity:** Editorial
   - **Location:** `references.bib:79`
   - **Problem:** Entry `ns` (Nakai–Shiokawa 1997) uses `\href{https://doi.org/10.4064/aa-81-4-345-356}{doi:10.4064/aa-81-4-345-356}` without `\nolinkurl`, whereas all other DOI entries in `references.bib` use `doi:\nolinkurl{...}`.
   - **Concrete fix:** Change `references.bib:79` to `note={\href{https://doi.org/10.4064/aa-81-4-345-356}{doi:\nolinkurl{10.4064/aa-81-4-345-356}}}`.

8. **Separate adjacent citations on `paper.tex:89`**
   - **Severity:** Editorial
   - **Location:** `paper.tex:89`
   - **Problem:** `\cite[p.~535]{bc}\cite[\S5.1]{bugeaud}` compiles to `[3, p. 535][5, §5.1]` with no separator.
   - **Concrete fix:** Change to `\cite[p.~535]{bc}, \cite[\S5.1]{bugeaud}`.
