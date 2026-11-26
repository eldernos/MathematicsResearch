# Phase 20 Track F4: Publication Assessment

Assessment date: 25 November 2026. This document assesses the publication potential of the Phase 20 research results, distinguishes what warrants a new standalone manuscript from what belongs in future revisions of existing preprints, and records the readiness requirements before any submission or release. **No new manuscript is drafted, released, or submitted here, and no archived release (`manuscripts-v1.0.0`, `manuscripts-v1.1.0`, `manuscripts-v2.0.0`) is modified.**

Nothing in this assessment claims peer review or journal acceptance. Independent cross-provider AI referee audits are internal quality checks, not external peer review.

---

## 1. Candidate New Manuscript Assessment

**Proposed title:** *Digit Distribution of Arithmetic Generating Functions: Euler Products, Theta Values and Sparse Coefficient Transfer*

### Core thesis and mathematical coherence

Phase 20 produced a unified, self-contained mathematical story around one central mechanism — **finite coefficient-to-discrepancy transfer** — and its arithmetic applications across Euler products, theta series, modular forms, multiplicative Lambert series, and classical residue-class transfers:

1. **General sparse coefficient transfer (Track B1–B3, kernel-verified core in `NormalityChecker/CoefficientTransfer.lean`):**
   - Sharp finite all-prefix bound $1 - D_N(F_b(a); b) = \sup_x |D_N(x+F;b)-D_N(x;b)| \le 2\varepsilon + L(1+S(N-1))/N + \widehat A(N+L)/((b-1)b^L \varepsilon N)$ for arbitrary signed integer sequences and arbitrary prime or composite radices $b \ge 2$.
   - Linear-mass rate $1 - D_N(F) \le \rho_N(2\log_b(1/\rho_N) + \log_b^+(4C/(b-1)) + 3)$ with sharp constant $2$ (attained by alternating-digit periodic blocks), proving $A(X) = O(X), S(X) = o(X) \implies F_b(a) \in K_b$.
   - Composite-radix displaced-source factorization $a(m) = b^{V(m)} U(m)$ reducing the leading constant from $2$ to $1$ when $|U|$ has bounded mean, plus sharp width-density counterexamples showing density-zero support alone is insufficient (including logarithmic-support normal numbers and polynomial-coefficient normal numbers).
   - Isolated-source law $1 - D_N(F) = (1+o(1))(W(N) + S_{\rm eff}(N)\lambda_N)/N$, giving exact leading constants for power-law supports, logarithmic supports, the prime constant $\sum_p b^{-p}$ ($\sim \frac{\log\log N}{\log b \cdot \log N}$), growing-width series, and the positive-coefficient clustering shadow law.

2. **Euler's product $E_b$, its low powers, and sparse quadratic polynomials (Track A1–A2, B5, kernel-verified core in `NormalityChecker/EulerPentagonal.lean`):**
   - Exact base-$b$ digit block structure of $E_b = \prod_{k \ge 1}(1 - b^{-k})$, explicit all-prefix word frequencies ($1/2$ for $0^L$ and $(b-1)^L$; $E_2$ simply normal, $E_b$ not simply normal for $b \ge 3$; never disjunctive), and sharp discrepancy asymptotic $1 - D_N(E_b; b) = \sqrt{2/3}\,\log_b N / \sqrt{N} + O_b(1/\sqrt{N})$.
   - Exact base-$b$ digits and **disjunctivity** of $E_b^3$ with sharp gap $1 - D_N(E_b^3; b) = \sqrt{2}\,\log_b N / \sqrt{N} + O_b(1/\sqrt{N})$ — a clean elementary companion to the multiplicative Lambert disjunctive-nonnormal phenomenon, with polynomial rather than logarithmic rate.
   - Complete analysis of $E_b^2$ via the weight-1 Klein-four CM eigenform $\eta(12\tau)^2$, establishing exact prime-factorization support, Serre exponent $\lambda = 3/4$, and $1 - D_N(E_b^2; b) \asymp (\log\log N)/(\log N)^{3/4}$.
   - Polynomials of degree $\le 3$ in $E_b$ over $\mathbb Z[1/b]$ lie in $K_b$, sharp rational-scalar criterion $(a/d)E_b \in K_b \iff a/d \in \mathbb Z[1/b]$ (with exact limits $D_N(E_2/3; 2) \to 1/2$, $D_N(E_3/2; 3) \to 2/3$), and degree-$\le 2$ polynomials in unary quadratic-polynomial sparse series (Track B5).

3. **Binary quadratic-form theta values and weight-1 modular forms (Track A3–A4):**
   - Every positive definite integral binary quadratic form $Q$ satisfies $\Theta_Q(1/b) \in K_b$ with $1 - D_N(\Theta_Q(1/b); b) \ll_{Q,b} (\log\log N)/\sqrt{\log N}$ and matching lower bound, including imprimitive forms, shifted lattices, congruence subsums, and character twists.
   - **Every** holomorphic weight-1 modular form $f$ with integer Fourier coefficients on $\Gamma_1(M)$ (dihedral CM, exotic $A_4/S_4/A_5$, and Eisenstein series alike) satisfies $f(1/b) \in K_b$ with $1 - D_N(f(1/b); b) \ll_{f,b} (\log\log N)/(\log N)^{\alpha_f}$, via Deligne–Serre + Chebotarev + $A(X) \ll X \log X$.
   - Structural boundary at weight $\ge 2$: Serre's lacunary even $\eta$-powers ($\eta^4, \eta^6, \eta^8, \eta^{10}, \eta^{14}, \eta^{26}$) fail coefficient transfer because polynomial coefficient growth causes radix-digit overlap despite zero coefficient density.

4. **Exact leading constant for $L_{\chi_4}$, $\Theta_3(1/2)^2$, and real-character Lambert series (Track B4):**
   - Upgrades Phase 17's order result (Paper VI, `CC-48`) to the exact leading asymptotic $1 - D_N(L_{\chi_4}; 2) = \sup_x |D_N(x + L_{\chi_4}; 2) - D_N(x; 2)| \sim \frac{K}{2\log 2}\frac{\log\log N}{\sqrt{\log N}}$ where $K = 0.76422365\dots$ is the Landau–Ramanujan constant (and the same asymptotic for $\Theta_3(1/2)^2$, and $C_\chi/(2\log 2)$ for every real nonprincipal $\chi$), explicitly contrasting $K$ with the BBCP (2004) 1-bit constant $C_0 \approx 0.7996$.

5. **Dense $q$-series, partitions $P_b$, multiplication/inversion in $K_b$, and residue-class Lambert transfers (Tracks D1–D4, E1–E3, kernel-verified mod-8 core in `NormalityChecker/CharacterLambertTransfer.lean`):**
   - Carry-window transfer framework, partition generating function $P_b = 1/E_b$ (congruence wash-out, pentagonal circle recurrence, honest open status), non-closure of $K_b$ under squaring and arbitrarily lacunary $z$ with $1-z \in K_2$ and $\liminf D_N(1/(1-z)) = 0$.
   - Exact residue-class Lambert transfers for $(\mathbb Z/q)^\times/H \cong (\mathbb Z/2)^k$ (mod 8, mod 24, general 2-elementary quotients), proving identical binary discrepancy asymptotics for $A_1, A_3, A_5, A_7$ and $E_{\rm odd}$, while plainly separating this from the still-open problem for $E_{\rm odd}$ and $E$ individually.

### Verdict on standalone paper worthiness

**Strong Yes — warrants a new standalone manuscript (Paper XI candidate).**

Why it should be its own paper rather than scattered across revisions of Papers VI and X:
- **Cohesive new theorem family:** Euler products ($E_b, E_b^2, E_b^3$), general binary quadratic-form theta values $\Theta_Q(1/b)$, and all integer-coefficient weight-1 modular forms $f(1/b)$ are classical number-theoretic objects that do not live in Paper VI (binary multiplicative Lambert series) or Paper X (abstract discrepancy arithmetic).
- **Single unifying engine:** The finite sparse coefficient transfer inequality (`CoefficientTransfer.lean`) and the isolated-source law tie all of Tracks A, B, D, and E together into one clean conceptual arc: *sparse support + controlled mass $\implies K_b$ (exact constants via isolation) $\implies$ structural overlap barrier at weight $\ge 2$ and dense $q$-series ($P_b$, $\Theta^3$, $E_2, E_4, E_6$)*.
- **Clean literature positioning:** Primary-source comparison ([literature.md](literature.md)) found no published paper proving base-$b$ discrepancy asymptotics for $E_b, E_b^2, E_b^3$, $\Theta_Q(1/b)$, weight-1 modular forms, or the exact leading constant $K/(2\log 2)$ for $L_{\chi_4}$ and $\Theta_3(1/2)^2$, while cleanly siting the results against BBCP (2004), Serre (1981, 1985), Deligne–Serre (1974), Landau–Bernays, Nesterenko (1996), Rauzy (1976), and Bergelson–Downarowicz (2025).

---

## 2. What Belongs in Revisions of Existing Manuscripts Instead

The remaining Phase 20 results fit much more naturally as targeted future v1.1/v2.0 revisions of existing preprints (never editing archived `manuscripts-v2.0.0` releases in place):

| Existing Manuscript | Phase 20 Material Fitting a Future Revision | Recommendation |
|---|---|---|
| **Paper VI** (*Disjunctive but Nonnormal Multiplicative Lambert Series*, v1.0 on alphaXiv) | Track B4 exact leading constant $K/(2\log 2)$ (and $C_\chi/(2\log 2)$) for $L_{\chi_4}$ and general real $\chi$; Track E1 residue-class Lambert transfers ($A_1, A_3, A_5, A_7 \equiv E_{\rm odd}$ up to $O(\log\log N/\sqrt{\log N})$). | Include B4 as a headline theorem of the new Paper XI *or* as Paper VI v2.0; avoid double-claiming by citing Paper VI v1.0 in Paper XI and upgrading Paper VI only if the owner wants a unified Lambert monograph. |
| **Paper VII** (*Synthetic Arithmetic Expansions and Prescribed Discrepancy*, v1.0 on alphaXiv) | Track C1–C2 (universal all-prime polynomial normality `W` with super-logarithmic rate $\exp(-c(\log N)^{2/3})$ and protected-pole algebras, plus kernel-verified [`ProtectedPole.lean`](../../NormalityChecker/ProtectedPole.lean), `GF-10`) and Track C3 (higher-degree polynomial normality for all $r < d$ on power schedules $t k^d$, `GF-11`, audited and repaired in [track-c-review.md](reviews/track-c-review.md)). | **Definitely belongs with Paper VII (v2.0)** rather than the generating-functions paper — Track C directly extends Paper VII's valuation-weighted power-schedule and all-prime normality results (`SY-02`, `OP-09`, `OP-14`). |
| **Paper X** (*The Arithmetic of Extreme Discrepancy*, v1.0 on alphaXiv) | Track D4 (non-closure of $K_b$ under squaring, sumset criterion, radix-primary reciprocal test, arbitrarily lacunary $z$ with $1-z \in K_2$ and $\liminf D_N(1/(1-z)) = 0$); Track B1 general coefficient-transfer criterion for $K_b$. | Track D4 can be included in Paper XI as the multiplication/inversion obstruction section (directly motivating why $P_b = 1/E_b$ and $E_b^4$ resist $K_b$ methods) and cross-referenced in any future Paper X v2.0. |
| **Paper V** (*Denominator Growth and Rational Shadowing for Classical Constants*, v2.0) | Track E2 (chronological prefixes of $\ln 2 = \sum \mu(m) F(2^{-m})$ collapse to ordinary Taylor prefixes and inherit `OP-11`). | Short remark in any future Paper V revision; also suitable as a brief section in Paper XI contrasting sparse vs. logarithmic Euler-product transfers. |

---

## 3. Immediate Publication-Hygiene Actions (Pre-Release / Existing Four alphaXiv Preprints)

From [publication-audit.md](publication-audit.md):

1. **Merge PR #3 / branch to `main`** so GitHub Pages deploys the four alphaXiv links onto the live manuscript pages at `https://eldernos.github.io/MathematicsResearch/papers/…/`.
2. **Owner check on Paper VII's alphaXiv licence:** Live SSR inspection on 25 November 2026 showed Papers VI, I, and X carry `CC BY 4.0` (`http://creativecommons.org/licenses/by/4.0/`), whereas Paper VII (`2611.synthetic-arithmetic-expansions-prescribed-discrepancy`) carries the default alphaXiv submission-policy licence (`https://www.alphaxiv.org/docs/submission-policy#license`). The owner should check Paper VII's alphaXiv licence setting and visually confirm PDF checksums and AI disclosures on all four pages.
3. **Second-batch alphaXiv papers (II, III, IV, V, VIII, IX):** Wait for owner authorization; all verification maps, ledgers, and metadata already pass strict checks.

---

## 4. Readiness Checklist Before Drafting Paper XI (Future Phase)

Before turning the Phase 20 generating-functions results into a formal manuscript (`papers/11-generating-functions-digits/`):

- [ ] **Owner decision** on scope: keep Paper XI focused on Tracks A + B + D + E (generating functions, Euler products, theta/weight-1 modular forms, coefficient transfer, Lambert leading constant, partition/product obstructions) while routing Track C to Paper VII v2.0.
- [ ] **Optional Lean expansion:** `CoefficientTransfer.lean`, `EulerPentagonal.lean`, and `CharacterLambertTransfer.lean` already kernel-verify the core transfer theorem, $E_b \in K_b$, $E_b^3 \in K_b$, composite-radix factorization, circle separation (Lemma 3.3), and mod-8 character transfers. Formalizing the non-lookahead shadow bound $L(1+S(N-1))$ and Theorem 1.5 rate in `CoefficientTransfer.lean` would upgrade even more statements from `paper` to `lean` or `lean+paper`.
- [ ] **Primary-source bibliography confirmation:** Verify Euler (1750/1783) dates via Bell (`arXiv:math/0510054`) and confirm exact journal bibliographic records for Landau (1908), Bernays (1912), Nesterenko (1996), and DNNS (1996) in `LEDGER.md`.
- [ ] **Strict publication contract:** Complete `paper.tex`, `paper.pdf`, `metadata.toml`, `VERIFICATION.md`, `LEDGER.md`, independent multi-model manuscript review, and human specialist review before any external submission.
