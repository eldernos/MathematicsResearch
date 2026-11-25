# Verification map: Disjunctive but Nonnormal Multiplicative Lambert Series (v1.0)

Lean links are pinned to research-checkpoint-18, commit `e4809cf561573aef588e6ffc491a35cdb79fd9ec`. At that commit the integrated `lake build` succeeded, the axiom audit accepted only `propext`, `Classical.choice` and `Quot.sound`, and an independent kernel replay covered every module (`notes/phase18/verification.md`). The written proofs have been checked only by AI models; human specialist review is outstanding. Cross-model review is not peer review.

Abbreviation: `L4` = `https://github.com/eldernos/MathematicsResearch/blob/e4809cf561573aef588e6ffc491a35cdb79fd9ec/NormalityChecker`.

Hypotheses (H1)–(H4) are those of §1.1 of the paper: a set S of primes containing a reduced class modulo q₀ with Σ_{p≤x, p∈S} 1/p = δ log log x + O(1), 0 < δ < 1; c ≥ 0 multiplicative, integer-valued, c(pᵉ) ≤ e + 1; c(p) = 2 on S and c(p) = 0 at other primes not dividing q₀; c(p₀^{2u}) = 2u + 1 at one p₀ ∈ S. κ = 1 − δ.

## Theorem verification table

| # | Statement (short) | Evidence | Lean declarations | External inputs | Reproduce |
| --- | --- | --- | --- | --- | --- |
| Thm A | Under (H1)–(H4), 7/12 < a ≤ 1, N^a ≤ H ≤ N: #_w(N,H) ≍ H/(log N)^κ for words containing a 1; H − #_{0^k}(N,H) ≍ H/(log N)^κ. Upper bounds for all a > 0. | Lean-supported paper proof | [`arrival_sum`](https://github.com/eldernos/MathematicsResearch/blob/e4809cf561573aef588e6ffc491a35cdb79fd9ec/NormalityChecker/ErdosBorweinArrivals.lean#L41) (identity (2), Lemma 3.2); [`nonneg_one_bit_count_le`](https://github.com/eldernos/MathematicsResearch/blob/e4809cf561573aef588e6ffc491a35cdb79fd9ec/NormalityChecker/WeightedLambertIdentities.lean#L166) (Markov step, Prop. 3.3(a)) | Shiu 1980, Thm 1, p. 163; Perelli–Pintz–Salerno 1985, Theorem, p. 2 (only q = q₀); Montgomery–Vaughan 1973, Thm 2 (1.10), p. 121; Mertens (Montgomery–Vaughan 2007, Thm 2.7) | Paper proof: §§3–6. Lean: see “Reproduce”. |
| Cor 1.1 | Prefix counts #_w(0,M) ≍ M/(log M)^κ (w ∋ 1); one-frequency → 0; L disjunctive and irrational; not simply normal. | Lean-supported paper proof | as Thm A | as Thm A | §6 |
| Thm B | 1 − D_N(L) ≍ (log log N)/(log N)^κ; D_N(L) → 1. | Lean-supported paper proof | [`one_sub_discrepancy_le_one_bits`](https://github.com/eldernos/MathematicsResearch/blob/e4809cf561573aef588e6ffc491a35cdb79fd9ec/NormalityChecker/Phase17DiscrepancyBounds.lean#L98) (upper bound); [`upper_freq_le_one_bits`](https://github.com/eldernos/MathematicsResearch/blob/e4809cf561573aef588e6ffc491a35cdb79fd9ec/NormalityChecker/Phase17DiscrepancyBounds.lean#L77) (auxiliary); [`one_sub_discrepancy_ge_of_separated_mass`](https://github.com/eldernos/MathematicsResearch/blob/e4809cf561573aef588e6ffc491a35cdb79fd9ec/NormalityChecker/Phase17DiscrepancyBounds.lean#L123) (lower bound) | as Thm A (via Prop. 3.3, Prop. 5.3) | §7 |
| Cor 1.2 | sup_x \|D_N(x+L) − D_N(x)\| = 1 − D_N(L), attained at x = 0, ≍ (log log N)/(log N)^κ; translation by L preserves lim sup and lim inf of D_N. | Lean-supported paper proof (the exact identity, for every real translation z, is Kernel-verified; the order is a paper deduction from Thm B) | [`sharp_translation_isGreatest`](https://github.com/eldernos/MathematicsResearch/blob/e4809cf561573aef588e6ffc491a35cdb79fd9ec/NormalityChecker/SharpTranslation.lean#L386), [`sharp_translation`](https://github.com/eldernos/MathematicsResearch/blob/e4809cf561573aef588e6ffc491a35cdb79fd9ec/NormalityChecker/SharpTranslation.lean#L343), [`radixDiscrepancy_zero`](https://github.com/eldernos/MathematicsResearch/blob/e4809cf561573aef588e6ffc491a35cdb79fd9ec/NormalityChecker/SharpTranslation.lean#L357) | Companion manuscript “Synthetic Arithmetic Expansions and Prescribed Discrepancy” (papers/07-synthetic-expansions) for the identity; Thm B | §8 |
| Thm C | For odd χ (primitive or imprimitive) and algebraic 0 < \|q\| < 1, Σ χ(m)qᵐ/(1−qᵐ) is transcendental; in particular L_χ for odd real χ. | Paper proof | — | Hamieh–Murty 2016, Thm 1.1 (p. 766) for primitive χ; Thm 3.1 (p. 771) for the imprimitive oldform combination; both rest on Nesterenko 1996 | §9 |
| Lemma 2.1 | Σ f(m)/(2ᵐ−1) = Σ c(n)2⁻ⁿ, \|f\| ≤ τ. | Lean-supported paper proof | [`lambert_head_eq_taylor`](https://github.com/eldernos/MathematicsResearch/blob/e4809cf561573aef588e6ffc491a35cdb79fd9ec/NormalityChecker/WeightedLambertIdentities.lean#L21) (finite head only) | — | §2 |
| Lemma 2.2 | Odd-part reindexing x_n = {A(n)}, 0 ≤ x_n ≤ A(n). | Paper proof | — | — | §2 |
| Lemma 3.1 | Σ_{x−y<m≤x} U(m) ≪ y/(log x)^κ for x^σ ≤ y ≤ x. | Paper proof | — | Shiu 1980, Thm 1, p. 163 (applied with k = 2, a = 1) | §3 |
| Lemma 3.2 | Window and prefix masses of A(n). | Lean-supported paper proof | `arrival_sum` (above) | Lemma 3.1 | §3 |
| Prop 3.3 | Upper bounds for ones, words with a one, rejected zero-word starts, prefixes. | Lean-supported paper proof | `nonneg_one_bit_count_le` (above) | Lemma 3.2 | §3 |
| Thm 4.1 | Shiu's theorem (quoted). | External input | — | Shiu, J. Reine Angew. Math. 313 (1980) 161–170, Thm 1, p. 163; class M defined p. 162; (1.1) on p. 161 | — |
| Thm 4.2 | Perelli–Pintz–Salerno short-interval Bombieri–Vinogradov (quoted). | External input | — | Invent. Math. 79 (1985) 1–9, Theorem, p. 2; estimate (1.1), p. 1 | — |
| Thm 4.3 | Montgomery–Vaughan Brun–Titchmarsh (quoted). | External input | — | Mathematika 20 (1973) 119–134, Thm 2, (1.10), p. 121 | — |
| Lemma 4.4 | Primes ≡ a₀ (mod q₀) in (X, X+Y], Y ≥ (X+Y)^ν, ν > 7/12: (1+o(1))Y/(φ(q₀) log X). | Paper proof | — | Thm 4.2 (single modulus q₀) | §4 |
| Lemma 4.5 | Harmonic sums over Q (primes ∤ q₀ outside S). | Paper proof | — | Mertens (MV 2007, Thm 2.7) | §4 |
| Lemma 4.6 | Σ_{m∈M_N} 1/m ≫ (log N)^δ. | Paper proof | — | Mertens; Rankin's trick | §4 |
| Lemma 4.7 | Selberg upper-bound sieve with explicit G(z) lower bound and trivial remainders. | Paper proof (self-contained) | — | Mertens | §4 |
| Lemma 5.2 | Consequences of R-isolation: x_n ∈ I_w, x_{n−r} = 2^{−r}x_n. | Paper proof | — | — | §5 |
| Prop 5.3 | Planted occurrences: ≫ H/(log N)^κ R-isolated starts in [N, N+H). | Paper proof | — | Lemmas 4.4–4.7; Thm 4.3 | §5 |
| Prop 6.1 | #{m ≤ x : c(m) > 0} ≍ x/(log x)^κ. | Paper proof | — | Lemma 3.1; Prop. 5.3 construction | §6 |
| Lemma 7.1 | 1 − D_N(x) ≤ 2^{−L} + (L−1)/N + L·F_N(1/2,1), every real x. | Kernel-verified | `one_sub_discrepancy_le_one_bits` (above) | — | Lean |
| Lemma 7.2 | Separated-mass lower bound for 1 − D_N(x), every real x. | Kernel-verified | `one_sub_discrepancy_ge_of_separated_mass` (above) | — | Lean |
| Rem 7.3 | 1 − D_N(x) ≥ min(1/3, F_N(1/4,3/4)) − 1/N. | Kernel-verified (inequality); application is a paper deduction | [`one_sub_discrepancy_ge_transition`](https://github.com/eldernos/MathematicsResearch/blob/e4809cf561573aef588e6ffc491a35cdb79fd9ec/NormalityChecker/Phase17DiscrepancyBounds.lean#L28) | — | Lean |
| Thm 8.1 | \|D_N(x+z) − D_N(x)\| ≤ 1 − D_N(z), equality at x = 0 (base 2). | Kernel-verified (result of the companion manuscript) | `sharp_translation_isGreatest`, `sharp_translation`, `radixDiscrepancy_zero` (above) | — | Lean |
| Thm 9.1 | Hamieh–Murty Theorems 1.1 and 3.1 (quoted). | External input | — | Int. J. Number Theory 12 (2016) 765–773: Thm 1.1 p. 766, Thm 3.1 p. 771 | — |
| §10.2 | Certified 132,096 binary digits of L_{χ₄} and the δ = 1/4 example; finite discrepancy enclosures. | Finite certificate | — | — | `python -B scripts/phase17_multiplicative_lambert.py` |

Lean definitions used to match the paper: [`shift`](https://github.com/eldernos/MathematicsResearch/blob/e4809cf561573aef588e6ffc491a35cdb79fd9ec/NormalityChecker/Basic.lean#L15) (= {bⁿx}), [`frequency`](https://github.com/eldernos/MathematicsResearch/blob/e4809cf561573aef588e6ffc491a35cdb79fd9ec/NormalityChecker/Basic.lean#L18) (half-open [a,c), first N starts), [`radixDiscrepancy`](https://github.com/eldernos/MathematicsResearch/blob/e4809cf561573aef588e6ffc491a35cdb79fd9ec/NormalityChecker/BinaryDiscrepancy.lean#L11) (sup over 0 ≤ a < c ≤ 1 of \|frequency − (c − a)\|), [`transitionFrequency`](https://github.com/eldernos/MathematicsResearch/blob/e4809cf561573aef588e6ffc491a35cdb79fd9ec/NormalityChecker/BinaryDiscrepancy.lean#L23) (frequency of [1/4,3/4)). The paper's D_N, F_N(s,t) and x_n are these objects with b = 2.

## What is completely kernel-verified

Only finite inequalities and identities valid for every real number (or every finite family of sources):

- Lemma 7.1 and its auxiliary count (`one_sub_discrepancy_le_one_bits`, `upper_freq_le_one_bits`, internally `nonzero_shift_has_one_bit`, line 46).
- Lemma 7.2 (`one_sub_discrepancy_ge_of_separated_mass`).
- The transition inequality of Remark 7.3 (`one_sub_discrepancy_ge_transition`, which uses `sharp_finite_discrepancy`, `SharpDiscrepancy.lean` line 68).
- Theorem 8.1, the sharp translation identity (`sharp_translation_isGreatest`), a result of the companion manuscript.
- The finite source-reindexing identity (`arrival_sum`) and the finite Markov one-bit inequality (`nonneg_one_bit_count_le`) used in §3, and the finite Lambert–Taylor head identity (`lambert_head_eq_taylor`).

None of Theorems A, B, C or Corollaries 1.1, 1.2 is formally verified in its entirety. The Lean statements do not mention multiplicative functions, the hypotheses (H1)–(H4), Shiu's theorem, sieve estimates or modular forms.

## External analytic dependencies

| Input | Exact statement used | Location | Checked against |
| --- | --- | --- | --- |
| Shiu 1980 | Theorem 1: for f in class M (f ≥ 0 multiplicative, f(pˡ) ≤ A₁ˡ, f(n) ≤ A₂(ε)n^ε), 0 < α, β < 1/2, uniformly for 0 < a < k, (a,k) = 1, k < y^{1−α}, x^β < y ≤ x: Σ_{x−y<n≤x, n≡a (k)} f(n) ≪ (y/φ(k))(1/log x) exp(Σ_{p≤x, p∤k} f(p)/p). | J. Reine Angew. Math. 313 (1980), p. 163 (class M p. 162; (1.1) p. 161). DOI 10.1515/crll.1980.313.161 | GDZ page scans of pp. 161–164 |
| Perelli–Pintz–Salerno 1985 | Theorem (p. 2): estimate (1.1) holds for y = x^θ, 7/12 < θ ≤ 1, Q = x^{1/40}; (1.1) is Σ_{q≤Q} max_{(a,q)=1} max_{h≤y} max_{x/2<z≤x} \|ψ(z+h;q,a) − ψ(z;q,a) − h/φ(q)\| ≪ y log^{−A} x. Used only for the single modulus q₀ (Lemma 4.4). | Invent. Math. 79 (1985), pp. 1–2. DOI 10.1007/BF01388653 | GDZ page scans of pp. 1–2 |
| Montgomery–Vaughan 1973 | Theorem 2, (1.10): π(x+y;k,l) − π(x;k,l) < 2y/(φ(k) log(y/k)) for (k,l) = 1, y > k. | Mathematika 20 (1973), p. 121. DOI 10.1112/S0025579300004708 | Full text (PDF) |
| Mertens | Σ_{p≤x} log p/p = log x + O(1), Σ 1/p = log log x + O(1), Π(1 − 1/p) ≍ 1/log x. | Montgomery–Vaughan, Multiplicative Number Theory I (2007), Thm 2.7 | Secondary citations of the theorem number |
| Dirichlet | Σ_{p≤x} χ(p)/p = O(1) for nonprincipal χ (Examples 1.3, 1.4). | Davenport, Multiplicative Number Theory, Chs. 1 and 4 | Standard |
| Hamieh–Murty 2016 | Thm 1.1: primitive χ of conductor N, χ(−1) = (−1)^k, q algebraic, \|q\| < 1 ⇒ L_q(k,χ) transcendental. Thm 3.1: nonzero modular form of level N, weight k, algebraic Fourier coefficients, e^{2πiτ} algebraic ⇒ f(τ) transcendental. | Int. J. Number Theory 12 (2016), pp. 766 and 771. DOI 10.1142/S1793042116500494 | Full text (archived author PDF, journal pagination) |
| Wirsing 1961 | Satz 1 (only in a remark, not used in any proof). | Math. Ann. 143 (1961), p. 76 | GDZ page scan |

Primary-source audit outcome (details in LEDGER.md, “Audit record”):

- Shiu's theorem requires 0 < a < k, so k = 1 is excluded; Lemma 3.1 uses k = 2, a = 1 and separates powers of two. Verified.
- PPS 1985: the admissible range is y = x^θ, 7/12 < θ ≤ 1 with Q = x^{1/40}. The threshold a > 7/12 in Theorem A comes only from this (Huxley's exponent). In this version the sieve uses trivial remainders, so the level Q is not used.
- Selberg sieve: proved in full in Lemma 4.7, including |λ_d| ≤ 1 and G(z) ≥ ½ Π_{q≤z^{1/8}}(1 − g(q))^{−1}.
- Montgomery–Vaughan: used with d′ ≤ 2√N ≤ Y^{7/8}, which needs (a − θ)·7/8 > 1/2. This holds because a − θ > 7/12.
- Hamieh–Murty Thm 1.1 covers only primitive characters. The imprimitive case is deduced from Thm 3.1, applied to a nonzero weight-one form on Γ₁(q*P).

## Reproduce

From the repository root at the pinned commit (or this branch):

```sh
# Lean statements (no full build needed to read them)
git show e4809cf:NormalityChecker/Phase17DiscrepancyBounds.lean | sed -n '28,180p'
git show e4809cf:NormalityChecker/SharpTranslation.lean | sed -n '336,392p'
git show e4809cf:NormalityChecker/ErdosBorweinArrivals.lean | sed -n '35,55p'
git show e4809cf:NormalityChecker/WeightedLambertIdentities.lean | sed -n '163,180p'

# Full kernel check (long): Lean 4.36.0 toolchain
lake build NormalityChecker.Phase17DiscrepancyBounds NormalityChecker.SharpTranslation \
  NormalityChecker.ErdosBorweinArrivals NormalityChecker.WeightedLambertIdentities

# Finite certificate (standard library only, ~2 s)
python -B scripts/phase17_multiplicative_lambert.py

# Manuscript
wsl -d Ubuntu -- bash papers/wsl-build.sh 06-multiplicative-lambert
```

The checkpoint's recorded build, axiom audit and kernel replay are in `notes/phase18/verification.md`. The research note from which the manuscript was developed is `notes/phase17/multiplicative-lambert.md` (CC-48). The translation corollary corresponds to SY-24 (`notes/phase18/phase17-transfer.md`).
