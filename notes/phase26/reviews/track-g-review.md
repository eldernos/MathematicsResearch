# Phase 26 Track G (G1–G3): Independent Cross-Provider Referee Review

**Reviewer:** Claude Opus 5.5 (Anthropic) via Claude Code, acting as cross-provider review sub-agent.
**Date:** 28 November 2026.
**Branch / worktree:** `research/phase-26-arithmetic-amplification` (files under review are uncommitted).
**Files audited:** [`notes/phase26/external-grh-and-lambert-windows.md`](../external-grh-and-lambert-windows.md) (720 lines) and [`scripts/phase26_grh_windows.py`](../../../scripts/phase26_grh_windows.py) (658 lines).
**Repository inputs consulted:** `notes/phase25/grh-lambert-windows.md` (`GF-48`: Theorem A, Corollary A.2, Remark B.1, Lemma E.2, Steps 2′–7′, Proposition D.2, §9 open questions), `notes/phase22/radix-thresholds-and-class-groups.md:8`, `docs/registry/GF.toml:381`, `docs/research-objectives.md` (Rules 1–5).

> **Cross-model review is not independent human peer review.** This is a review by an AI model from a different provider than the one that drafted Track G. It does not count as refereeing, and none of its conclusions authorize a change to a benchmark status or promote any result to peer-reviewed status.

---

## Verdict: **REVISE** (0 Critical, 4 Major, 8 Minor, 4 Nit)

No theorem in G2 was invalidated. I tried to break every statement and every exponent. All main conclusions survive: G2.1A (all *C* > 2 and the *C* = 2 endpoint), G2.1B, G2.2A, G2.2A′, G2.2B, G2.2C, G2.2D, G2.3, G2.4A, G2.4B. The four Major findings must still be fixed before any registry entry is written:

- **M1:** a false intermediate inequality in G2.4A when φ(*h*) ≥ 4. I give a counterexample. The repair keeps the conclusion.
- **M2:** G2.4B claims more than it proves. Its stated scope goes beyond its proof, and it conflicts with Open Question 4(b).
- **M3:** G2.2C, G2.2A and G2.2D depend on Huxley's zero-density input, which was read only at the `[S]` level. The exact form of that input matters near σ = 1.
- **M4:** the G3 audit leaves out Matomäki–Radziwiłł II (`arXiv:2007.04290`), which directly bears on the almost-all-window claims.

The revisions are local. Each one is a lemma insertion, a scope restriction or a provenance action.

---

## 1. Reproduction and exactness audit of `scripts/phase26_grh_windows.py`

| Check | Result |
| --- | --- |
| `python -B scripts/phase26_grh_windows.py` (Windows, no WSL) | Exit code `0`. Output: `ALL 14965 CHECKS PASSED (14946 exact, 19 finite)`. Matches the note's §7 and §8 counts. Runtime about 0.26 s (the note says "≈ 1 s"). |
| Static scan of the `[exact]` region (lines 1–555) for float tokens (`float(`, decimal literals, `math.log/sqrt/exp/cos/pi`, `1e-`) | Every hit is a comment, a message string, or the numerator/denominator of a `Fraction`. `math` is used only through `math.isqrt` on integers. |
| **Runtime type audit** (I monkey-patched `check_exact` to inspect the caller's local variables on all 14,946 calls) | **Zero** `float` locals in any frame that calls `check_exact`, and every asserted condition is a `bool`. **No floating-point value enters any `C1`–`C6` exact certificate.** |
| `ln_rat_enclosure` | Valid outward enclosure. The reduction `r → r/2` uses exact `Fraction`s. After the loop `zpow = z^(2K+1)`, so the tail bound `2 z^(2K+1)/((2K+1)(1−z²))` is correct. |
| `C6` P(2) and P_𝒫′(2) | Exact rational partial sums over p ≤ 10⁴, with the tail bounded by Σ_{n>10⁴} 1/(n(n−1)) = 10⁻⁴. The enclosures [0.452238, 0.452338] ∋ P(2) = 0.4522474… and [0.422597, 0.422697] are correct. The set 𝒫′ = {p ≡ 2, 3, 4, 5 (mod 7)} is exactly the set of primes with χ(p) ≠ 1 for the cubic character mod 7, since the cubes mod 7 are {1, 6}. |
| `C6` integer certificates | 2²¹·10¹⁰ < 43¹⁰ ⇔ g₃(2.1) < 1 ✓; 2²¹·10⁴⁰ > 42748¹⁰ ⇔ g₃(2.1) > 0.996 ✓; 80000 < 81225 ⇔ 2√2/3 < 0.95 ✓. |
| `C5` δ*_b | δ*₆ = 0.701754…, δ*₁₀ = 0.673632…, δ*₁₂ = 0.765433… with β_b = log b / log b′. These agree with `notes/phase22/radix-thresholds-and-class-groups.md:8`. The note correctly flags that the prose formula at `docs/registry/GF.toml:381` contradicts its own numbers: as printed it gives δ*₆ = 1/2. |

**Caveat on what the checks prove (Minor m7).** Several `[exact]` checks are true by construction and carry no evidentiary weight:

- `C1` "SHA validation" checks hexadecimal **format** only. I verified the SHA *values* on GitHub myself (§2).
- `C2` part 3 uses an illustrative `C_2 = 10` and sets `K_min = isqrt(rhs)+1`, so `K_min² > rhs` holds automatically.
- `C3` checks `2·c_lo < 2·c_hi` and `2·(d/lo) == 2d/lo`.
- `C4` checks `61.5 + 0.5 = 62`.
- `C6` part 1 checks coefficient bookkeeping of Σ_j (2 + x^j + x^{−j}) and never evaluates at a root of unity.

They are harmless, but the headline "14,946 exact checks" overstates their content. §8 should call these "consistency checks". Separately, G2.3 Step 2 cites `C5` for the Shiu-class membership of g_t and z^{ω_S}, but `C5` checks only h_q.

---

## 2. G1: primary-source verification and evidence policy

**Independently re-verified by this reviewer (GitHub API, read-only, 28 Nov 2026):**

| Claim in §1 | Verified value |
| --- | --- |
| Sole commit of `lsernau/grh-lean` | `72fead102f663d5c7a407964a13dc0cf9d977207`, committed `2026-11-25T20:38:07Z`, GitHub reports `verified: true` ✓ |
| Tree SHA | `5eb1240f03e791edd3fc7aa84a3a7d8dc3997b7f` ✓ |
| `grh/src/Statements.lean` vs `grh-compact/src/Statements.lean` | Byte-identical (783 bytes). Imports only `Mathlib`. The four `def`s match §1.2 verbatim ✓ |
| `Main.lean` (both editions) | The same five theorems with the same proof terms. The only difference is that the compact edition drops the docstrings ✓ |
| `lean-toolchain` (both editions) | `leanprover/lean4:v4.35.0` ✓ |
| `lake-manifest.json` (both editions) | Mathlib `56a005855ea1…`, together with the batteries, aesop, Qq, Cli, plausible, importGraph, proofwidgets and LeanSearchClient revisions, all prefix-match §1.1 ✓ |
| `.lean` file counts | `grh/src`: 803 = 495 (Lib) + 306 (New) + 2. `grh-compact/src`: 794 = 573 + 219 + 2 ✓ |
| README caveat | "The proof has passed machine checks only… No mathematician has read it through, and no paper comes with it." ✓. Licence Apache 2.0, Copyright 2026 Anthropic, PBC ✓ |
| `https://alpo.ge/remark.pdf` | HTTP 200, `Content-Length: 245114` (matches the stated 245,114 bytes) ✓ |
| Lean FRO blog post URL | HTTP 200 ✓ |

**Not independently re-run:** the MIT and Waterloo kernel logs, the declaration counts, the `con-leche`/`con-ron`/`nanoda`/`lean4lean` runs and the export hashes. I accept these as `[R]` transcriptions. They are consistent with the README.

**Scope.** I confirmed from the Lean source that the statements cover exactly ζ and every `DirichletCharacter.LFunction χ` for every `N` with `[NeZero N]`, primitive or not. The scope is the open strip, together with nonvanishing on Re s > 1/2 except at s = 1 for χ = 1. ERH, Hecke, Artin and automorphic L-functions are excluded, as are zeros on Re s ≤ 0 and any prime-counting corollary in progressions. §1.4 is accurate. The remark that abelian Dedekind zeta functions follow by factorization is mathematically correct, and the note says correctly that this step is not formalized.

**Policy (§1.6, §5, §6).** The policy is compliant:

- No Phase 26 result is labelled `Kernel-verified`.
- Every GRH-dependent result is `Conditional / External-GRH` with the hypothesis named: `GRH(q_0)` for the fixed modulus, `Dirichlet GRH` for the growing q′.
- Benchmarks `BC-01`…`BC-50` are unchanged.
- The cross-model caveat is stated in the evidence box and again in §4.

This matches Rules 2–4 of `docs/research-objectives.md`, and it matches the revised `GF-48` scope text in the working tree. **G1: ACCEPT.**

---

## 3. G2: theorem-by-theorem attempt to invalidate

### 3.1 G2.1A (Paper VI at H = √N (log N)^C under GRH(q₀)): **holds**

Here B = 2(C − 2) − ε, M = (log N)^B, b ≤ p₀^{2u} M, Y = H/b ≥ √N (log N)^{C−B}/p₀^{2u}, J = ⌈C_J log log N⌉ and C_J log 2 ≥ B + 2. I re-derived every logarithmic power:

| Step | Requirement (exponent of log N) | Status |
| --- | --- | --- |
| 1. Prime supply (Cor. A.2 error/main) | C₂ φ(q₀) √(2bN) log²(4q₀N) / H ≪ (log N)^{B/2+2−C} → 0 needs **C > B/2 + 2** | B/2 + 2 = C − ε/2 ✓. **This is the binding constraint.** |
| 2. Small factors | Σ_{m∈𝓜(M)} 1/m ≍ (log M)^δ ≍_B (log log N)^δ. Rankin with ω(m) ≤ 2 log log N gives (log N)^{−2 log 2}(log log N)^{2δ} = o(1) | ✓ (and j₀ ≤ k + 2 + 2 log log N ≤ J because C_J ≥ 4) |
| 3. (I2) sieve | Y ≥ N^{1/2−o(1)}, shifts ≤ (C_J + C_R + 1) log log N < z₀ = (log N)², remainder Y^{1/2} log² Y per shift | ✓ |
| 4a. Far tail, Y-term | Y log N · J 2^{−J} = o(Y/log N) needs C_J log 2 > 2 | 4 log 2 > 2 ✓ |
| 4b. Far tail, √N-term | √N J 2^{−J} ≤ Y b (log N)^{−C} J 2^{−J} = o(Y/log N) needs **B − C − C_J log 2 < −1** | Holds whenever C > −1, since C_J log 2 ≥ B + 2 ✓ |
| Lemma E.2 application | D = b, Z = bY = H, X₁ = N − 1 + H + j < 3N; τ(gcd(h, b)) ≤ h; Σ_{j>J} j 2^{−j} = (J+2) 2^{−J} | ✓ (by positivity, the sum runs over all n′ ≡ h (mod b), not only primes) |
| 5. Assembly | ≥ (H/(4 p₀^{2u} φ(q₀) log N)) Σ 1/m ≫ H (log log N)^δ/log N; injectivity is Paper VI's | ✓ |
| Part 2 (C = 2, m = 1) | ratio → C₂ φ(q₀) √2 p₀^u / K ≤ 1/4 ⇔ K ≥ 4√2 C₂ φ(q₀) p₀^u (strict inequality for the asymptotic). Use u = 1 (w = "1") for the discrepancy bound | ✓ |
| Part 3 (α ∈ (0,1)) | ratio ≪ M^{−1/2}/log N. Σ 1/m ≍ 2^{−δ}(log N)^{αδ}. Rankin needs αδ < 2 log 2. √N/Y ≤ p₀^{2u}(log N)^{−3}. J = 10 log log N | ✓ |

The claim that Lemma E.2 breaks the a > 1/2 far-tail wall of Remark B.1 is **correct**. In Paper VI the far-tail weights 2^{−j}, j > J, give a free polylogarithmic factor, because J costs only O(J) sieve shifts. In GF-22 the zero block is paid for through the CRT. So the additive 2√X₁ term of Lemma E.2 does not bind for Paper VI at any fixed C. Row 4b holds for every C > −1. Phase 25 Open Question 1 was too pessimistic for Paper VI. *Nit n4:* the script and the proof check B + 1 − C − C_J log 2 < −1, which is stronger than needed (< 0 suffices). Stating the weaker condition makes clear that the far tail is never the bottleneck.

### 3.2 G2.1B (polylogarithmic barrier and sub-polynomial threshold for GF-22): **holds, with wording changes (Minor m2)**

- **log φ(q′) asymptotic.** The kill primes are the s ≍ L smallest primes ≡ g₀ (mod q) above P₀ ≍ s, even after G2.4A enlarges K₀. So Σ log p_j = s log s + O(s), and log φ(q′) = (αd/log b + o(1)) log log N · log log log N ✓. Then φ(q′)/(log N)^C → ∞ for every fixed C ✓.
- **Part 1 is a method barrier, not an impossibility.** The barrier is the pointwise Theorem A error √U log², combined with Lemma E.2's additive √N term, for **this** CRT construction. The summary row calls it "unconditional impossibility of fixed H = √N (log N)^C" and the section is labelled "Paper proof (barrier)". Rephrase as a barrier for the method (see M2 for how to make it method-robust).
- **Part 2 thresholds.** C₀ > αd/log b gives Y/φ(q′) ≥ √N exp((C₀ − αd/log b − o(1)) log log N · log log log N) ≫ √U log²(2q′U) ✓. With α = 1, Shiu applies with y ≥ x^{1/2−o(1)} and modulus N^{o(1)} ✓.
- **"Exact sharp threshold" is inconsistent with the note's own G2.4A.** G2.4A states α*(χ) < 1 (for example 0.9979 at h = 3). Hölder at t = t* together with Shiu on |c_χ|^{t*} then lowers C₀ to α* d/log b. "Sharp" can only mean sharp for the t = 2 CRT method. Change "exact sharp threshold" in §2.1 item 2, summary row G2.1B and §10 to "threshold of the t = 2 CRT method".

### 3.3 G2.2C (unconditional GF-22 on every window, a > 7/12): **mathematically correct in outline; Major M3 (provenance)**

I looked hard for a uniformity bug in the growing modulus q′ = q Q(N, w), with log q′ ≍ log log N · log log log N. I found none:

| Ingredient | q′-dependence | Check |
| --- | --- | --- |
| Zero density Σ_{χ mod q′} N(σ, T, χ) ≪ (q′T)^{12(1−σ)/5}(log q′T)^{C_H} | (q′)^{12/5} = exp(O(log log N · log log log N)) = U^{o(1)}, absorbed by the margin U^{−γ₀/2} with γ₀ = (6/5)(a − 7/12). The log factor is (log U)^{C_H}. **The hybrid form (Q²T)^{12(1−σ)/5} would serve equally well**, because q′^{O(1)} = U^{o(1)} | ✓ |
| Khale, Theorem 1.1. **I verified it verbatim in `arXiv:2210.06457v1`:** for q ≥ 3 and every χ (mod q), L(σ+it, χ) ≠ 0 for σ ≥ 1 − 1/(10.5 log q + 61.5 (log\|t\|)^{2/3}(log log\|t\|)^{1/3}), \|t\| ≥ 10 | 10.5 log q′ = O(log log U · log log log U) = o((log U)^{2/3}), so η(U) = (62 (log U)^{2/3}(log log U)^{1/3})^{−1} for large U ✓. Imprimitive χ inherit the zeros of χ* with conductor q* ≤ q′ ✓ | ✓ |
| Landau–Page for \|t\| ≤ 10 | c₀/log(12 q′) ≍ 1/(log log N · log log log N) ≫ η(U) ✓. Two families with gcd(q′₁, q′₂) = q: an exceptional conductor q₁ dividing both would divide q, and the finitely many characters of conductor dividing q have fixed zero-free margins ✓. Two families are enough, rather than Phase 25's three, because one Q_max is used instead of two evaluation points ✓ | ✓ |
| Low-β zeros | (1/φ(q′)) · φ(q′) T log(q′T) · Y U^{−1/2} = Y U^{(1/2)−a+ε₀} log U, with exponent −(a − 5/12)/2 < −1/12 ✓ | ✓ |
| High-β zeros | ((q′T)^{12/5}/U)^{1−σ}: the exponent 12(1 − a + ε₀)/5 = 17/10 − 6a/5 = 1 − γ₀ ✓. The supremum at 1 − σ = η(U) gives exp(−c (log U)^{1/3}(log log U)^{−1/3}), which beats (log U)^{C_H+1} ✓ | ✓ |
| Truncation, imprimitive, prime powers, x^{1/4} term | U log²/T = U^{a−ε₀} log²; O(ω(q′) log N); O(√N log N); O(U^{1/4} log U), all o(Y/φ(q′)) ✓ | ✓ |
| Steps 6′–7′ | Lemma E.2 needs Y/φ(q′) ≫ √N log N, i.e. a > 1/2 ✓ | ✓ |

**M3 (Major, provenance of a load-bearing input).**

- **Huxley's form is cited specifically but read only second-hand.** The note cites "Huxley (1975), *Acta Arith.* **26**, 435–444, **Theorem 1**: Σ_{χ mod q′} N(σ, U, χ) ≪ (q′U)^{A(1−σ)}(log q′U)^{C_H}" (§3.2 Lemma 3.2 and §5). The G2.5 table and the reference list label Huxley `[S]`, so this specific form was never read in the primary source.
- **The difference matters near σ = 1.** The argument needs zero-density **without an ε-loss outside the factor (1 − σ)**. With a bound (q′T)^{12(1−σ)/5+ε}, the factor T^ε does not decay as σ → 1. It overwhelms U^{−η(U)} = exp(−c(log U)^{1/3}…), and the high-β estimate fails.
- **The preprint shows the risk.** The Chen–Gupta–Li abstract, which I read in `arXiv:2507.08296v2`, states its bound in exactly this ε-form: (qT)^{7(1−σ)/3+ε}. The note is right to segregate that preprint, and its 4/7 and 1/7 addenda need the same repair.

**Required action, either (a) or (b):**

- **(a)** Read Huxley primary and quote the exact statement. A single-modulus (qT) form or the hybrid (Q²T) form both suffice, but either must come with log powers.
- **(b)** Split the σ-range. On 1 − σ ≤ ε₁, use a **log-free** density estimate. Jutila (1977) gives Σ_{χ mod q} N(σ, T, χ) ≪ (qT)^{(2+ε)(1−σ)} near σ = 1. It needs only 2(1 − a + ε₀) < 1, i.e. a > 1/2, so it covers a > 7/12 and also the 4/7 addendum. On 1 − σ ≥ ε₁, any ε-form of Huxley gives a power saving. This route must be primary-verified too.

Khale's own paper remarks (eq. (1.4), citing Montgomery 1971, p. 176) that the **non-explicit** uniform Vinogradov–Korobov region σ ≥ 1 − c′/(log q + (log\|t\|)^{2/3}(log log\|t\|)^{1/3}) is classical. G2.2C needs only that shape, not Khale's explicit constants. This makes the theorem robust, and §5 should say so. The same zero-density provenance issue applies to Lemma 3.2 and therefore to G2.2A and G2.2D.

**Novelty.** The argument is Huxley's prime number theorem in short intervals, applied to progressions with q ≤ x^{o(1)} and with an exceptional modulus avoided. The note should present it as a standard technique applied to the CRT moduli, not as a new analytic method. Priority is provisional (Rule 5).

### 3.4 Almost-all windows: Lemmas 3.1–3.3, G2.2A, G2.2A′, G2.2D, G2.2B: **hold; quantifiers clean (Minor m4)**

- **Lemma 3.1 (Selberg under GRH(q)).** |c(ρ)| ≤ min(δ, 3/|ρ|), the majorant with ŵ ≪ (1+ξ²)^{−1}, AM–GM, and X2 give T² δ log²(qT) ≍ TY log²(qT), plus T log⁴ from truncation ✓. Cauchy–Schwarz over χ is valid, at a loss of φ(q). That loss is the source of the note's φ(q′)² law and the 2αd/log b constant in G2.2B. The law is not optimal, but it is honestly stated.
- **Lemma 3.2.** The normalization (φ(q′)/(TY²)) Σ_χ is correct. The β ≤ 1/2 piece gives φ(q′)² log²/Y. The β > 1/2 exponent A(1 − a + ε₀) = 11/5 − 6a/5 = 2 − γ₁ with γ₁ = (6/5)(a − 1/6) ✓. The truncation term φ(q′)² T^{−2ε₀} log⁴ is absorbed but not displayed (*Nit n2*).
- **Lemma 3.3.** (I2) and (I3) failure is a property of (m, p) alone, with J and R fixed per dyadic X. Each bad (m, p) meets at most H starts N ✓. Paper VI's Brun–Titchmarsh needs moduli ≤ 2√X ≤ (2X/b)^β with β > 2/3, which holds since 2X/b ≥ X^{3/4} ✓.
- **G2.2A (unconditional, a > 1/6).**
  - (a − θ)/(1 − θ) > a − θ ≥ (a + 1/6)/2 > 1/6 ✓.
  - The intervals [t_N, t_N + 1/b) are disjoint ✓, (t, t + δ_m t] ⊂ (t_N, t_N + Y_m] ✓, and δ_m t ≥ Y_m/7 ✓.
  - The prime-power average is ≤ (H/X) Σ_{m≤M} √(X/b) ≪ H √(M/X) ≤ H X^{−3/8} ✓.
  - Markov leaves O(X (log log X)^{1+κ}/(log X)^κ) = o(X) exceptions ✓. The count is ≫ H (log X)^{δ−1} = H/(log X)^κ ✓.
- **G2.2A′ (GRH(q₀)).** Part 1: √(HM) ≤ H X^{−(θ−μ)/2} ✓. Part 2 (m = 1): Chebyshev gives O(X (log X)²/H) = o(X) ✓, provided Y₁ ≫ log² X so that Lemma 3.1's clean form applies ✓.
- **G2.2D and G2.2B.**
  - Fixing L and q′ once per dyadic X with b^L inflated by ψ(X) = log log X changes log q′ by O((log log log X)²) ✓.
  - The averaged-tail interchange holds because each u lies in [U(N), U(N)+Y) for at most AY + 1 starts N ✓. Both the r = 1 and r = 2 computations are correct.
  - The exceptional set is X[φ(q′) exp(−c′(log X)^{1/3}…) + φ(q′)² log²/Y] = o(X) ✓ (unconditional). Under GRH it is X φ(q′)² log²/Y, which is o(X) for C₁ > 2αd/log b ✓.
  - *Nit n1:* the prime-power average should read O(Y √(A/X) log X). A log factor is missing, which is harmless.
- **Quantifiers.** I found no place in the note where "almost all windows" is confused with "every sufficiently late window". Every almost-all result says "for almost all N ∈ [X, 2X]": the summary rows, §2.2, §3.2, G2.3(1) and §10. **Minor m4:**
  - The §0 definition writes 𝓔(X), but every proof's exceptional set depends on H. Write 𝓔(X, H), with the bound uniform in H ∈ [X^a, X].
  - Add explicitly that simultaneity in H is **not** claimed and does not follow. Covering [X^a, X] by O(log X) dyadic H costs O(log X) · X (log log X)^{1+κ}/(log X)^κ, which is not o(X) for κ < 1.

### 3.5 G2.3 (window leading constants): **holds; Minor m1 in Part 2(b)**

- **h_q.** For an odd prime q dividing b, h_q(n) = 2^{v_q(c(n))} 1_{c(n)>0} is multiplicative. h_q(p) = 1_{c(p)>0}, since c(p) ≤ 2 is never divisible by an odd q. At prime powers, 2^{v} ≤ q^{v} ≤ c(p^e) ≤ e + 1 ≤ 2^e, which holds trivially for every e, not only for e ≤ 500. Shiu gives Σ h_q ≪ H (log N)^{δ−1} ✓. Markov at 2^{ελ} gives #{V_b > ελ} = o(S(N, H)) ✓.
- **Constants.** (1 + ω_b) κ = κ + δ log 2 matches GF-12, and ω_b ≤ 1 ⇔ δ ≤ 1/(1 + log 2) ✓. The (E1)–(E4) localization is at outline level but consistent.
- **m1 (Part 2(b) under GRH(q₀)).** The proof shifts Perron's integral to σ = 1/2 + 1/log N and invokes Littlewood's GRH **upper** bound for |L|. But F(s) = ∏_χ L(s, χ)^{a_χ} G(s) with a_χ = φ(q₀)^{−1} Σ_{r∈S} χ̄(r) complex. If Re a_χ < 0 for some χ, which happens for suitable unions of classes, one needs a **lower** bound for |L|. At distance 1/log N from the critical line, GRH gives only −log |L| ≪ (log t/log log t) · log log N ≍ log N for t ≈ √N, i.e. |L|^{−1} up to N^{O(1)}.
  - **Fix:** put the contour at σ₁ = 1/2 + c/log log N, where GRH gives |log L(σ₁ + it, χ)| ≪ log t/log log t uniformly. The error becomes N^{σ₁} exp(C log N/log log N) = √N exp(C′ log N/log log N), so the stated range is unchanged.
  - For the worked examples (χ₋₄, and `ex:quarter` with all a_χ = 1/4), every a_χ ≥ 0 and the original contour is fine.

### 3.6 G2.4A (second-moment Shiu halving): **conclusion holds; Major M1 in the proof**

- **Identity.** (1/φ(q)) Σ |1 + χ(r)|² = 2 + 2 Re φ(q)^{−1} Σ χ(r) = 2 ✓ (trivial). Shiu on |c_χ|² with Σ_{p≤N} |1 + χ(p)|²/p = 2 log log N + O(1) gives (Y/φ(q′)) log N ✓. Chebyshev then gives b^{2L} ≫ log N, i.e. L = log_b log N + O(1) ✓.
- **Stationary point and minimizer.** κ_t(∞) = 2^t Γ((t+1)/2)/(√π Γ(t/2 + 1)) and κ₂(∞) = 2 ✓. The derivative of log(κ_t/t) at t = 2 is log 2 + (1 − 2 log 2)/2 − 1/2 = 0 ✓, using ψ(3/2) − ψ(2) = 1 − 2 log 2. *Minor m3:* "global minimizer" needs one sentence. log κ_t = log E[X^t] is convex (Hölder) and −log t is convex, so a stationary point of log(κ_t/t) is the global minimum.
- **"α*(χ) < 1 for every h ≥ 2" is unproved** (m3). It is checked only by a float grid for h ∈ {2,…,7,12} (`C7`, `[finite]`). For h = ∞ the derivative at t = 2 is exactly 0, so finite-h strictness needs κ₂′(h) ≠ 1, i.e. an argument about the Riemann-sum error. Either prove it or state it as numerical for the listed h.
- **M1 (Major).** The proof defines R(u) = Σ_k |c_χ(Au + L + k)| b^{−k} (complex absolute value) and then applies Chebyshev to {C_Φ R(u) ≥ b^L/2}. This implicitly asserts |T_{Au+L}| ≤ C_Φ R(u), i.e. |Φ(z)| ≤ C_Φ |z| on ℤ[ζ_h] with C_Φ = max_j |Φ(ζ_h^j)|. **That inequality is false whenever φ(h) ≥ 4.** A ℚ-linear form on ℚ(ζ_h) is not controlled by one complex embedding.
  - **Counterexample (computed):** take h = 5 and Φ(a₀ + a₁ζ + a₂ζ² + a₃ζ³) = a₀, so C_Φ = 1. For n = p₁⋯p_k with χ(p_i) = ζ₅², c_χ(n) = (1 + ζ²)^k and |c_χ(n)| = 0.618^k. Yet |Φ(c_χ(n))| = 8, 89, 10946, 165580141 at k = 5, 10, 20, 40, while |c_χ(n)| = 9.0·10⁻², 8.1·10⁻³, 6.6·10⁻⁵, 2.1·10⁻⁸.
  - For h ∈ {3, 4, 6}, ℤ[ζ_h] is a lattice in ℂ and only the constant changes (for example 2C_Φ/√3 when h = 3). The headline cubic L_±(2) case is therefore unaffected apart from the constant.
  - **Repair.** Use |Φ(z)| ≤ C′_Φ max_σ |σ(z)| over σ ∈ Gal(ℚ(ζ_h)/ℚ), by the Minkowski embedding. Note that σ(c_χ(n)) = c_{χ^σ}(n). Then apply Cauchy–Schwarz and Shiu to each of the φ(h) multiplicative functions |c_{χ^σ}|². Each χ^σ is nonprincipal of order h, so κ₂(χ^σ) = 2 and L = log_b log N + O(1) survives.
  - **Consequences.** The constants d/log b in G2.1B(2) and G2.2C, and 2d/log b in G2.2B, are correct after the repair. So is the r = 2 branch of G2.2D. Also restate "for every nonprincipal χ" in the summary row.

### 3.7 G2.4B (CRT zero-block covering barrier): **covering lemma holds; Major M2 (scope) and Minor m5**

- **The covering lemma is correct.**
  - For odd h, d_p ≥ 3 and c_χ(p^e) = 0 ⇔ d_p | e + 1. So each killed offset needs p^{d_p−1} ≥ p² to divide m₀ + j ✓.
  - I_p lies in one class mod p^{d_p−1}, so |I_p| ≤ ⌊L/p²⌋ + 1 ✓, and primes p > √L kill at most one offset each ✓.
  - Small primes cover at most P_𝒫′(2) L + π(√L) offsets. Hence m ≥ (1 − P_𝒫′(2))L − π(√L) offsets need distinct large primes, each dividing Q to power d_p ≥ 3. So log Q ≥ d_min (1 − P − o(1)) L log L ✓. The C6 table is correct as a lower bound.
- **m5.** "For **any** integer L ≥ 1 … > L/2" holds only for L ≥ L₀. At L = 10, C6 itself gives exactly 5 = L/2, and the script guards with `if L >= 20`. Also, the "required" block length is phrased once as L ≥ α log_b log N and once as "to absorb a typical tail of size (log N)^{(log 2)/h}". The latter needs only L ≥ ((log 2)/h) log_b log N. State the barrier for L ≥ c log_b log N with any fixed c > 0.
- **M2 (Major, scope).**
  - The proof bounds the density 1/Q of **one** CRT residue class. The theorem then concludes that this blocks H/(log N)^C "by any single CRT congruence system **or any Paper-VI-style squarefree Selberg sieve**". §10 and the summary row strengthen this to "proving why neither Paper VI's Selberg sieve nor any CRT congruence system … can reach H/(log N)^C". Nothing in the proof addresses sieves or unions of classes.
  - **The stronger statement is true, and should be proved.** A union bound over *all* zero blocks gives density ≤ binom(L, m) (Σ_{p>√L} p^{−2})^m ≤ 2^L (2/(√L log L))^m = exp(−((1 − P_𝒫′(2))/2)(1 + o(1)) L log L). That is the density of {n : c_χ(n+1) = … = c_χ(n+L) = 0}, for any method. Add this as a lemma, for long windows or as a natural density; the +1 terms for primes above H^{ε} need the usual care. The exponent is weaker than the single-class exponent d_min(1 − P), so state both.
  - **Open Question 4(b) conflicts with this.** It asks whether "a non-CRT squarefull-covering inclusion–exclusion counting all zero blocks simultaneously" can reach H/(log N)^C. For L ≫ log log N the union bound above answers it negatively. Rephrase OQ4(b) to methods that avoid long zero blocks (for example a short block plus atypically small tail coefficients) or drop it.

### 3.8 G2.5: short-interval prime inputs in progressions: **attributions consistent**

- **Exponent arithmetic.** C4 is correct: 1 − 1/A and 1 − 2/A for A = 8/3, 5/2, 12/5, 7/3, 30/13, 2.
- **Guth–Maynard.** `arXiv:2405.20552v2` (v2 dated 2026-04-07; abstract read) has N(σ, T) ≤ T^{30(1−σ)/13+o(1)} and primes in intervals of length x^{17/30+o(1)}, both for ζ only, so q₀ = 1 ✓.
- **Chen–Gupta–Li.** `arXiv:2507.08296v2` (v2 dated 2026-07-27; authors Bin Chen, Vishal Gupta and Yung Chi Li; abstract read) has Σ_{χ mod q} N(σ, T, χ) ≪_ε (qT)^{7(1−σ)/3+ε}. The abstract says it "improves upon Huxley's earlier exponent of 12/5". This confirms the single-modulus exponent attribution to Huxley, but not the log-power form (see M3).
- **Other rows.** BHP 0.525 (q = 1 only), Kumchev 0.53 in progressions, PPS 7/12 and Jia 1/20 (q = 1) agree with the standard literature and with Paper VI's own audit. I did not re-read them in this review.
- **m6.**
  - The PPS (1985) row says it applies to GF-22 "via Huxley 12/5 + Khale 2024 in Theorem G2.2C". G2.2C does not use PPS; delete that clause.
  - The Huxley row is labelled `[S]` while §3.2 and §5 cite "Theorem 1" with a precise form. Make the reading label and the citation agree (M3).
  - Khale's "*Q. J. Math.* (2024)" and Guth–Maynard's "*Ann. of Math.* **203**(2)" have no `journal_ref` in arXiv metadata. I verified Khale's theorem text against arXiv v1 only, so mark the journal data `[S]` until checked.

---

## 4. G3: six-topic literature and provenance audit

| Topic | Assessment |
| --- | --- |
| 4.1 Mesoscopic local-limit theorems | **M4 (Major).** Matomäki–Radziwiłł, "Multiplicative functions in short intervals II", `arXiv:2007.04290`. Abstract read: "We determine the behavior of multiplicative functions vanishing at a positive proportion of prime numbers in almost all short intervals… an asymptotic for the number of integers that are sums of two squares in almost all short intervals." This is the sparse analogue relevant to Paper VI's support 1_{c>0}, a multiplicative function vanishing on the positive-proportion prime set 𝒬. For χ₋₄ that support is exactly the sums of two squares. The note's §4.1 cites only MR (2016) and says it "does not directly yield sparse (log X)^{−κ} asymptotics". Taken alone that is true, but with MR II and Hooley omitted it misleads. **Required:** cite MR II and Hooley. State that unconditional almost-all-window **support** asymptotics S(N, H) ∼ C_f H/(log N)^κ are available far below X^{1/6} (exact range to be checked in MR II). Position G2.2A and G2.2A′ as **word-count / isolated-planting** results. Revisit the almost-all clauses of G2.3(1)–(2): MR II may give the explicit GF-12 window constant for almost all windows at every fixed a > 0, unconditionally. That is a suggestion only; verify MR II's hypotheses first. |
| 4.2 Short-interval primes in progressions | Accurate apart from M3 and m6. Khale verified (§3.3). Le Duc Hieu `arXiv:2509.04883v2`: title and date ✓; "assisted by GPT-5" not checked. |
| 4.3 Generalized Lambert classifications (Mira Cult, Captain Sude) | Pins and the zero-contact / zero-endorsement wording are consistent with earlier phases. Not re-fetched. |
| 4.4 Badly approximable normal numbers | Consistent with Phase 25 H2/F2 and with the Phase 26 Audit IV caveats. |
| 4.5 Toeplitz / OPUC | The Szegő–Kolmogorov–Krein ratio 1 − γ for (1−γ)λ + γδ₀ is correct (exp ∫ log w with w = 1 − γ). D_m(δ_c) = 0 for m ≥ 2 ✓. The Simon theorem number is `[S]` and was not checked. *Minor:* "maximal-discrepancy elements x ∈ K_b (μ = δ_c)": membership in K_b does not force every weak* limit to be a Dirac mass. Say "if μ = δ_c". |
| 4.6 Padé/Hankel for ln 2 | **m8.** "Rukhadze (1987): μ(ln 2) ≤ 3.8921…" disagrees with the values usually cited, 3.893 (Rukhadze 1987) and 3.8913998 (Hata 1990). Recheck against the primary text. Rhin–Viola (1996, 2001) concern ζ(2) and ζ(3); the group method for ln 2 is Marcovecchio's (3.57455391 ✓). Say "method lineage". |

The methodological caveat in §4 ("no search proves priority… cross-model review is not independent human peer review… zero external contact") is present and adequate.

---

## 5. Consolidated findings

| ID | Severity | Location | Finding | Required action |
| --- | --- | --- | --- | --- |
| M1 | **Major** | §3.4 proof of G2.4A (R(u) definition and Chebyshev step); summary row G2.4A | \|Φ(z)\| ≤ C_Φ \|z\| is false for φ(h) ≥ 4 (counterexample h = 5: \|c_χ\| = 2.1·10⁻⁸ while \|Φ(c_χ)\| = 1.66·10⁸ at k = 40). For h ∈ {3,4,6} only the constant is wrong | Bound by max over Galois conjugates. Run Shiu on each \|c_{χ^σ}\|² (κ₂ = 2). The constants d/log b and 2d/log b survive |
| M2 | **Major** | §2.4 G2.4B last sentence; summary row G2.4B; §10 Objective 4; §9 OQ4(b) | The barrier is proved for one CRT class but claimed for sieves and unions. OQ4(b) is answered negatively by a union bound | Add the union-bound lemma (density ≤ exp(−((1−P)/2) L log L)), state the single-class and union exponents separately, restrict wording to zero-block methods with L ≥ c log log N, and fix OQ4(b) |
| M3 | **Major** | Lemma 3.2; proofs of G2.2A, G2.2C, G2.2D; §5 Huxley row; §3.5 table | Load-bearing zero-density input read only `[S]`. A log-power (or ε(1−σ)) form is essential near σ = 1; the ε-form breaks the high-β estimate | Primary-verify Huxley's statement (the hybrid (Q²T) form suffices), or split σ and use a log-free estimate (for example Jutila 1977) near σ = 1. Note that Khale's explicit constants are not needed. Apply the same repair to the 4/7 and 1/7 addenda |
| M4 | **Major** | §4.1; novelty framing of G2.2A, G2.2A′ and G2.3 almost-all clauses | Omits Matomäki–Radziwiłł II (`arXiv:2007.04290`) and Hooley: almost-all short-interval asymptotics for sparse multiplicative supports | Cite them, restate MR (2016) caveat, reposition G2.2A/A′ as planting/word-count results, and revisit the G2.3 almost-all ranges |
| m1 | Minor | §3.3 Step 4 (GRH) of G2.3(2b) | Contour at 1/2 + 1/log N needs lower bounds for \|L\| when some Re a_χ < 0 | Use σ₁ = 1/2 + c/log log N; the range is unchanged |
| m2 | Minor | Summary row G2.1B; §2.1 item 2; G2.1B(1) label; §10 | "Exact/sharp threshold" contradicts α* < 1; "unconditional impossibility" is a method barrier | Say "threshold of the t = 2 CRT method" and "method barrier" |
| m3 | Minor | §2.4 G2.4A last sentence; §3.4 | "α*(χ) < 1 for every h" unproved; "global minimizer" lacks the convexity argument | Prove it or label it numerical for the listed h; add the log-convexity sentence |
| m4 | Minor | §0 quantifier definition | 𝓔(X) should be 𝓔(X, H); simultaneity in H is not implied | Edit the definition and add the explicit disclaimer |
| m5 | Minor | §2.4 G2.4B statement | "> L/2 for any L ≥ 1" fails at L = 10; the required L is phrased inconsistently | Say "for L ≥ L₀" and use L ≥ c log_b log N |
| m6 | Minor | §3.5 G2.5 table | PPS row claims use in G2.2C; Huxley reading label conflicts with the citation; journal metadata unverified | Correct the table |
| m7 | Minor | Script C1, C2(3), C3, C4, C6(1); §8; G2.3 Step 2 | Tautological "exact" checks inflate the count; SHA checks are format-only; C5 is misattributed for g_t and z^ω | Relabel as consistency checks and correct the attribution |
| m8 | Minor | §4.6; §4.5 | Rukhadze value 3.8921 doubtful; Rhin–Viola relevance; K_b ⇒ δ_c overstated | Recheck and rephrase |
| n1 | Nit | §3.2 G2.2D prime powers | Missing log X factor | Insert it |
| n2 | Nit | Lemma 3.2 display | Truncation term not shown | Add it, or say it is absorbed |
| n3 | Nit | §7 | Runtime "≈ 1 s" (measured 0.26 s) | Optional |
| n4 | Nit | G2.1A Step 4 / C2 | Check stronger than needed; far tail never binding | State the < 0 condition and the C > −1 remark |

---

## 6. Recommendation

**REVISE.** After M1–M4 are addressed, and provided the Huxley/log-free input is primary-verified, I expect Track G to meet **ACCEPT WITH MINOR POLISH**. Until then:

1. **Registry.** Do not register G2.2C, G2.2D or G2.2A as unconditional `Paper proof` or `Lean-supported paper proof` until M3 is closed. Do not register G2.4B's sieve/union clause until M2 is closed. G2.1A, G2.2A′, G2.2B, G2.1B(2) and G2.3(2b) may be registered as `Conditional` (Dirichlet GRH or GRH(q₀) named, and the external formal proof noted as not human-reviewed). Constants that depend on G2.4A wait for M1, which is a one-paragraph repair.
2. **Benchmarks.** Zero status changes on `BC-01`…`BC-50` or `BF-*`. This agrees with the note and with Rules 1–4.
3. **Evidence separation.** The note keeps unconditional, GRH(q₀), Dirichlet-GRH, preprint (`[A]`) and finite (`[finite]`) material separate throughout. I found no conflation of almost-all windows with all windows.

*This review was produced by an AI model (Claude Opus 5.5, Anthropic). Cross-model review is not independent human peer review.*

---

## Post-Repair Verification

**Reviewer:** Claude Opus 5.5 (Anthropic) via Claude Code, the same cross-provider review sub-agent.
**Date:** 28 November 2026.
**Repaired files audited (uncommitted working tree, not modified by this check):** `notes/phase26/external-grh-and-lambert-windows.md` (816 lines, SHA-256 `e3571f9c…f7dccc6`) and `scripts/phase26_grh_windows.py` (910 lines, SHA-256 `89301c63…770ae34`).

> **Cross-model review is not independent human peer review.** This verification is a second pass by the same AI model that wrote the review above. It does not count as refereeing. It does not authorize a registry entry or a benchmark status change.

### Verdict: **ACCEPT** (all 4 Major, 8 Minor and 4 Nit findings closed; 2 new non-blocking nits)

I found no new mathematical error. Two citation and parameter nits (p1 and p2 in §D) are editorial and can be fixed in passing.

### A. Reproduction and exactness

| Check | Result |
| --- | --- |
| `python -B scripts/phase26_grh_windows.py` (Windows, Python 3.13.13, no WSL) | Exit code `0`. Output: `ALL 19101 CHECKS PASSED (18955 exact, 127 consistency, 19 finite)`. This matches the note's header, §6 and §7. |
| **Runtime type audit.** I wrapped `check_exact`, `check_consistency` and `check_finite`. On each call I scanned the locals of every calling frame up to `main`. | Observed 18,955 `[exact]` and 127 `[consistency]` calls. **Zero** `float` or `complex` locals appear in any calling frame, and every asserted condition is a `bool`. Floating point occurs only in `c7_finite_illustrations` (the 19 `[finite]` checks) and in the print formatting of `main`. |
| `C6` h = 5 code | `_mul_z5`, `_conj_z5` and `_tr_z5` correctly implement ℤ[ζ₅] = ℤ[x]/(1 + x + x² + x³ + x⁴). det(Tr(ζ₅^{i+j})) = 125. β_{Φ₀} = (1 − ζ₅)/5 and K_{Φ₀} = 2/5, which I rechecked by hand: Tr(β ζ^i) = δ_{i0}, and Σ_j \|1 − ζ^j\|²/25 = 10/25. The naive-failure certificate uses the rigorous bound \|1 + ζ₅²\|² = (3 − √5)/2 < 39/100, derived from 2.22² < 5. The values 8, 89, 10946, 165580141 are F₆, F₁₁, F₂₁, F₄₁. |

### B. Primary-source spot checks by this reviewer

- **Thorner–Zaman, `arXiv:2108.10878v2`.** I extracted the text from the PDF.
  - **Theorem 2.1** reads: "Let ε > 0. Let T ≥ 1, q ≥ 2, and 0 ≤ σ ≤ 1. We have the unconditional bound (2.1) N_q(σ, T) ≪_ε (qT)^{(12/5+ε)(1−σ)}". Here N_q := Σ_{χ mod q} N_χ, the sum over **all** characters mod q.
  - The proof says "(2.1) follows from the work of Huxley [5] and Jutila [7]". Reference [7] is M. Jutila, *On Linnik's constant*, *Math. Scand.* **41** (1977), 45–62.
  - **Remark 1.3:** if β₁ ≤ 1 − c₂/log q with c₂ independent of q, then Theorem 1.1 holds with λ = 1 and δ = 7/12.
  - The journal data (*Math. Z.* **306** (2024), no. 3, Paper No. 54, DOI `10.1007/s00209-023-03414-3`) matches the arXiv abstract page.
  - All of this agrees with the note's §3.2, §3.5 and §5.
- **Matomäki–Radziwiłł II, `arXiv:2007.04290v1`.** I extracted the text from the PDF.
  - The statement the note uses is **Corollary 1.1**. Let 𝒩 be a multiplicative subset satisfying condition **(2)** for some α > 0. Then there is κ = κ(α) > 0 such that, for all δ ∈ (0, 1/1000) and 2 ≤ h₀ ≤ X, the normalized count over (x, x + h₀ δ(𝒩; X)^{−1}] is within δ of the [X, 2X] mean, outside a set of ≪ X h₀^{−δ^κ} values x ∈ [X, 2X].
  - The quantifier "for all δ" makes the bound uniform in δ. The note may therefore choose δ₀(X) → 0.
  - Hooley's papers appear as [19] (*Acta Math.* **127**, 1971) and [20] (*J. Reine Angew. Math.* **452**, 1994), matching the note.
  - The arXiv record shows no journal reference, so the note's "preprint" label is correct.
- **Not re-read by me:** Jutila (1977), Theorem 1 itself (the note's `[R]` scan). The main theorems do not depend on it (see M3).

### C. Finding-by-finding status

| ID | Status | Evidence in the repaired note and script |
| --- | --- | --- |
| **M1** | **Closed** | §2.4 (G2.4A) and §3.4 Step 1 replace the false single-embedding bound by trace duality: Φ(z) = Tr(β_Φ z) = Σ_σ σ(β_Φ)σ(z). Cauchy–Schwarz then gives \|Φ(c_χ(n))\|² ≤ K_Φ Σ_σ \|c_{χ^σ}(n)\|² with K_Φ = Tr(β_Φ β̄_Φ). This identity uses that complex conjugation commutes with the abelian group G, which holds. Also σ(c_χ(n)) = c_{χ^σ}(n), and each χ^σ is nonprincipal of order h with κ₂(χ^σ) = 2. Shiu is run on each of the φ(h) functions, at a cost of the constant φ(h)K_Φ. The Step 2 Cauchy–Schwarz over k with the factor 1/(b − 1) is correct. The r = 2 branch of G2.2D (§3.2) also uses the Galois form. The h = 5 counterexample is stated and certified in `C6`. The constants d/log b and 2d/log b are intact. No new error. |
| **M2** | **Closed** | §3.4 Part 2 now contains Lemma 3.4. I re-derived it:<br>• Every n ∈ 𝒵_χ(L) has ≥ m(L) offsets, each needing a distinct prime p > √L with p² \| n + j.<br>• Subcase A (some p > Z = H^{1/(4m)}) contributes ≤ 2LH/Z + 2L√(N + H + L).<br>• Subcase B contributes ≤ H·binom(L, m)(Σ_{p>√L} p^{−2})^m + 2^L H^{1/4}.<br>• Σ_{p>y} p^{−2} ∼ 1/(y log y) gives the exponent −((1 − P)/2)(1 + o(1)) L log L.<br>The three applications are correct. Natural density follows. On long windows, a > 1/2 handles the √N term and Z ≥ exp(Ω(log N/log log N)). Almost-all windows follow from Markov, using the slack in o(1). The single-class and union exponents are stated separately, with the factor 2d_min between them. The wording is restricted to zero-block methods with L ≥ c log_b log N (summary row, §2.4, G2.1B(1), §10). OQ4(b) is rephrased to zero-block-free or short-block constructions. No new error. |
| **M3** | **Closed** | Lemma 3.2 and the proof of G2.2C now rest on Thorner–Zaman (2.1), and through them so do G2.2A and G2.2D. I read (2.1) in the primary text (§B). It is log-free in the required sense: ε multiplies (1 − σ).<br>**Route 1, rechecked:** put s = 1 − a + ε₀. Then (12/5 + ε₁)s < 2 − γ₁/2 in Lemma 3.2, and (12/5 + ε₁)s < 1 − γ₀/2 in G2.2C. After absorbing q′ = T^{o(1)}, the integrand is ≤ T^{−(γ₁/4)(1−σ)} (resp. U^{−(γ₀/4)(1−σ)}). The supremum at 1 − σ = η gives exp(−c(log T)^{1/3}(log log T)^{−1/3}), which beats every power of log T.<br>**Route 2 (σ-split at 4/5), rechecked:** [1/2, 4/5] gives T^{−γ₁/10} (resp. U^{−γ₀/10}). On [4/5, 1 − η], Jutila needs (2 + ε″)s < 2 (resp. < 1). With ε″ = 1/10 this holds iff a + 1 − 2/A > 2/11 (resp. a − 1/A > 1/16), which is true for A ∈ {12/5, 7/3}.<br>**Other repairs:** Khale's explicit constants are now marked non-essential, and the classical Vinogradov–Korobov shape is cited. The Huxley row is consistently `[S]`. The 4/7, 1/7, 17/30 and 2/15 addenda are segregated as preprint-dependent. G2.2C is framed as standard technique applied to the CRT moduli, with provisional priority. The M3 blocker in item 1 of my §6 no longer applies. |
| **M4** | **Closed** | MR II and Hooley are cited in the §2.2 positioning note, §4.1, §5, G2.3(1) and G2.3(2c). The MR (2016) caveat is restated. G2.2A and G2.2A′ are repositioned as word-count and R-isolated planting theorems.<br>**Proof of G2.3(2c), checked:**<br>• The support {c > 0} is a multiplicative subset.<br>• Condition (2) holds with α = 1/(2φ(q₀)), by Mertens in progressions.<br>• h₀ = Hδ(𝒩; X) ≥ X^{a/2}.<br>• δ₀ = (log log X)^{−1/(2κ)} gives an exceptional set ≤ X exp(−(a/2) log X (log log X)^{−1/2}) = o(X), uniformly in H.<br>• The main term (H/X)·#(𝒩 ∩ (X, 2X]) is ∼ C_f H/(log N)^κ.<br>The result is labelled "Preprint-input paper proof", separately from the published inputs. G2.3(1) uses Hooley (1994) only for the order of magnitude for χ₋₄, which suffices because Part 1 needs only S(N, H) ≫ H/(log N)^κ. The only defect is theorem numbering (nit p1). |
| m1 | Closed | G2.3(2b) moves the contour to σ₁ = 1/2 + c/log log N and uses the two-sided GRH bound for log L, which covers Re a_χ < 0. The range is unchanged. |
| m2 | Closed | The wording "threshold of the t = 2 CRT method" and "method barrier" is used in the summary row, §2.1, G2.1B(1) and §10. |
| m3 | Closed (strengthened) | The strict log-convexity sentence has been added. α*(χ) < 1 is now **proved** for every h ≥ 2, via f̂(n) = (−1)^n/(\|n\|(n² − 1)) and κ′₂(h) − 1 = 2 Σ_k f̂(kh). I rechecked the coefficients and the sign argument: the sum is positive for even h, and for odd h it is an alternating decreasing series with a negative sum. Also d/dt(κ_t/t) at t = 2 equals (κ′₂ − 1)/2 ≠ 0. |
| m4 | Closed | §0 now writes 𝓔(X, H), uniform in H, and adds an explicit simultaneity disclaimer with the O(log X) computation. |
| m5 | Closed | The note now uses the threshold L₀(χ), records m(10) = 5 and L₀ = 20 for cubic mod 7, and writes L ≥ c log_b log N throughout. |
| m6 | Closed | The PPS row now says "NOT used in Theorem G2.2C". Huxley is `[S]`, consistent with its citation through Thorner–Zaman. Khale's and Guth–Maynard's journal data are `[S]`. |
| m7 | Closed | 127 `[consistency]` checks are separated out (`C1`, `C2`(3), `C3` sanity, `C4` 62, `C6`(1)). §8 says the SHA checks are format-only. G2.3 Step 2 no longer cites `C5` for g_t and z^{ω}. |
| m8 | Closed | Rukhadze is now 3.8913998… with sources. Rhin–Viola is described as method lineage, and Marcovecchio is credited for ln 2. The §4.5 claim about K_b and δ_c is corrected. |
| n1 | Closed | The bound now reads O(Y√(A/X) log X). |
| n2 | Closed | The truncation and imprimitive terms are explicitly absorbed in Lemma 3.2. |
| n3 | Closed | Runtime ≈ 0.3 s (measured about 0.3 s). |
| n4 | Closed | G2.1A Step 4 states the < 0 condition and the C > −1 remark. `C2` checks both. |

### D. New non-blocking nits

- **p1 (citation numbering, MR II).** The note cites "Corollary 1", "condition (1.2)", "Theorem 1" and "Theorem 2 of MR II". In `arXiv:2007.04290v1` these are:
  - **Corollary 1.1** (the statement used);
  - condition **(2)**;
  - **Theorem 1.9** (the technical form);
  - **Theorems 1.4–1.5** (norm forms).

  These citations appear in the §2.2 positioning note, G2.3(1), G2.3(2c) and its proof, §4.1, §5, §6, §9 and §10. The mathematics is unaffected.
- **p2 (parameter remark).** In the general parenthetical of Lemma 3.2 ("any … A ≥ 2"), the fixed choice ε″ = 1/10 relies on "≥ 2/7". The same applies to G2.2C's "≥ 1/7". These hold for the A ∈ {12/5, 7/3} actually used, but not for every A ∈ [2, 7/3). There, take ε″ = ε″(a) small. The claim stays true, because s < 1 strictly.

### E. Recommendation

**ACCEPT.** M1–M4 are repaired, and I found no new error in the repairs. All Minor and Nit findings are closed.

- **Evidence labels.** The note's labels are now consistent with Rules 2–4:
  - G2.2A is `Lean-supported paper proof`, and G2.2C and G2.2D are `Paper proof`, all on published inputs (Thorner–Zaman 2024).
  - G2.3(2c) is a preprint-input result.
  - Every GRH-dependent result is `Conditional / External-GRH`, with `GRH(q_0)` or `Dirichlet GRH` named.
- **Registry decisions.** These remain with the repository owner.
- **Benchmarks.** Zero status changes on `BC-01`…`BC-50` or `BF-*`.

*This verification was produced by an AI model (Claude Opus 5.5, Anthropic). Cross-model review is not independent human peer review.*
