# Claim-to-source novelty ledger: Paper II, version 2.0

Status: provisional. No search establishes novelty, no specialist has reviewed any entry, and "apparently new in the sources examined" means only that the exact statement was not located. All external artifacts were read on 25 November 2026 at the pinned URLs below. Dates of public artifacts identify what was public; they do not settle historical priority.

## Sources read directly

| Artifact | Pin | What was read |
| --- | --- | --- |
| Mira, public gist "Normality research" (account Mira-acc) | [`d699a69c`](https://gist.github.com/Mira-acc/ea2791119de611279237096e35cbc976/d699a69c2037ee4420bfb8e1e0ad0b310bbc8eb0), created 2026-09-23 | Full text of note S09 (status line: "Working conventional proof, 22 September 2026 ... not an independently reviewed or formally verified paper. Literature priority has NOT been established"), the summary entries T28-T31, and the S07 summary T29. |
| Mira, public gist "Normality research #2" | [`41b5a780`](https://gist.github.com/Mira-acc/79be9a5d4aa54a9df41e702c4f3113ea/41b5a780f79f7bdd275cd96e7e310b000a897d35), created 2026-10-07 | The summary list of program results P01, P02, P08 and the statements of S07 Theorems 1.1, 1.2, 9.1 as quoted there. The proofs in S07 were not read. The archive states "no complete formal verification or independent referee audit is supplied". |
| Mira Cult, `Mira-Cult/math`, `stoneham-joint-normality.md` | [`357d26a2`](https://github.com/Mira-Cult/math/blob/357d26a23fbbee5c900098938744ab732b84d03a/notes/number-theory/normal-numbers/stoneham-joint-normality.md), commit dated 2026-11-24T20:54Z | Full text. The file's history in `notes/number-theory/normal-numbers` has no later commit as of 2026-11-25. The note says it "consolidates the conventional arguments in the earlier research archive, S07 and S09", makes no priority claim and is not formally verified. |
| Captain Sude, `xi-normality` | [`06961817`](https://github.com/CaptainSude/xi-normality/blob/06961817c7f61181ed9a5c73badb8d908d6ccdcc/paper/localized-logarithm-normality.tex) | Full `.tex` of "Binary normality of a localized logarithm" and README. Lean development not re-run. |
| Captain Sude, `xi-family` | [`f0f99121`](https://github.com/CaptainSude/xi-family/blob/f0f991216abd7fd5af9157f43281faca9671938a/paper/a-new-family-of-normal-numbers.tex), paper dated 10 September 2026 | Full `.tex` through the end of the proof of the rational-combination theorem. |
| Captain Sude, `stoneham-prime-support` | [`5919ad4e`](https://github.com/CaptainSude/stoneham-prime-support/blob/5919ad4ebec42e22f707f97b0471d03b8995f70b/paper/stoneham-prime-support.tex) | Full `.tex` and `PRIOR-ART-CHECK.md`. |
| Captain Sude, `Stoneham-sum-normal` | [`f4d3d1f0`](https://github.com/CaptainSude/Stoneham-sum-normal/tree/f4d3d1f01d00c57425c684409849053e58e42261) | Listing only. Concerns sums of two Stoneham numbers with different parameters; not otherwise relevant to Paper II. |
| Vandehey, J. Anal. Math. 138 (2019) | arXiv:1606.07911 | Statements of Corollary 1.2, Theorem 2.5 (= Bourgain, Theorem 8.28) and Theorem 7.4. Numbering is that of the arXiv text; the published numbering was not checked. |
| Bailey-Crandall, Exp. Math. 11 (2002) | author copy `bcnormal-em.pdf` | Corollary 4.9 (generalized Stoneham numbers), Theorems 4.6 and 4.8, Theorem 2.2, the discrepancy remark after Theorem 4.8 (log^2 N / sqrt N for m_i = c^i, n_i = i). |
| Dibag, J. Algebra 125 (1989) | Bilkent repository copy | Abstract, Definitions 1.1-1.2 (span of a set of primes, localization `L_S`). |
| Kano, Osaka J. Math. 30 (1993) | Osaka repository copy | Introduction and statement of Theorem 1 (OCR text; normality of `sum A_n / (a^{lambda_n} b^{mu_n})` for coprime `a,b` under growth and divisibility hypotheses). |

## Mira and Sude: statement-by-statement comparison

Notation: `M(S)` smooth numbers, `J` the set of support primes not dividing `b`.

| Public statement | Precise content | Relation to Paper II |
| --- | --- | --- |
| Mira S09 Theorem 1 (22 Sep 2026); T30; Mira Cult Theorem 2 (24 Nov 2026) | `S` finite nonempty, no prime of `S` divides `b`, every `s >= 1`: `sum_{m in M(S)} m^{-s} b^{-m}` is base-`b` normal. Proof: unique term with maximal `p_0`-adic denominator (`p_0 = min S`) plus a Korobov-type exponential sum bound (Lemma 3, via Weyl differencing). | Theorem A with `J = S` is this statement. **Inherited / overlapping discovery.** Theorem A adds supports with radix primes and the value 1 of the limit. |
| Mira S09 Theorem 2; T31; Mira Cult Theorem 1 | Finitely many distinct pairs `(p_i, s_i)`, `p_i` prime not dividing `b`: the vector `({b^n L_{p_i,s_i}(b)})`, `L_{p,s}(b) = sum_{k>=0} p^{-sk} b^{-p^k}`, is uniformly distributed; every nonzero rational combination (plus rational constant) is normal. | `L_{p,s}(b) = X_s` for `S = {p}`. Theorem C(i) with `S = {p}`, unit numerators, recovers the one-prime, several-orders case, and Laurent numerators give the rational combinations. **Overlap.** Theorem C does not cover joint distribution across different primes on different supports (Mira does). Theorem C covers fixed supports with several primes, radix primes in `S`, and numerators `P_i(m)` with arbitrary degree. |
| Mira S07 / T29; Mira Cult Theorem 3 | `S_{B,C,D} = sum_{j>=1} D^{-j} B^{-C^j}` is `B`-normal iff `D` has a prime divisor not dividing `B`. | Axis with unit weights and a full axis. Overlaps Theorem D(iii) only in the special case `K = N`, `P = 1`. Theorem D(iii) classifies every mask `K` and numerators of unrestricted degree. |
| Mira #2, S07 Theorems 1.1, 1.2, 9.1 (P02, P08) | Periodic rational arrays `A_k`: `sum_{k>=1} A_k p^{-sk} b^{-p^k}` is normal iff, at each phase `t mod D`, one of `C_{1,t},...,C_{s,t}` is nonzero; joint normality (also at mixed orders) iff a rational rank condition holds at every phase. Full axis only. | Proposition 6.3 is, in our reading, the `s = 1` scalar case. **Overlap; no priority claimed.** Equivalence of the tests not checked. Theorem C(ii) (arbitrary infinite masks, polynomial numerators) is a different class. |
| Sude `xi-normality`, Theorem 1.1 | `xi = sum_{a,c>=0} 1/(2^a 3^c 2^{2^a 3^c})`, i.e. `S = {2,3}`, `b = 2`, `s = 1`, is binary normal (Lean-verified, qualitative). | Special case of Theorem A. **Inherited.** |
| Sude `xi-normality`, Theorem 4.1 | `D_M(xi) << M^{-1/2} (log 2M)^3` for that `xi`. | Stronger rate than anything in Paper II for this support; Theorem F gives only `A/log log N` for a larger family. Paper II has no rate for general supports. |
| Sude `xi-normality`, Theorem 5.1 | `Lambda_P(b) = sum_{m in M(P)} 1/(m b^m)` is `b`-normal if (1) every prime of `P` is coprime to `b`, or (2) `b = 2` and `3 in P`. Paper proof only for this theorem. | Theorem A at `s = 1`, `J = S`, and for binary supports containing 3. **Inherited / overlapping discovery.** Not covered by 5.1: supports with a radix prime and `b != 2`, higher orders. |
| Sude `xi-family`, Theorem 1 (Lean-verified) | `a,b,c >= 2`, `gcd(c, ab) = 1`: `xi_{b,c;a} = sum_{m in {a^i c^k}} 1/(m b^m)` is `b`-normal. `a` may share primes with `b`. | With `{a, c}` the two primes of `S` and `c` off the radix, **Theorem A at order one on every two-prime support with an off-radix prime is already a consequence of this theorem** (version 1.1 did not cite it; this is corrected). It also gives normality in Theorem F (take `a = q`, `c = p`). Not covered: three or more generators at order one with a radix prime other than binary-with-3; orders `s >= 2` on mixed supports. |
| Sude `xi-family`, Theorem 2 (Lean-verified) | Rational combinations over distinct `c_j` (with `gcd(c_j, ab) = 1`) and a rational constant are normal. Lemma 4 ("denominator slope") covers periodic weights in the exponent of `c` and uses that equal-valuation terms are separated by a factor of at least `a`. | Different family (varying `c`, fixed `a`). Method note: the separation step fails for two or more cofactor primes, which is the case Theorem 4.1 of Paper II treats. |
| Sude `stoneham-prime-support` | For `b,c >= 2`: `alpha_{b,c} = sum_{k>=1} c^{-k} b^{-c^k}` is `b`-normal iff some prime dividing `c` does not divide `b`; otherwise the zero digit has frequency 1. | For prime `c` this is Theorem A with `|S| = 1`. **Overlap.** The full-axis composite case is outside Paper II. |

## Literature trail (earliest relevant, in order)

- Stoneham (1973), Acta Arith. 22, 277-286: `alpha_{b,c}` normal under `c` odd prime and `b` a primitive root of `c^2` (as reported in Bailey-Crandall's introduction; the article itself was not read).
- Korobov (1972), Math. USSR-Sb. 18, 659-676 (DOI verified; contents not read) and Kano (1993): constructions with varying numerators; Kano's Theorem 1 contains Korobov's case `A_n = 1` (Kano, Remark 1).
- Dibag (1989): localization `L_S` of `log(1+x)` at a set of primes (Definitions 1.1-1.2, p. 520, read).
- Bailey-Crandall (2002), Corollary 4.9(i): generalized Stoneham numbers `sum 1/(b^{m_i} c^{n_i})` for coprime `b, c`; Section 7 asks about replacing coprimality by mutual non-divisibility (answered negatively by Sude `stoneham-prime-support`).
- Bailey-Crandall (2001), Exp. Math. 10, 175-190: Hypothesis A, polylogarithmic constants (not used beyond context).
- Vandehey (2019): Corollary 1.2 (fixed-prime-support short-orbit bound), Theorem 7.4 (unit-numerator series on an infinite subset of a divisibility chain, gap condition `exp((1+eps) log c_k / log log c_k) = o(mu_k)`), Theorem 2.5 (Bourgain's Theorem 8.28, unbounded support).
- Bourgain (2008), J. Anal. Math. 106, 1-93 (Crossref record verified; Theorem 8.28 as restated in Vandehey).
- Wang, "Sparse polynomial-weighted expansions", arXiv:2606.24972 (read the abstract only): if `sum_{n in S} p(n) b^{-n}` is rational for a nonzero rational polynomial `p`, then `S` has positive lower density in long windows. A relation by subject (polynomial weights, sparse radix sums), not a comparison of results; Theorem B/D(iii) give normality, hence irrationality, for specific sparse supports.

## Headline theorems

### Theorem A: unsigned dichotomy (LS-01)
- **Statement and hypotheses:** `S` finite set of primes, `b >= 2`, `s >= 1`. `D_N(sum_{m in M(S)} m^{-s} b^{-m}) -> 0` if `J != empty`, `-> 1` if `J = empty`.
- **Evidence:** Kernel-verified. `unsigned_discrepancy_limit`, `unsigned_finite_support_normal`; mathlib-only statement checked in `Check.lean`.
- **Earliest relevant literature:** Stoneham (1973) and Bailey-Crandall (2002, Cor. 4.9(i)) for `|S| = 1`, `s = 1`; Dibag (1989) for the localized logarithm itself.
- **Closest published results:** Bailey-Crandall Corollary 4.9(i) (singleton, order one, up to the term `1/b`); Vandehey Theorem 7.4 (infinite subsets of one prime-power axis with a divisibility chain); Kano (1993) Theorem 1 (varying numerators on one axis).
- **Closest unpublished or public-repository results:** Mira S09 Theorem 1 / Mira Cult Theorem 2 (no radix primes, all `s`); Sude `xi-normality` Theorems 1.1, 5.1 (order one; no radix primes, or binary with 3); Sude `xi-family` Theorem 1 (two generators); Sude `stoneham-prime-support` (singleton axis, composite `c`).
- **Relation:** Strengthens the above by allowing radix primes in `S` for `|S| >= 3` at order one (except binary with 3) and for all orders on mixed supports, and by determining the limit (1) when `J` is empty for `|S| >= 2`. Specializes to / inherits the coprime and two-prime order-one cases (credited). Different method for `|S| >= 3` with radix overlap: recurrence on the logarithmic circle plus `p`-adic separation of rays (Theorem 4.1), in place of the equal-valuation separation used for two generators.
- **Search record:** "localized logarithm normality finite prime support", "localized polylogarithm normality smooth numbers", "normal numbers series restricted to integers with prime factors in a finite set Stoneham generalization", "sparse series 1/(m b^m) smooth numbers normal Li_s(1/b)", "Bailey Borwein Crandall polylogarithm constants normal"; general web search only (no direct zbMATH Open, MathSciNet or Google Scholar queries were possible); reference trails: Bailey-Crandall Sections 4 and 7, Vandehey Sections 1, 2 and 7, Kano's introduction, Sude's `PRIOR-ART-CHECK.md`. Nothing matching the statement for `|S| >= 3` with radix overlap was found.
- **Dependencies and outstanding review:** A specialist should check that no earlier statement for `|S| >= 3` mixed supports (for example in Korobov-Kano-type results for numerators supported on products of several generators) implies Theorem A, and the relation of the recurrence step to known multiplicative-recurrence arguments.

### Theorem B: rational polynomial weights (MW-01)
- **Statement and hypotheses:** as in the paper; pole criterion `r < s` and `J != empty`; failing cases nonnormal on every mask with `liminf D_N >= 1/L`.
- **Evidence:** Kernel-verified (the identification `L = D_0` is a written argument).
- **Earliest relevant literature:** Stoneham (1973); Kano (1993) for varying integer numerators on one axis.
- **Closest published results:** Kano Theorem 1 (integer numerators `A_n`, coprime `a, b`, growth and divisibility conditions on one axis).
- **Closest unpublished or public-repository results:** Mira S09 Theorem 2 / T31 and Mira Cult Theorem 1 (rational combinations of `L_{p,s}`, one prime); Sude `xi-family` (periodic weights in the exponent of `c`, `a >= 2`); Mira #2 S07 (periodic arrays on one axis).
- **Relation:** Apparently new in the sources examined for numerators `P(m)` of unrestricted degree on supports with `|S| >= 1`, including the failing-case lower bound `1/L` and the two limits equal to 2/3 (Example 5.1). Specializes to Mira's rational combinations when `S = {p}` and `P` has the form `sum c_j X^{t-j}`.
- **Search record:** as for Theorem A plus "rational polynomial weights normal numbers Stoneham sparse series", "Kano normal numbers Korobov type varying numerators".
- **Dependencies and outstanding review:** Same as Theorem A; plus whether Kano's Theorem 1 yields the axis case for integer-valued numerators `P(p^k)`.

### Theorem C: joint distribution at distinct orders (LS-09, MW-08)
- **Statement and hypotheses:** one support `S` with an off-radix prime, distinct positive orders, rational numerators `P_i(0) != 0`; box frequencies tend to the volume. (ii) single axis with common mask `K` iff `K` infinite. (iii) odd `b`, `2 in S`, late powers of 2.
- **Evidence:** Kernel-verified (`joint_full_polynomial_orders`, `joint_axis_orders_iff`, `joint_late_twos_orders`; mathlib-only statement of (i) in `Check.lean`). The unsigned case was a written corollary in version 1.1.
- **Earliest relevant literature:** Weyl (1916) criterion; Bailey-Crandall Theorem 2.2.
- **Closest published results:** none located for joint distribution on a fixed multi-prime support.
- **Closest unpublished or public-repository results:** Mira S09 Theorem 2 / Mira Cult Theorem 1 (one prime per coordinate, singleton supports, distinct `(p, s)`); Mira #2 S07 Theorems 1.2, 9.1 (periodic arrays on one axis, rank condition, mixed orders).
- **Relation:** Inherits the one-prime, several-orders case (Mira), and the single-axis unit-weight joint case at full mask. Different class otherwise: fixed multi-prime supports, radix primes in `S`, polynomial numerators, arbitrary infinite masks. The proof is the standard collection of a character into one scalar series; the new input is Theorem B.
- **Search record:** "joint normality several Stoneham numbers same base uniform distribution torus", "joint normality of localized polylogarithms distinct orders same support".
- **Dependencies and outstanding review:** the correspondence of `JointUniform` and `maskedValue` with the displayed statement (read, not machine-checked beyond `PaperII.jointPolynomial`).

### Theorem D: masks, windows and axes (MW-02, MW-03)
- **Statement and hypotheses:** as in the paper.
- **Evidence:** (i) Lean-supported paper proof; (ii), (iii) Kernel-verified.
- **Earliest relevant literature:** Vandehey Theorem 7.4 (unit numerators on infinite subsets of one axis with a chain/gap condition); Bailey-Crandall Theorem 4.8 (growth conditions on `m_k, n_k`).
- **Closest published results:** Vandehey Theorem 7.4 gives the unit-numerator axis statement for every infinite `K` (its gap condition holds on a prime-power axis, as computed in version 1.1: `c_i = p^{s k_i}`, `mu_i >= (1 - 1/p) p^{k_i}`).
- **Closest unpublished or public-repository results:** Mira T29 / Mira Cult Theorem 3 (full axis); Sude `stoneham-prime-support` (singleton axis).
- **Relation:** The axis classification for signed polynomial numerators of any degree and the window bound on multi-prime supports are apparently new in the sources examined; unit-numerator axis normality is inherited (Vandehey).
- **Search record:** as above plus "Stoneham series arbitrary subset exponents normal infinite set".
- **Dependencies and outstanding review:** the counting step in (i); equality of the density formula in Corollary 6.1 with the kernel's `periodic_mask_price`.

### Theorem E: computable common depth (LS-10)
- **Statement and hypotheses:** as in the paper (`p` off-radix, finite orders `T`, `epsilon` rational).
- **Evidence:** Kernel-verified; finite example by `scripts/localized_certificate.py`.
- **Earliest relevant literature:** none; this is a statement about the paper's own certificates.
- **Closest published/unpublished results:** none located.
- **Relation:** Apparently new, as a statement about the finite certificates only. It gives no cutoff in `N` (see Proposition 7.2).
- **Search record:** not searchable as a literature question beyond the searches above.
- **Dependencies and outstanding review:** none beyond the definition of the certificate.

### Theorem F: a rate on two-generator supports (LS-04)
- **Statement and hypotheses:** `q | b`, `p` odd prime, `p` not dividing `b`; `D_N <= A / log log N`.
- **Evidence:** Kernel-verified; the written outline is not the evidence.
- **Earliest relevant literature:** Sude `xi-normality` Theorem 4.1 (`O(M^{-1/2} (log 2M)^3)` for `b = 2`, `{2,3}`).
- **Closest unpublished results:** Sude `xi-family` Theorem 1 (normality for all `a, c` with `gcd(c, ab) = 1`).
- **Relation:** Normality is inherited (Sude). The rate is weaker than Sude's for `{2,3}` and covers a larger family (`q | b` composite, any odd prime `p`); apparently new only as a rate in that family.
- **Dependencies and outstanding review:** none beyond the Lean statement.

### Theorem 4.1: nullity of persistent failure (LS-03)
- **Statement and hypotheses:** `p in J`, `s >= 1`: the set `Z_{p,s}` has Lebesgue measure zero.
- **Evidence:** Kernel-verified.
- **Earliest relevant literature:** none located for the argument; recurrence of rotations on the circle is classical (Poincare); the density of multiples of `log_p r` modulo 1 is elementary.
- **Closest published / unpublished results:** Sude `xi-family` Lemma 4 (denominator slope), for two generators.
- **Relation:** Different method / apparently new in the sources examined for three or more generators; no search result proves this.
- **Search record:** "multiplicative recurrence logarithmic circle", "p-adic separation geometric progressions thresholds", "recurrence rotation measure positive zero set differences" (general web search; nothing relevant to this step was found).
- **Dependencies and outstanding review:** the specialist should check the recurrence step (return time chosen as a multiple of the eventual period), survival of the bare ray, and the separation restricted to rows at bounded distance.

### Proposition 6.3: signed periodic weights on one axis (MW-10)
- **Evidence:** Kernel-verified.
- **Closest results:** Mira #2 S07 Theorem 1.1 (periodic arrays, all orders).
- **Relation:** Overlaps (case `s = 1`); not claimed as new.

## Bibliography verification

| Entry | Checked against | Status |
| --- | --- | --- |
| Dibag 1989 | Crossref record (title, volume 125, number 2, pages 519-523); Bilkent repository copy (Definitions 1.1-1.2) | verified |
| Bailey-Crandall 2002 | Crossref; author copy (Cor. 4.9, Thms 4.6, 4.8, 2.2) | verified |
| Bailey-Crandall 2001 (cited in this ledger only) | Crossref | verified |
| Vandehey 2019 | Crossref; arXiv text (Cor. 1.2, Thm 7.4, Thm 2.5) | verified; theorem numbers are those of the arXiv text |
| Stoneham 1973 | Crossref (volume 22, number 3, pages 277-286) | metadata verified; contents not read |
| Kano 1993 | Osaka repository record (Osaka J. Math. 30(4), 909-919, DOI 10.18910/10356); Theorem 1 text (OCR) | verified; the Crossref API did not return this DOI |
| Korobov 1972 | Crossref | metadata verified; contents not read |
| Bourgain 2008 | Crossref | metadata verified; Theorem 8.28 only through Vandehey Theorem 2.5 |
| Sude `xi-normality`, `xi-family`, `stoneham-prime-support` | pinned repository files | verified at the pins; authors given only as the GitHub account name |
| Mira (two gists), Mira Cult | pinned gist revisions and commit | verified at the pins; authors given only as the account/author names on the artifacts |
| Wang, arXiv:2606.24972 (ledger only) | arXiv API abstract | abstract only |

No bibliography entry is marked unverified; the "contents not read" rows are cited only for the attributions stated in the paper.
