# Independent Review of Paper I: *Polynomial images of Stoneham numbers*

- **Reviewer:** Gemini 4 Neon (internal AI review)
- **Date:** 24 November 2026
- **Reviewed source commit:** `a9d9166e40aab0b9b85af0fdc9b967f87cd3b606` (verified unchanged in `papers/01-stoneham-polynomials/` at `HEAD` `6fd1442508a7ef22d87dd9e07d07ba156cf8244d`)
- **Pinned Lean checkpoints audited:** `a09e011720bc74396a27f4cb3ce2d8a5b3ce5035` and `afc35498a377fce8ce1d216e820990e54c7ba32c`
- **Scope:** `papers/01-stoneham-polynomials/` (`paper.pdf`, `paper.tex`, `REVIEW.md`, `CORRESPONDENCE.md`, `references.bib`, `check.lean`, `figures/`), all referenced `NormalityChecker` Lean modules, and primary bibliography checks. No manuscript files were modified; no other reviewer report was consulted.

---

## Overall Assessment

**Publication readiness: Minor-to-moderate revision (mathematically sound; needs targeted technical tightening, one rendered-PDF notation fix, bibliographic cleanup, and prose polishing before submission).**

The core mathematics is genuinely solid and original in mechanism. The orthant-numerator / compactness argument (Lemmas 3–5) is crisp, self-contained, and cleanly bridges $p$-adic valuation survival to short-orbit exponential sum cancellation. All 24 pinned Lean line citations in `paper.tex` and `CORRESPONDENCE.md` resolve to the claimed declarations at their pinned commits, the $j \ge 1$ indexing is consistent across the manuscript and all three Lean developments (via definitional equality and the verified reindexing $A(b,c,mc) = c\,\alpha_{b^m,c}$), and independent exact Python recomputations confirm the Lemma 3 example, the Theorem 7 square profile (including $R_{30}, R_{35}, R_{36}$ and the $k=3$ dip), Table 1 (all 16 counts, sum $4096$), and the Theorem 8 / Corollary 9 arithmetic.

No fatal mathematical errors were found. The required revisions fall into: (i) one broken mathematical symbol in the compiled PDF (`C(\R/\Z^d)`), (ii) small proof/statement precision gaps in Lemma 5, Corollary 6, Corollary 10, and Proposition 11, (iii) structural and bibliographic issues in Section 7 and `references.bib`, and (iv) internal repository/AI-meta phrasing leaking into mathematical prose.

---

## Findings by Severity

### Major

1. **Rendered torus notation bug in Corollary 6 proof (`paper.tex:18, 304`; `paper.pdf` p. 5, proof of Corollary 6, line 3)**
   - **Issue:** `\newcommand{\T}{\mathbb R/\mathbb Z}` lacks grouping, so `C(\T^d)` compiles in the PDF as $C(\mathbb{R}/\mathbb{Z}^d)$, which is syntactically ill-formed ($\mathbb{Z}^d$ is not a subgroup of $\mathbb{R}$).
   - **Fix:** Write `C((\R/\Z)^d)` or `C(\R^d/\Z^d)` (or define `\newcommand{\T}{\mathbb{T}}`).

2. **Internal review/repository meta-text inside the manuscript (`paper.tex:120-121, 181, 490, 539-550`)**
   - **Issue:** Several passages read as internal audit notes rather than research-paper prose:
     - p. 2, Section 1 ("Relation to earlier results", final sentence): *"Historical priority for polynomial images of the classical generators under the full hypotheses of Theorem 1 remains open for review."*
     - p. 3, Figure 1 caption: *"(theorem-derived)"*.
     - p. 8, Proposition 11 header: `Proposition 11 (Independent parameters, paper deduction).` (also inconsistent with Corollaries 9–10, which omit `"paper deduction"`).
     - p. 9, Table 2: unexplained internal IDs `ST-01`, `ST-02`, `ST-04`, `ST-05`, `ST-03`, `ST-06` listed out of numerical order and never defined in the text.
   - **Fix:** Replace the priority sentence with standard scholarly framing (e.g., *"To our knowledge, normality of nonlinear polynomial images of the classical constants (1) has not previously been established."*), delete `"(theorem-derived)"` and `", paper deduction"`, and drop or define the `ST-*` codes in Section 8.

3. **Unexplained logical redundancy in Section 7 (`paper.tex:442-517`; `paper.pdf` pp. 7–9)**
   - **Issue:** Corollary 9 proves transcendence of Theorem 1 values via Coons [3] and of $\alpha_{2,3}\alpha_{2,5}$ via Ridout [9]. Immediately afterward, Corollary 10 proves transcendence of all Theorem 2 values (which strictly include Theorem 1) using only Ridout [9], and Proposition 11 proves transcendence of $\alpha_{b,c}\alpha_{b,d}$ for all multiplicatively independent $c, d$ (strictly including $(3,5)$). The text never points out that Corollary 10 independently reproves the first half of Corollary 9 without Mahler's method, nor that Proposition 11 subsumes the second half.
   - **Fix:** Consolidate Section 7 or state the logical relationship explicitly (e.g., present Corollary 10 as the main one-axis transcendence result via Ridout, noting in a sentence that the univariate case also follows immediately from Coons [3, Appendix A]; and fold $\alpha_{2,3}\alpha_{2,5}$ into Proposition 11 as an explicit-exponent example with $\mu < 11/10$).

4. **Bibliography formatting and citation precision (`references.bib:1-70`; `paper.pdf` pp. 9–10)**
   - **Hidden links:** Nearly every entry prints bare anchor words (*"Publisher."*, *"Institutional copy."*, *"Fixed manuscript."*) with no visible DOI, URL, or arXiv ID. In print or offline PDF inspection, the identifiers disappear. Display the DOIs and arXiv IDs visibly.
   - **Missing author and punctuation typo in `[8]` (`twosum`):** Has no `author` field (prints anonymously under title) and renders `"9 September, 2026."` with a stray comma. Cite the author(s) of the manuscript or treat it consistently as a dated preprint with full attribution.
   - **Ridout citation `[9]` (`paper.tex:458-461`):** Cites Ridout (1958), *Mathematika* 5, 40–48 (*The $p$-adic generalization of the Thue–Siegel–Roth theorem*). While the 1958 $p$-adic theorem implies the $1+\varepsilon$ threshold via $\prod_{\ell \in S} |q|_\ell = q^{-1}$, the restricted-prime-denominator theorem itself is the main theorem of Ridout (1957), *Mathematika* 4, 125–131 (*Rational approximations to algebraic numbers*). Cite Ridout (1957) alongside or in place of (1958).
   - **Vandehey numbering `[11]`:** `REVIEW.md` cites Vandehey's 2016 arXiv preprint (`1606.07911`, §§1 and 7.2), whereas `paper.tex` cites the 2019 *Journal d'Analyse Mathématique* publication for `Corollary 1.2` and `Theorem 7.4`. Confirm that the published numbering matches the preprint.
   - **Stoneham companion paper `[10]`:** Stoneham (1973), *Acta Arith.* 22, 277–286 treats odd prime $c$ with $b$ a primitive root mod $c^2$ (including $\alpha_{2,3}$); citing the companion paper in the same volume (*Acta Arith.* 22, 371–389) would complete the historical record.

---

### Moderate

5. **Quantification gap between Lemma 5 and its use in Section 4 (`paper.tex:198-205, 256-257`; `paper.pdf` pp. 3–4)**
   - **Issue:** Lemma 5 states both $p^{dk-C} \mid \den(R_n(M))$ and $\den(R_n(M)) \mid p^{dk}$ only for $d \ge 1$ and $k = \lfloor \log_p n \rfloor \ge k_0$. Section 4 (p. 4) then asserts for every lower-degree term (which may have $d_\nu = 0$ or a different $k_0$) that its denominator divides $p^{(d-1)k}$.
   - **Evidence:** The upper divisibility $\den(R_n(M)) \mid p^{dk}$ holds trivially for all $n \ge 1$ and all $d \ge 0$ (as proved in `StonehamPolynomialPrefix.lean:110`, `denominator_dvd`). Also specify that $C \ge 0$ and $k_0 \ge 1$ are integers with $d k_0 \ge C$ so $p^{dk-C}$ is an integer.
   - **Fix:** Split the statement of Lemma 5: state $\den(R_n(M)) \mid p^{dk}$ for all $n \ge 1$ and $d \ge 0$, and $p^{dk-C} \mid \den(R_n(M))$ for $d \ge 1$ and $k \ge k_0$.

6. **Missing quantifiers in Theorem 2 (`paper.tex:77-82`; `paper.pdf` p. 1)**
   - **Issue:** Theorem 2 omits $s \ge 0$ and does not explicitly state that $M_1, \dots, M_s$ are monomials of the form (2) on the same radix $b$ and prime $p$.
   - **Fix:** Write *"let $s \ge 0$, let $M, M_1, \dots, M_s$ be monomials of the form (2) for these $b, p$ with $\deg M = d \ge 1$ and $\deg M_\nu < d$ for $1 \le \nu \le s$."*

7. **Collar overlap edge case in Corollary 6 proof (`paper.tex:306-311`; `paper.pdf` p. 5)**
   - **Issue:** The proof says to taper linearly across collars of width $\delta$ inside (for lower) and outside (for upper), adding *"A zero-length interval has lower bound zero; an interval of length one has upper bound one."* For any fixed $\delta > 0$, the interior collars already overlap whenever $0 < \ell < 2\delta$, and the exterior collars overlap on $\mathbb{R}/\mathbb{Z}$ whenever $1 - 2\delta < \ell < 1$.
   - **Fix:** Replace that sentence with: *"taking the constant function $0$ when $\ell \le 2\delta$ and the constant function $1$ when $\ell + 2\delta \ge 1$."*

8. **Notation clash in Corollary 10 proof (`paper.tex:475-486`; `paper.pdf` p. 8)**
   - **Issue:** The symbol $v$ is used simultaneously for the integer exponent in $m_i p^{-v}$ ($v \ge -1$, line 476) and for the right endpoint of the gap interval $[u, v] \subset (1, p)$ (lines 479, 484–485).
   - **Fix:** Rename the exponent to $r$ (i.e., $m_i p^{-r}$ with $r \ge -1$).

9. **Small-$k$ gap and implicit Weyl transfer in Proposition 11 (`paper.tex:499-510`; `paper.pdf` p. 8)**
   - **Issue:**
     1. Line 500 claims *"for a set of $k$ with bounded gaps there is $\ell \ge 1$ with $Q/P = d^\ell/c^k$ in the chosen interval."* When the chosen interval $[r_1, r_2] \subset (1/(d-1), c-1)$ has $r_1 < 1$ (e.g., $c=2, d=5$), small $k$ can produce $\ell \le 0$. This holds only for $k$ sufficiently large ($c^k r_1 \ge d$).
     2. Line 509 jumps from Equation (5) (an exponential sum bound) directly to *"uniform interval frequencies on that window"* without noting the Weyl/mesh transfer used in Theorem 8.
     3. Line 496 states $(c-1)(d-1) > 1$ without noting why $c=d=2$ is excluded (multiplicative independence forbids $c=d$).
   - **Fix:** Clarify *"for sufficiently large $k$ in a set with bounded gaps"*, note *"$c, d$ cannot both equal $2$"*, and write *"As in the proof of Theorem 8, equation (5) and Weyl's criterion give uniform interval frequencies on that window."*

10. **Why $p=2$ is excluded deserves an explicit remark (`paper.tex:154-156`; `paper.pdf` pp. 2–3)**
    - **Issue:** The proof of Lemma 3 notes $p - 1 > 1$ in passing, leaving a reader to wonder whether $p = 2$ is merely a proof artifact.
    - **Evidence:** It is a genuine obstruction to the bounded-loss method. For $p=2, d=2, e_1=e_2=1$, the upper set $U = \mathbb{N}_0^2 \setminus \{(0,0)\}$ (realized by $\alpha_{3,2}^2$ on $[3\cdot 2^{k-1}, 2^{k+1})$) has $K_U(z) = 2z - z^2$, so $K_U(2) = 0$ and $H_U(2) = 0$ in $\mathbb{Z}_2$. Exact arithmetic confirms that for $\alpha_{3,2}^2$ at $n = 3 \cdot 2^{k-1}$ ($k = 4, 5, 6, 7, 8$), $v_2(q_n) = k - 1$ instead of $2k - O(1)$ — losing $k+1$ powers of $2$ rather than $O(1)$. Adding a two-sentence remark after Lemma 3 or Lemma 4 would clarify the sharpness of the odd-prime hypothesis.

---

### Minor

11. **Small mathematical and typographical details:**
    - `paper.tex:250` (`paper.pdf` p. 4): An inline GitHub hyperlink (`formal orbit estimate` → `SmoothOrbit.lean#L207`) sits inside Section 4, whereas all other Lean links are confined to Section 8, and `SmoothOrbit.lean` is omitted from Table 2. Move the link to Section 8 / Table 2 (and note in Table 2 that the paper proof cites [11] while the Lean proof is self-contained).
    - `paper.tex:374` (`paper.pdf` p. 6): *"At $k=3$ the pair $(k, k-3)$ is absent because the index zero is excluded."* Should read *"the pairs $(3,0)$ and $(0,3)$ are absent because $i, j \ge 1$"* (both are needed to drop the degree-$3$ count from $4$ to $2$ and give $3 + 3\cdot 2 \equiv 0 \pmod 9$).
    - `paper.tex:406` (`paper.pdf` p. 7): *"choose a power $Q = 5^\ell$ in $[P/3, 5P/3)$"* — state $\ell \ge 1$ explicitly (holds for $k \ge 2$).
    - `paper.tex:427` (`paper.pdf` p. 7): *"For arbitrary large $N$"* → *"For arbitrarily large $N$"* (or *"For sufficiently large $N$"*).
    - `paper.tex:521-526` (`paper.pdf` p. 9): Splitting GitHub permalinks across two commits (`a09e011720bc` and `afc35498a377`, with the latter unpublished per `CORRESPONDENCE.md`) is fragile; pin Section 8 and Table 2 to a single published commit/tag before release.
    - `paper.tex:570-572` (`paper.pdf` p. 9): `"the project owner"` is repository language; replace with standard author-responsibility wording prior to submission.
    - `paper.tex:44-46` (`paper.pdf` p. 1, Abstract): Mentions transcendence only for $\alpha_{2,3}\alpha_{2,5}$, omitting Corollary 10 and Proposition 11.

---

## Verification of Core Technical Checkpoints

| Checkpoint | Result | Evidence |
| --- | --- | --- |
| Principal hypotheses ($b \ge 2$, odd prime $p \nmid b$, $e \ge 1$) | **Verified** | Exact match across Theorems 1–2, `StonehamStatements.lean:21-30`, and `StonehamPolynomial.lean:70,87,112`. Oddness of $p$ is genuinely needed for Lemmas 3–5 (verified $p=2$ collapse on $\alpha_{3,2}^2$). |
| First insertion $j = 1$ | **Verified** | `paper.tex:53`, `StonehamStatements.lean:14`, `StonehamPolynomial.lean:42`, `StonehamSquare.lean:28`, `ProductThreeFivePrefix.lean:15` all start at $j=1$; `check.lean:20-22` verifies definitional equality; Lean's $j \ge 0$ internal shift $A(b,c,mc) = c\,\alpha_{b^m,c}$ (`StonehamPolynomial.lean:44-64`) is exact. |
| Unique-leading monomial distinction | **Verified** | Lemma 5 gives denominator order $p^{dk - O(1)}$ independent of $m_i, e_i$. Thus two distinct maximal-degree monomials (e.g., $\alpha_{2,3}$ and $\alpha_{2,9}$, or $\alpha_{2,3}^2$ and $\alpha_{2,3}\alpha_{2,9}$) have equal pole order $p^{dk}$ and can cancel; strict top degree is essential for the ultrametric survival step. |
| Square exceptions (Theorem 7) | **Verified** | Exact Python check confirms all 7 initial intervals on $[0, 81)$, $R_{30} = 16952434/9$, $R_{35} = 542477888/9$, $R_{36} = 29293805954/243$, the $k=3$ dip on $[30,36)$, and $n^2 < 243 q_n$, $q_n \le n^2$ for $n \ge 81$. Matches `StonehamSquare.lean:251,305,310,316` and `square.csv` / Figure 2. |
| Joint Weyl (Corollary 6) | **Verified** (modulo `C(\R/\Z^d)` typo & collar overlap) | Distinctness and positivity of $r_i$ guarantee $\sum h_i X^{r_i}$ is nonconstant for $h \ne 0$; matches `StonehamJoint.lean:69-203` (`joint_uniform_powers`). Independent Python check confirms all 16 cells of Table 1 (`joint.csv`, sum $4096$). |
| $3,5$ upper bound vs normality (Theorem 8) | **Verified** | Separation $\ge 4P/15$, $[s-B, s+B) \subset [P, 44P/15] \subset [P, 3P)$, $44\cdot 81/15 = 237.6 < 238$, $32R - 4 \ge 2N/45$ for $R \ge 15$, yielding $D_\infty \le 43/45$ and irrationality. Paper accurately states that normality ($D_\infty = 0$) remains open and no positive lower bound is obtained. |
| Paper-only transcendence (Cor. 9–10, Prop. 11) | **Sound** (minor fixes needed) | Coons [3, App. A] applies to all $b, c \ge 2$. Ridout $1+\varepsilon$ threshold applies cleanly ($11/10$ in Cor. 9; compact-countable gap $[u,v] \subset (1,p)$ in Cor. 10; irrational rotation with bounded gaps and shared-prime resilience in Prop. 11). Fix $v$ clash in Cor. 10, small-$k$ $\ell \ge 1$ in Prop. 11, and Cor. 9/10/Prop. 11 redundancy. |
| Literature & novelty claims | **Reasonable, needs sharpening** | Correctly distinguishes Stoneham [10], A. N. Korobov [6], Bailey–Crandall [2], Wagner [12], Kano–Shiokawa [5] (growth conditions (15)–(16) fail for standard $\alpha_{b,c}$), N. M. Korobov [7], Vandehey [11] (Thm 7.4 requires unit numerators and divisibility chain), Bailey–Borwein [1, §4], and 2026 two-sum [8]. Note also that Mahler-method algebraic independence literature (Nishioka, Adamczewski–Faverjon) is relevant context for Section 7, though Ridout makes the paper's transcendence proofs far more elementary. |

---

## Prose and Exposition Audit (Exact Locations & Rewrites)

| Location | Verbatim Quote | Issue | Proposed Correction |
| --- | --- | --- | --- |
| p. 1, Abstract, lines 9–10 (`paper.tex:45-46`) | `"an upper bound of $43/45$ for the limiting upper binary interval discrepancy"` | Awkward double modifier ("limiting upper") | `"an upper bound of $43/45$ for the asymptotic binary interval discrepancy $D_\infty(\alpha_{2,3}\alpha_{2,5})$"` |
| p. 1, §1, para 1, lines 5–7 (`paper.tex:58-59`) | `"This counts overlapping words, including words with leading zeros. The half-open intervals select the terminating expansion at a radix rational."` | Stiff Lean-docstring phrasing | `"Equivalently, every length-$k$ base-$b$ word occurs in the terminating base-$b$ expansion of $x$ with asymptotic frequency $b^{-k}$."` |
| p. 1, §1, para 2, lines 1–2 (`paper.tex:68-69`) | `"The square and cube of $\alpha_{2,3}$ and the value $-\tfrac52\alpha_{10,9}^7+\alpha_{10,9}^2+\tfrac13$ are examples."` | Chatty/arbitrary toy example | Cut, or replace with a concise remark after Theorem 2 (e.g., $\alpha_{2,3}^2$, $\alpha_{2,3}^3$, and $\alpha_{2,3}\alpha_{2,9}$). |
| p. 1, §1, para 2, line 5 (`paper.tex:75`) | `"A monomial of degree zero has value one."` | Orphan sentence | Fold into the preceding sentence: `", with the empty product ($d=0$) equal to $1$."` |
| p. 1, §1, para 3, lines 2–3 (`paper.tex:85-86`) | `"The strict degree inequality in Theorem 2 controls cancellation after the monomials have been evaluated."` | Imprecise ("after evaluation") | `"The uniqueness of the maximal-degree monomial prevents cancellation of the leading $p$-adic pole in the rational prefixes."` |
| p. 2, §1 "Relation...", para 2, lines 6–9 (`paper.tex:106-108`) | `"The older results establish polynomial normality for explicit families. Joint normality also occurs in N. M. Korobov's work on conjunctly normal numbers [7]. Here the coordinates are powers of the specified values in (1)."` | Choppy, templated transitions | `"While those constructions produce specially lacunary rings of normal numbers—and N. M. Korobov [7] studied conjunctly normal vectors—Theorems 1--2 and Corollary 6 apply directly to the classical constants (1) and their powers."` |
| p. 2, §1 "Relation...", para 3, lines 5–6 (`paper.tex:115`) | `"Bailey and Borwein posed a different question about a sum of two standard constants [1, §4]."` | Vague ("a different question") | `"Bailey and Borwein [1, §4] asked whether sums of two Stoneham constants are normal."` |
| p. 2, §1 "Relation...", para 3, lines 9–11 (`paper.tex:120-121`) | `"Historical priority for polynomial images of the classical generators under the full hypotheses of Theorem 1 remains open for review."` | Internal review meta-commentary | `"To our knowledge, normality of nonlinear polynomial images of the classical Stoneham constants (1) has not previously been established."` |
| p. 3, §2, Lemma 3 proof, lines 2–4 (`paper.tex:154-156`) | `"The alternating binomial sum at one equals $1$. ... This proves the assertion even when $p$ divides $K_U(p)$."` | Slightly informal ("at one") and defensive | `"Evaluating (3) at $z=1$ gives $K_U(1) = \sum_{r=1}^s (-1)^{r+1}\binom{s}{r} = 1$. ... Hence $H_U(p) \ne 0$ in $\mathbb{Z}_p$ (even when $p \mid K_U(p)$, as in the example below)."` |
| p. 3, Fig. 1 caption (`paper.tex:181`) | `"Reflected insertion lattice at the cut $10/9$ (theorem-derived)."` | Internal provenance tag | `"The reflected upper set $U = \{(i,j) \in \mathbb{N}_0^2 : 3^{-i} + 3^{-j} \le 10/9\}$; circled points mark its minimal vectors."` |
| p. 3, §3, para 1, line 1 (`paper.tex:188`) | `"For a monomial (2) use the original positive indices"` | Internal allusion to Lean reindexing | `"For a monomial $M$ as in (2) and $j = (j_1,\dots,j_d) \in \mathbb{Z}_{\ge 1}^d$, set"` |
| p. 4, §3, Lemma 5 proof, line 15 (`paper.tex:223-224`) | `"The positive lower index therefore removes no contributing tuple."` | Awkward phrasing | `"Hence the restriction $j_i \ge 1$ omits no tuple contributing modulo $p^L$."` |
| p. 4, §4, Thm 2 proof, lines 6–7 (`paper.tex:261-262`) | `"Consequently $q_n = \den(R_n(x))$ tends uniformly to infinity at late positions"` | Redundant/ill-posed ("uniformly" for 1D sequence) | `"Consequently $q_n = \den(R_n(x)) \to \infty$ as $n \to \infty$"` |
| p. 5, §4, Thm 2 proof, line 7 (`paper.tex:275-276`) | `"proves vanishing for every $N \to \infty$."` | Unidiomatic | `"shows that $\frac{1}{N}\sum_{n=0}^{N-1} \exp(2\pi i h b^n x) \to 0$ as $N \to \infty$."` |
| p. 5, Table 1 caption (`paper.tex:318`) | `"Exact finite illustration for $\alpha = \alpha_{2,3}$."` | Templated label | `"Simultaneous two-bit prefix counts for $\{2^n \alpha\}$ and $\{2^n \alpha^2\}$ over $0 \le n < 4096$ ($\alpha = \alpha_{2,3}$)."` |
| p. 6, §6, para 1, line 4 (`paper.tex:394`) | `"Endpoints $a=0$ and $c=1$ are allowed."` | Redundant with $0 \le a < c \le 1$ right above | Cut sentence. |
| p. 7, Fig. 2 caption (`paper.tex:381-383`) | `"Exact finite computation of the square denominator through $n=242$."` | Templated label | `"Exact values of $v_3(q_n)$ for $0 \le n \le 242$, computed from the recurrence in Theorem 7."` |
| p. 7, §6, Thm 8 proof, line 23 (`paper.tex:427`) | `"For arbitrary large $N$"` | Grammatical error | `"For sufficiently large $N$"` |
| p. 7, §6, para after Thm 8 (`paper.tex:437-438`) | `"The estimate leaves full binary normality of this product open. It also gives no positive lower bound for $D_\infty(x)$."` | Choppy two-sentence coda | `"Theorem 8 leaves open whether $\alpha_{2,3}\alpha_{2,5}$ is binary normal (that is, whether $D_\infty(x) = 0$)."` |
| p. 8, §7, Prop. 11 header (`paper.tex:490`) | `Proposition 11 (Independent parameters, paper deduction).` | Audit tag in theorem title | `Proposition 11 (Independent parameters).` |
| p. 9, §8, para 3, line 5 (`paper.tex:566`) | `"No finite digit count is used to deduce a limit."` | Defensive/templated | Cut (or move to Table 1 caption as `"These counts are purely illustrative."`). |
| p. 9, §8, Preparation (`paper.tex:570-572`) | `"rest with the project owner."` | Internal repo jargon | Replace with author name(s) prior to submission. |

---

*Signed: Gemini 4 Neon*
