# Independent Referee Report: *Disjunctive but Nonnormal Multiplicative Lambert Series* (Version 1.0)

- **Reviewer model:** Gemini 4 Argon, Antigravity
- **Date:** 2026-11-25
- **Reviewed commit:** `dedc430` (`dedc4302b1f68576f8adfcdde28c5d3642d03d22`; pinned Lean checkpoint `e4809cf561573aef588e6ffc491a35cdb79fd9ec`)
- **Review status:** AI model review; not independent human peer review

---

## Verdict

**Accept with minor revisions.**

The manuscript *Disjunctive but Nonnormal Multiplicative Lambert Series* (v1.0) is a clear, self-contained, and carefully scoped paper establishing two-sided moving-window binary word counts (`Theorem A`, `paper.tex:120-132`), base-2 disjunctivity and non-normality (`Corollary 1.1`, `paper.tex:134-140`), the exact asymptotic order of the extreme discrepancy gap $1 - D_N(L) \asymp (\log\log N)/(\log N)^{1-\delta}$ (`Theorem B`, `paper.tex:142-148`), the resulting sharp worst-case discrepancy translation rate (`Corollary 1.2`, `paper.tex:154-161`), and transcendence for odd Dirichlet characters, primitive or imprimitive (`Theorem C`, `paper.tex:168-174`).

All five audit areas pass verification:

1. **Primary-source and bibliography audit:** Every external theorem used in the proofs—Shiu (1980, Theorem 1, p. 163), Perelli–Pintz–Salerno (1985, Theorem, p. 2), Montgomery–Vaughan (1973, Theorem 2, (1.10), p. 121), Montgomery–Vaughan (2007, Theorem 2.7), Davenport (1980, Chs. 1 and 4), Halberstam–Richert (1974, Ch. 3), Hamieh–Murty (2016, Theorem 1.1, p. 766 and Theorem 3.1, p. 771), Nesterenko (1996), Diamond–Shurman (2005, §§4.5–4.8), and Wirsing (1961, Satz 1, p. 76, cited only in a remark for unions of residue classes)—matches the printed primary source in theorem number, page number, and hypotheses. None of the 22 bibliography entries in `references.bib` is invented.
2. **Novelty, antecedents, and priority language:** Extensive searches across arXiv, zbMATH Open, Google Scholar, and public GitHub repositories/gists (`CaptainSude` and `Mira-Cult` / `Mira-acc`) uncovered no prior work establishing two-sided moving-window word counts, base-2 disjunctivity with zero one-digit frequency, or the exact discrepancy gap $(\log\log N)/(\log N)^{1-\delta}$ for sparse multiplicative Lambert series such as $L_{\chi_4} = \frac{1}{4}(\theta_3(1/2)^2 - 1)$. All priority language is properly qualified (`paper.tex:254-257`, `LEDGER.md:3`).
3. **Lean 4 correspondence and evidence labels:** Every `\lean{File}{line}{label}` link in `paper.tex` (`lines 316, 414, 449, 836, 838, 848, 890, 906, 907, 911, 1046-1063`) and every link in `VERIFICATION.md` points to the exact line of the corresponding declaration at commit `e4809cf561573aef588e6ffc491a35cdb79fd9ec`. No analytic theorem is labelled `Kernel-verified`; the main theorems are accurately labelled `Lean-supported paper proof` or `Paper proof`, with `Kernel-verified` restricted strictly to finite inequalities and identities valid for every real number (`paper.tex:274-285, 1039-1074`).
4. **Presentation and build:** Building with `wsl -d Ubuntu -- bash papers/wsl-build.sh 06-multiplicative-lambert` succeeds with exit code 0 (18 pages, zero undefined references or citations, and zero overfull or underfull boxes). The main theorems are stated up front with precise hypotheses `(H1)–(H4)` (`paper.tex:72-84`), all notation is defined before use, and the body is free of repository jargon. (Note that the tracked `paper.pdf` at `dedc430` predates the shared byline commit `6ad4d2c` and needs to be refreshed; see Finding 1.)
5. **Submission package:** All six files in `submission/` (`abstract.txt`, `alphaxiv.md`, `announcement.md`, `summary.md`, `reviewer-inquiry.md`, `reviewer-packet.md`) are accurate, nonpromotional, compliant with word and character limits, carry the required authorship and AI-use disclosures, and target directly relevant specialists with accurate citations.

No critical or major issues were found. Detailed task audits and numbered minor and editorial findings follow.

---

## Task 1: Primary-Source and Bibliography Audit

Every external theorem in `paper.tex` and every entry in `references.bib` (`lines 1-235`) was checked against primary sources and publisher/Crossref records:

| Source (`references.bib` key) | Citation in `paper.tex` | Primary-source verification |
| --- | --- | --- |
| **Shiu 1980** (`Shiu1980`, `lines 5-13`) | `lines 375, 384, 462-473` | P. Shiu, *A Brun–Titchmarsh theorem for multiplicative functions*, J. Reine Angew. Math. **313** (1980), 161–170, `doi:10.1515/crll.1980.313.161`. **Theorem 1** is on **p. 163**; class $M$ ($f \ge 0$ multiplicative, $f(p^l) \le A_1^l$, $f(n) \le A_2(\epsilon)n^\epsilon$) is defined on **p. 162**; condition (1.1) on **p. 161** specifies $0 < a < k$, $\gcd(a,k)=1$, $0 < \alpha,\beta < 1/2$, $k < y^{1-\alpha}$, $x^\beta < y \le x$. Because $0 < a < k$ excludes $k=1$, Lemma 3.1 (`paper.tex:377-395`) properly factors $m = 2^e v$ ($v$ odd) and applies Theorem 1 to $U(v)$ with $k=2, a=1, \alpha=1/4, \beta=\sigma/4$. |
| **Wirsing 1961** (`Wirsing1961`, `lines 15-23`) | `lines 818-821` | E. Wirsing, *Das asymptotische Verhalten von Summen über multiplikative Funktionen*, Math. Ann. **143** (1961), 75–102, `doi:10.1007/BF01351892`. **Satz 1** is on **p. 76** and requires $\sum_{p\le x} f(p) \sim \tau x/\log x$. Unlike the earlier development note, `paper.tex:818-821` invokes Wirsing only as an optional remark when $S$ is a union of residue classes (where the PNT in progressions supplies the prime-counting hypothesis), and proves Proposition 6.1 (`paper.tex:804-816`) under `(H1)–(H4)` directly from Lemma 3.1 and Proposition 5.3 without Wirsing. |
| **Perelli–Pintz–Salerno 1985** (`PPS1985`, `lines 25-33`) | `lines 475-487, 513-521, 993-1005` | A. Perelli, J. Pintz and S. Salerno, *Bombieri's theorem in short intervals. II*, Invent. Math. **79** (1985), 1–9, `doi:10.1007/BF01388653`. The **Theorem** on **p. 2** proves estimate (1.1) (stated on **p. 1**) for $y = x^\theta$, $7/12 < \theta \le 1$, and $Q = x^{1/40}$, with maxima over $(a,q)=1$, $h \le y$, and $x/2 < z \le x$. Theorem 4.2 (`paper.tex:475-482`) reproduces this statement accurately, and Lemma 4.4 (`paper.tex:504-521`) uses only the single modulus $q = q_0 \le (X+Y)^{1/40}$. |
| **Huxley 1972** (`Huxley1972`, `lines 35-43`) | `lines 484-485` | M. N. Huxley, *On the difference between consecutive primes*, Invent. Math. **15** (1972), 164–170, `doi:10.1007/BF01418933`. Cited accurately as the source of the short-interval exponent $7/12$. |
| **Montgomery–Vaughan 1973** (`MontgomeryVaughan1973`, `lines 45-53`) | `lines 488-493, 746-751` | H. L. Montgomery and R. C. Vaughan, *The large sieve*, Mathematika **20** (1973), 119–134, `doi:10.1112/S0025579300004708`. **Theorem 2, (1.10)** on **p. 121** states $\pi(x+y; k, l) - \pi(x; k, l) < 2y/(\varphi(k)\log(y/k))$ for $(k,l)=1$ and $y > k$. Applied in Proposition 5.3 (`paper.tex:746-751`) with $k = d' \le 2\sqrt{N} \le Y^{7/8} < Y$ (valid since $(a-\theta)\cdot\frac{7}{8} > \frac{7}{12}\cdot\frac{7}{8} > \frac{1}{2}$) and nonunit residues excluded because $p > X > 2\sqrt{N} \ge d'$. |
| **Montgomery–Vaughan 2007** (`MontgomeryVaughanBook`, `lines 55-64`) | `lines 495-500` | H. L. Montgomery and R. C. Vaughan, *Multiplicative Number Theory I. Classical Theory*, Cambridge Studies in Advanced Mathematics **97**, Cambridge Univ. Press, 2007, `doi:10.1017/CBO9780511618314`. **Theorem 2.7** (Ch. 2) gives the three Mertens estimates in `(3)` (`paper.tex:496-500`). |
| **Davenport 1980** (`Davenport`, `lines 66-77`) | `line 188` | H. Davenport, *Multiplicative Number Theory*, 2nd ed., GTM **74**, Springer-Verlag, 1980, `doi:10.1007/978-1-4757-5927-3`. Chapters 1 and 4 supply $\sum_{p\le x}\chi(p)/p = O(1)$ for nonprincipal $\chi$. |
| **Halberstam–Richert 1974** (`HalberstamRichert`, `lines 79-87`) | `lines 566-627` | H. Halberstam and H.-E. Richert, *Sieve Methods*, LMS Monographs **4**, Academic Press, 1974. Chapter 3 is cited for background on Selberg's upper-bound sieve, while Lemma 4.7 (`paper.tex:569-627`) gives a complete self-contained proof. |
| **Hamieh–Murty 2016** (`HamiehMurty2016`, `lines 89-98`) | `lines 176-178, 267, 283, 933-984` | A. Hamieh and M. R. Murty, *A note on $q$-analogues of Dirichlet $L$-functions*, Int. J. Number Theory **12** (2016), no. 3, 765–773, `doi:10.1142/S1793042116500494`. **Theorem 1.1** (**p. 766**) proves transcendence of $L_q(k,\chi)$ for primitive $\chi$ with $\chi(-1)=(-1)^k$ and algebraic $q = e^{2\pi i\tau}$ ($0 < |q| < 1$); **Theorem 3.1** (**p. 771**) proves transcendence of $f(\tau)$ for any nonzero modular form $f$ of level $N$ and weight $k$ with algebraic Fourier coefficients when $e^{2\pi i\tau}$ is algebraic; **§2 (p. 769)** gives the weight-1 Eisenstein series $E_{1,\chi^*}$, and **p. 767** notes that $\chi(-1) \ne (-1)^k$ is open. All locations and statements match `paper.tex:933-984`. |
| **Nesterenko 1996** (`Nesterenko1996`, `lines 100-109`) | `lines 205, 265, 946` | Yu. V. Nesterenko, *Modular functions and transcendence questions*, Sb. Math. **187** (1996), no. 9, 1319–1348, `doi:10.1070/SM1996v187n09ABEH000158`. Verified. |
| **Duverney et al. 1996** (`DNNS1996`, `lines 111-119`) | `line 206` | D. Duverney, Ke. Nishioka, Ku. Nishioka and I. Shiokawa, *Transcendence of Jacobi's theta series*, Proc. Japan Acad. Ser. A Math. Sci. **72** (1996), no. 9, 202–203, `doi:10.3792/pjaa.72.202`. Metadata and mathematical claim (transcendence of $\theta_3(q)$ for algebraic $0<|q|<1$ via Nesterenko's theorem, Theorem 1 / Corollary on p. 202) verified. See Finding 3 on reconciling the `unverified` note between `LEDGER.md:45` and `references.bib:111-119`. |
| **Diamond–Shurman 2005** (`DiamondShurman`, `lines 121-130`) | `line 959` | F. Diamond and J. Shurman, *A First Course in Modular Forms*, GTM **228**, Springer, 2005, `doi:10.1007/978-0-387-27226-9`. Sections 4.5–4.8 cover Eisenstein series on $\Gamma_1(N)$ and weight 1. |
| **Erdős 1948** (`Erdos1948`, `lines 132-140`) | `lines 59, 239` | P. Erdős, *On arithmetical properties of Lambert series*, J. Indian Math. Soc. (N.S.) **12** (1948), 63–66 (`https://users.renyi.hu/~p_erdos/1948-04.pdf`). Verified. |
| **Borwein 1992** (`Borwein1992`, `lines 142-150`) | `line 240` | P. B. Borwein, *On the irrationality of certain series*, Math. Proc. Cambridge Philos. Soc. **112** (1992), 141–146, `doi:10.1017/S030500410007081X`. Verified. |
| **Bailey–Crandall 2001** (`BaileyCrandall2001`, `lines 152-160`) | `line 59` | D. H. Bailey and R. E. Crandall, *On the random character of fundamental constant expansions*, Experiment. Math. **10** (2001), 175–190, `doi:10.1080/10586458.2001.10504441`. Metadata verified; see Finding 2 on citing Bailey–Crandall (2002) / Crandall (2012) for the Erdős–Borwein normality question. |
| **Crandall 2012** (`Crandall2012`, `lines 162-169`) | `line 241` | R. Crandall, *The googol-th bit of the Erdős–Borwein constant*, Integers **12** (2012), A23, `doi:10.1515/integers-2012-0007`. Verified; see Finding 2 on adding `pages = {A23}`. |
| **Campbell 2026** (`Campbell2026`, `lines 171-179`) | `lines 61, 242` | J. M. Campbell, *On the binary digits of the Erdős–Borwein constant*, `arXiv:2605.24160` [math.NT] (2026). Verified. |
| **Bell–Bruin–Coons 2012** (`BellBruinCoons2012`, `lines 181-189`) | `lines 268-270` | J. P. Bell, N. Bruin and M. Coons, *Transcendence of generating functions whose coefficients are multiplicative*, Trans. Amer. Math. Soc. **364** (2012), 933–959, `doi:10.1090/S0002-9947-2011-05479-6`. Verified. |
| **Calude–Priese–Staiger 1997** (`CaludePrieseStaiger1997`, `lines 191-199`) | `lines 260-261` | C. S. Calude, L. Priese and L. Staiger, *Disjunctive sequences: an overview*, CDMTCS Research Report **63**, Univ. of Auckland, 1997 (also Bull. EATCS **63** (1997), 136–167). Marked `note = {unverified...}` in `references.bib:198` and listed in `LEDGER.md:23, 84` in compliance with `WAVE2-CONTRACT.md:43`. |
| **Captain Sude 2026** (`SudeDisj`, `SudeElem`, `lines 201-217`) | `lines 61, 242-244` | `CaptainSude/erdos-borwein-disjunctivity` at `bd98789a177470cc4b3e33e6769e859f6144c906` (tag `v1.0.0`, conditional Lean proof `binaryDisjunctive_lambertE` and paper bound $N\exp(-C_w(\log\log N)^3)$) and `CaptainSude/erdos-borwein-disjunctivity-elementary` at `d51e93e91ff43efef6918efdd4258bbd43bad7aa` (unconditional Lean proof with prefix count $\ge N\exp(-70000(\log\log N)^3)$). Verified. |
| **Mira Cult 2026** (`MiraCult`, `lines 219-226`) | `lines 61, 245-246` | `Mira-Cult/math` at `149831943806a656c9efaa14cacbd9c915b2a2ba`, `notes/number-theory/normal-numbers/erdos-borwein-positive-word-density/README.md` (Claim 0002, lower bound $\ge c_{a,w}H$ in windows $[N, N+H)$ for $N^a \le H \le N$, $7/12 < a \le 1$). Verified. |
| **Companion manuscript** (`SyntheticCompanion`, `lines 228-235`) | `lines 164, 900, 909` | C. Anderson, *Synthetic arithmetic expansions and prescribed discrepancy*, v1.0 (`papers/07-synthetic-expansions`), pinned to `NormalityChecker/SharpTranslation.lean#L386` at `e4809cf561573aef588e6ffc491a35cdb79fd9ec`. Verified. |

---

## Task 2: Novelty, Antecedents, and Ledger Audit

1. **Wide search across formulations:**
   - Queries executed across web, arXiv, zbMATH Open, and Google Scholar indexed records: `"digits of Lambert series"`, `"binary expansion of sum of r_2(n) 2^{-n}"`, `"theta series digits normal"`, `"disjunctive non-normal number multiplicative function"`, `"Erdős–Borwein disjunctive"`, `"normality of q-series values"`, `"digit distribution of modular form values"`, `"Lambert series transcendence Dirichlet character"`, `"binary expansion" "r_2(n)" "disjunctive"`, and `"Shiu" "Lambert series" "binary"`.
   - For the classical Erdős–Borwein constant $E = \sum_{m\ge 1}(2^m-1)^{-1} = \sum_{n\ge 1}\tau(n)2^{-n}$ (where $\delta = 1$), the relevant antecedents are Erdős (1948), Borwein (1992), Bailey–Crandall (2001, 2002), Crandall (2012), Campbell (`arXiv:2605.24160`, May 2026), Captain Sude (`erdos-borwein-disjunctivity` at `bd98789a` and `erdos-borwein-disjunctivity-elementary` at `d51e93e9`, Sept 2026), Mira Cult (`Mira-acc` gist `79be9a5d/41b5a780` S06, Oct 2026), and Mira Cult (`Mira-Cult/math` Claim 0002 at `14983194`, Nov 2026).
   - For non-normal disjunctive Lambert-type series, Captain Sude's `generalized-Lambert-disjunctivity-and-nonnormality` (`fe33be210446c6c0b127ca7757fc8f1182c5b541`, Sept 2026) proves that the polynomial-exponent series $\sum_{m\ge 1}(b^{m^r}-1)^{-1}$ ($b, r \ge 2$) is disjunctive with *positive* limiting frequencies for all words yet non-normal.
   - No prior published or public-repository work was found that treats the binary digits or discrepancy of sparse multiplicative Lambert series $L = \sum_{m\ge 1} f(m)/(2^m-1) = \sum_{n\ge 1} c(n)2^{-n}$ under `(H1)–(H4)` (such as $L_{\chi_4} = \frac{1}{4}(\theta_3(1/2)^2 - 1)$), where the prime support density $\delta \in (0,1)$ causes the odd part $U(m)$ of $c(m)$ to decay on average like $(\log m)^{-(1-\delta)}$ while also permitting a Selberg upper-bound sieve over primes outside $S$ to force nearby coefficients to vanish identically.
2. **Completeness of `LEDGER.md` and qualification of priority language:**
   - `LEDGER.md` (`lines 1-87`) covers every headline result (Theorem A, Theorem B, Corollary 1.2, Theorem C, Proposition 6.1) in the required 8-field format of `WAVE2-CONTRACT.md:59-73`, followed by a primary-source audit table (`lines 58-78`) and bibliography verification section (`lines 80-87`).
   - Credit to Campbell, Captain Sude (including `bd98789`, `d51e93e`, and `fe33be2`), Mira Cult (`1498319`, crediting GPT-6.2 Astra under Mira's guidance, plus the `Mira-acc` gists `41b5a78` S06 and `d699a69`), and Hamieh–Murty is thorough and exact in `LEDGER.md:13, 45`. See Finding 4 for a minor recommendation to reflect two of the ledger's public-repository citations (`fe33be2` and `41b5a78` S06) in Section 1.4 of `paper.tex` as well.
   - All priority claims in `paper.tex:254-257` and `LEDGER.md:3, 14, 25` are explicitly qualified as statements about the sources examined rather than claims of priority.

---

## Task 3: Lean 4 Correspondence Audit

Every Lean declaration cited in `paper.tex` and `VERIFICATION.md` was inspected at commit `e4809cf561573aef588e6ffc491a35cdb79fd9ec` via `git show e4809cf561573aef588e6ffc491a35cdb79fd9ec:<path>`:

| Paper reference | Pinned Lean declaration at `e4809cf` | Verification against Lean source |
| --- | --- | --- |
| `paper.tex:316, 1062` (finite head of Lemma 2.1) | `NormalityChecker/WeightedLambertIdentities.lean#L21` (`lambert_head_eq_taylor`) | **Exact match.** Line 21 declares `theorem lambert_head_eq_taylor (a : ℕ → ℚ) (N : ℕ)`, proving the finite Lambert-to-Taylor head identity. |
| `paper.tex:414, 1060` (eq. `(2)` in Lemma 3.2) | `NormalityChecker/ErdosBorweinArrivals.lean#L41` (`arrival_sum`) | **Exact match.** Line 41 declares `theorem arrival_sum`, proving $\sum_{n\in\text{window}} \text{arrival}(n+d) = \sum_{m\in\text{sources}} \ind_{\text{location}(m)-d \in \text{window}} \text{mark}(m)$. |
| `paper.tex:449, 1061` (Markov step in Prop. 3.3(a)) | `NormalityChecker/WeightedLambertIdentities.lean#L166` (`nonneg_one_bit_count_le`) | **Exact match.** Line 166 declares `theorem nonneg_one_bit_count_le`, bounding the 1-bit count by $2\sum_{n\in\text{window}} S(n)$ whenever $S(n) \ge 0$ and $\text{bit}(n) \implies S(n) \ge 1/2$. |
| `paper.tex:836, 1056` (Lemma 7.1, upper gap transfer) | `NormalityChecker/Phase17DiscrepancyBounds.lean#L98` (`one_sub_discrepancy_le_one_bits`) | **Exact match.** Line 98 declares `theorem one_sub_discrepancy_le_one_bits (x : ℝ) {L N : ℕ} (hL : 1 ≤ L) (hN : 0 < N)`, proving $1 - \text{binaryDiscrepancy } x\ N \le (1/2)^L + (L-1)/N + L \cdot \text{frequency (shift 2 } x)\ (1/2)\ 1\ N$. |
| `paper.tex:838, 1057` (auxiliary to Lemma 7.1) | `NormalityChecker/Phase17DiscrepancyBounds.lean#L77` (`upper_freq_le_one_bits`) | **Exact match.** Line 77 declares `theorem upper_freq_le_one_bits`, bounding `frequency (shift 2 x) ((1/2)^L) 1 N`. |
| `paper.tex:848, 1058` (Lemma 7.2, lower gap transfer) | `NormalityChecker/Phase17DiscrepancyBounds.lean#L123` (`one_sub_discrepancy_ge_of_separated_mass`) | **Exact match.** Line 123 declares `theorem one_sub_discrepancy_ge_of_separated_mass`, proving $\Delta \le 1 - \text{binaryDiscrepancy } x\ N$ under $0 < \varepsilon \le 1/6$, $\Delta \le \varepsilon$, and frequency at least $\Delta$ on both $[0,\varepsilon)$ and $[3\varepsilon, 1/2)$. |
| `paper.tex:890, 1059` (Remark 7.3, transition lower bound) | `NormalityChecker/Phase17DiscrepancyBounds.lean#L28` (`one_sub_discrepancy_ge_transition`) | **Exact match.** Line 28 declares `theorem one_sub_discrepancy_ge_transition`, derived from `SharpDiscrepancy.lean#L68` (`sharp_finite_discrepancy`). |
| `paper.tex:906, 907, 911, 1063` (Theorem 8.1 & Cor. 1.2) | `NormalityChecker/SharpTranslation.lean#L386` (`sharp_translation_isGreatest`), `#L343` (`sharp_translation`), `#L357` (`radixDiscrepancy_zero`) | **Exact match.** Lines 343, 357, and 386 prove $|D_N(x+z)-D_N(x)| \le 1 - D_N(z)$, $D_N(0) = 1$, and attainment of the maximum $1 - D_N(z)$ at $x = 0$ for every base $b$, real $z$, and $N > 0$. |
| `paper.tex:1046-1048` & `VERIFICATION.md:40` (definitions) | `Basic.lean#L15` (`shift`), `Basic.lean#L18` (`frequency`), `BinaryDiscrepancy.lean#L11` (`radixDiscrepancy`), `BinaryDiscrepancy.lean#L23` (`transitionFrequency`) | **Exact match.** All definitions agree with Section 1.1 (`paper.tex:89-111`) at base $b = 2$. |

No analytic theorem is labelled `Kernel-verified` anywhere in the manuscript package.

---

## Task 4: Presentation and Build Audit

- **Build check:** `wsl -d Ubuntu -- bash papers/wsl-build.sh 06-multiplicative-lambert` compiles cleanly via `latexmk` and `bibtex`, producing an 18-page PDF with zero undefined references/citations and zero overfull/underfull box warnings.
- **Script check:** `python -B scripts/phase17_multiplicative_lambert.py` passes in 1.65 s and reproduces the exact numerical enclosures reported in Section 10.2 (`paper.tex:1018-1021`).
- **Exposition quality:** The manuscript is written in clean, journal-quality mathematical prose. Hypotheses `(H1)–(H4)` and all notation ($x_n$, $I_w$, $\cnt_w(N,H)$, $D_N(x)$, $\asymp$) are defined in Section 1.1 before Theorems A, B, and C are stated in Section 1.2. Examples 1.3 and 1.4 and Remark 1.5 immediately motivate each hypothesis. There is no repository jargon (`"Phase 17"`, `"Track B"`, registry IDs) in the prose body.

---

## Task 5: Submission Package Audit

- `submission/abstract.txt`: 215 words ($\le 250$ words), plain text with simple `$...$` math only.
- `submission/alphaxiv.md`: Contains title, author (`Christopher Anderson (Independent Researcher)`), version, `math.NT`, keywords, MSC2020 codes, abstract, pinned source/Lean/script links, verification scope paragraph, and the verbatim AI-use disclosure from `WAVE2-CONTRACT.md:77`.
- `submission/announcement.md`: The X post is 263 characters ($\le 280$ characters), nonpromotional, and states the verification boundary; the forum paragraph credits Campbell, Captain Sude, Mira Cult, and Hamieh–Murty and requests specialist review of the analytic steps.
- `submission/summary.md`: Accurate one-paragraph mathematical summary.
- `submission/reviewer-inquiry.md`: Two individualized templates using `[Name]` placeholders and no email addresses. Inquiry 1 targets Alia Hamieh and M. Ram Murty on Theorem C (citing *Int. J. Number Theory* **12** (2016), 765–773, Theorems 1.1 and 3.1, and asking about $\Gamma_1(q_*P)$ oldforms in Theorem 3.1). Inquiry 2 targets Alberto Perelli, János Pintz, and Saverio Salerno on Lemma 4.4 / Theorem A (citing *Invent. Math.* **79** (1985), 1–9, Theorem on p. 2, and asking whether a fixed-modulus lower bound in short intervals is known below exponent $7/12$). Both include the AI-assistance and human-review disclosure.
- `submission/reviewer-packet.md`: Self-contained summary of setting, exact theorem statements, evidence labels, 8-step proof sketch with every external input cited by theorem and page, reproduction commands, and 5 specific review questions.

---

## Numbered Findings

### Critical

None.

### Major

None.

### Minor

1. **Committed `paper.pdf` predates the shared byline update (`6ad4d2c`) and lacks author metadata**
   - **Severity:** Minor
   - **Location:** `papers/06-multiplicative-lambert/paper.pdf` (page 1 byline and PDF document info; cf. `paper.tex:3, 21` and `papers/common/byline.tex:5-16`)
   - **Problem:** At commit `dedc430`, the committed `papers/06-multiplicative-lambert/paper.pdf` (495,390 bytes, compiled in `ca2255f` before `6ad4d2c` updated `papers/common/byline.tex`) still displays the placeholder `"Author information pending owner approval"` and `"Version 1.0 · 25 November 2026 · manuscripts-v2.0.0 candidate"` on page 1, and its PDF `Author` metadata field is empty (`pdfinfo papers/06-multiplicative-lambert/paper.pdf`). Rebuilding via `wsl -d Ubuntu -- bash papers/wsl-build.sh 06-multiplicative-lambert` produces the updated 18-page PDF (494,286 bytes) displaying `Christopher Anderson`, `Independent Researcher`, `manuscripts-v2.0.0`, and PDF metadata `Author: Christopher Anderson`, as required by `WAVE2-CONTRACT.md` (Principle 5).
   - **Concrete fix:** Rebuild `papers/06-multiplicative-lambert/paper.pdf` with `wsl -d Ubuntu -- bash papers/wsl-build.sh 06-multiplicative-lambert` and refresh `papers/SHA256SUMS` with `python papers/check_release.py --write-checksums`.

2. **Add article identifier `A23` to `Crandall2012` in `references.bib` and cite `Crandall2012` (or Bailey–Crandall 2002) at `paper.tex:59` for the normality of $E$**
   - **Severity:** Minor
   - **Location:** `paper.tex:59`, `references.bib:152-169`, `LEDGER.md:12`
   - **Problem:** `paper.tex:58-59` cites only `BaileyCrandall2001` (*On the random character of fundamental constant expansions*, Experiment. Math. **10** (2001), 175–190) for the statement that the binary normality of the Erdős–Borwein constant $E$ is open. While Bailey and Crandall (2001) formulate the general Hypothesis A framework for fundamental constants, their specific analysis of the binary normality and 2-density of $E$ appears in Section 5 (pp. 537–541, Conjecture 5.3 and Theorem 5.5) of their sequel *Random generators and normal numbers*, Experiment. Math. **11** (2002), no. 4, 527–546 (`doi:10.1080/10586458.2002.10504704`), and in Crandall (2012, §7) (`Crandall2012`, already in `references.bib:162-169`). Furthermore, `Crandall2012` in `references.bib:162-169` omits the article number `pages = {A23}`.
   - **Concrete fix:** Add `pages = {A23}` to `Crandall2012` in `references.bib:162-169`, and cite `\cite{BaileyCrandall2001,Crandall2012}` (or add Bailey–Crandall 2002) at `paper.tex:59`.

3. **Reconcile the primary-source verification note for `DNNS1996` between `LEDGER.md` and `references.bib`**
   - **Severity:** Minor
   - **Location:** `references.bib:111-119`, `LEDGER.md:45, 82-87` (cf. `paper.tex:206` and `WAVE2-CONTRACT.md:43`)
   - **Problem:** `WAVE2-CONTRACT.md` (line 43) stipulates that any bibliography entry whose primary source was not directly checked must carry `note = {unverified}` in `references.bib` and be listed in the ledger. In `LEDGER.md:45`, the entry for Duverney, Ke. Nishioka, Ku. Nishioka and Shiokawa (`DNNS1996`, *Proc. Japan Acad. Ser. A Math. Sci.* **72** (1996), 202–203, `doi:10.3792/pjaa.72.202`) states `"Our account comes from secondary descriptions; we did not read the full text"`, whereas `references.bib:111-119` has no `note = {unverified...}` field and `LEDGER.md:82-84` lists only `CaludePrieseStaiger1997` as unverified. (The 2-page paper is open-access on Project Euclid at `https://doi.org/10.3792/pjaa.72.202`, where Theorem 1 and its Corollary on p. 202 deduce the transcendence of $\theta_3(q)$ for algebraic $0 < |q| < 1$ from Nesterenko's theorem.)
   - **Concrete fix:** Either check the open-access Project Euclid PDF (`doi:10.3792/pjaa.72.202`, p. 202) and update `LEDGER.md:45` to record primary-text verification, or add `note = {unverified: bibliographic record checked; full text not examined}` to `DNNS1996` in `references.bib:111-119` and list it in `LEDGER.md:82-84`.

4. **Reflect `LEDGER.md`'s citations of Captain Sude's generalized Lambert repository (`fe33be2`) and Mira Cult's October 2026 gist (`41b5a78` S06) in Section 1.4 (`paper.tex:237-263`)**
   - **Severity:** Minor
   - **Location:** `paper.tex:242-246, 259-263` (cf. `LEDGER.md:13`)
   - **Problem:** `LEDGER.md:13` accurately records two public-repository antecedents that are not mentioned in Section 1.4 (`subsec:context`) of `paper.tex`: (i) Captain Sude's `generalized-Lambert-disjunctivity-and-nonnormality` (`fe33be210446c6c0b127ca7757fc8f1182c5b541`), which proves that $\sum_{m\ge 1}(b^{m^r}-1)^{-1}$ ($b, r \ge 2$) is disjunctive (with positive limiting frequency for every word) yet nonnormal, whereas `paper.tex:259-263` (*Disjunctive nonnormal numbers*) contrasts the manuscript's constants only with combinatorial constructions (`CaludePrieseStaiger1997`); and (ii) Mira Cult's (`Mira-acc`) 7 October 2026 gist (`79be9a5d4aa54a9df41e702c4f3113ea`, revision `41b5a780f79f7bdd275cd96e7e310b000a897d35`, note `S06`), which gave prefix word-count lower bounds $N\exp[-C_w(\log\log N)^2\log\log\log N]$ for $E$ prior to the November 2026 moving-window note `MiraCult`.
   - **Concrete fix:** In `paper.tex:259-263`, briefly contrast the sparse multiplicative series $L_c$ (where every word containing a $1$ has frequency $0$ and $D_N(L_c) \to 1$) with Captain Sude's polynomial-exponent series $\sum_{m\ge 1}(b^{m^r}-1)^{-1}$ ($r \ge 2$, where every word has positive limiting frequency), and mention Mira Cult's October 2026 note `S06` alongside `MiraCult` on `paper.tex:245-246`.

5. **Clarify the right-endpoint bound $5N$ in Lemma 3.2 (`paper.tex:419-422`) when $N$ is small relative to the fixed shift $s$**
   - **Severity:** Minor
   - **Location:** `paper.tex:417-422`
   - **Problem:** In the proof of Lemma 3.2 (`lem:windows`), `paper.tex:408` sets $N' = N + s$ for a fixed integer $s \ge 0$. For $d \le N'$ and $H \le N$, `paper.tex:419-422` applies Lemma 3.1 (`lem:shiu`) with exponent $\sigma/2$ to the interval $(N'+d-1, N'+H+d+B-1]$, stating that it has `"length H+B \ge N^\sigma and right endpoint at most 5N"`. The right endpoint is $x = 2N' + H + B - 1 = 2N + 2s + H + B - 1$, which is at most $5N$ (and satisfies $H+B \ge N^\sigma \ge x^{\sigma/2}$) once $N$ is sufficiently large in terms of $s$ and $\sigma$, while for bounded $N$ the sum is $O_{\sigma,s}(1)$ trivially.
   - **Concrete fix:** On `paper.tex:419-422`, state `"For $N$ large relative to $s$ and $\sigma$, apply Lemma~3.1 with exponent $\sigma/2$ to the interval $(N'+d-1,\,N'+H+d+B-1]$ of length $H+B\ge N^\sigma\ge (5N)^{\sigma/2}$ and right endpoint at most $5N$ (for bounded $N$ the sum is $O_{\sigma,s}(1)$)"`.

### Editorial

6. **Include `lambert_head_eq_taylor` in the pinned Lean declaration list of `submission/alphaxiv.md`**
   - **Severity:** Editorial
   - **Location:** `submission/alphaxiv.md:20-27` (cf. `paper.tex:316, 1062` and `VERIFICATION.md:18, 50`)
   - **Problem:** The verification table in `paper.tex:1052-1065` and `VERIFICATION.md:18, 50` lists eight pinned Lean theorem declarations used in the manuscript, whereas `submission/alphaxiv.md:20-27` lists seven, omitting [`lambert_head_eq_taylor`](https://github.com/eldernos/MathematicsResearch/blob/e4809cf561573aef588e6ffc491a35cdb79fd9ec/NormalityChecker/WeightedLambertIdentities.lean#L21).
   - **Concrete fix:** Add `- [\`lambert_head_eq_taylor\`](https://github.com/eldernos/MathematicsResearch/blob/e4809cf561573aef588e6ffc491a35cdb79fd9ec/NormalityChecker/WeightedLambertIdentities.lean#L21)` to `submission/alphaxiv.md:20-27`.
