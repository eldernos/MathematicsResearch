# Novelty and literature ledger: Erdős–Borwein research note (v1.0)

Language is qualified throughout: no search result proves novelty. "Apparently new in the sources examined" records only what we looked at. Human specialist review is outstanding; cross-model review is not independent human peer review.

## Scope of the search record (read this first)

What was actually done for this note (25 November 2026):

- Primary sources read in full or in the relevant parts: Erdős (1948) scan; Crandall (2012) journal PDF; Tao–Teräväinen arXiv:2512.01739v2 (abstract, Theorems 1.3, 1.7, 3.1, introduction); Campbell arXiv:2605.24160 (abstract page); Mira Cult's README at the pinned commit; Mira-acc gist revision `41b5a780…` (the S06 passages); Captain Sude `Main.lean` at `bd98789…` and the elementary archive (SHA-256 verified, theorem statements of `ElementaryMain.lean` and `ElementaryQuantitative.lean` read; Lean build not rerun).
- Bibliographic data (journal, volume, pages, DOI) checked against Crossref for Borwein (1992), Bailey–Crandall (2002, cited since the revision), Vaaler (1985), Matomäki–Radziwiłł–Tao (2015), Tao (2016), Tao–Teräväinen (JTNB 2019), Heath-Brown (1984).
- Three general web searches (standard mode): (i) "Erdős–Borwein constant binary digits normality Poisson model divisor function digit frequency", (ii) "lower bound expectation (−1)^N given first r factorial moments Poisson parity Bonferroni inequality binomial moments", (iii) "Erdős–Borwein constant normal base 2 bits statistics Mitchell terabyte Crandall too many ones". They returned Campbell's preprint, MathWorld/Wikipedia/OEIS pages, and general Bonferroni-type literature (below). Nothing located stating our results.
- **Not done:** zbMATH Open, MathSciNet, Google Scholar and journal-archive searches; reference-trail following beyond Crandall's and Tao–Teräväinen's bibliographies. Before any priority statement the owner (or a reviewer) should run those searches. All "Relation" fields below are therefore provisional.
- **Revision of 25 November 2026 (after referee report 1, Gemini 4 Neon; `papers/reviews/09-erdos-borwein-note/review-1.md`; resolution in `papers/reviews/09-erdos-borwein-note/resolution.md`).** The referee ran zbMATH Open and Google Scholar searches for "Erdős–Borwein", "1/(2^n−1)", "Lambert series binary digits", "Bailey Crandall 2-normal", "Borwein 1/(q^n+r)" and "Vandehey Erdos Lambert", and read: the AMS PDF of Vaaler (1985); Sibuya (1991) in full (`ism.ac.jp/editsec/aism/pdf/043_2_0261.pdf`); the INTEGERS PDF of Crandall (2012); the arXiv source of Tao–Teräväinen v2. The reviser additionally (a) checked bibliographic data against Crossref for Bailey–Crandall (2002), Aragón Artacho–Bailey–Borwein–Borwein (2013), P. Borwein (1991), Sibuya (1991), Tao (2016) and Tao–Teräväinen (2019), and the arXiv API for Vandehey (arXiv:1206.0340); (b) read Section 5 of Bailey–Crandall in the author preprint dated 20 March 2003 (`davidhbailey.com/dhbpapers/bcnormal.pdf`): Conjecture 5.3 (equidistribution of x_d = Σ_{k≤d} (2^{d mod k} − 1)/(2^k − 1) mod 1) and the theorem that follows it (numbered 5.4 in the preprint, 5.5 in the referee's reading of the journal version) state that E is 2-normal iff the conjecture holds; (c) text-searched the Sibuya PDF for "parity" and "Poisson" (no hits); (d) could not download the AMS PDF of Vaaler (ams.org returned an HTML page to an automated request), so the theorem numbers for Vaaler rest on the referee's reading. Not done: MathSciNet; Galambos–Simonelli (1996) was not read (only its Zbl entry 0869.60014; the book is not in Crossref).
- Phase 19 notes (`literature.md`, `grids.md`) were read at the coordinator's instruction for EB-relevant remarks. They contain no Erdős–Borwein theorem and nothing cited here (one remark in `grids.md` observes that raw shifted prefixes of the divisor expansion are integral, grid size one; unused).

### Bibliography entries needing caution (see `references.bib`)

| Key | Status |
| --- | --- |
| `vaaler1985` | Metadata verified (Crossref). Theorem numbers verified against the AMS PDF by the referee of review 1: Theorem 6 (p. 193, eq. (2.28), `Ĵ`), Theorem 18 (p. 210, eq. (7.14), `ψ*j_N` and the Fejér-kernel bound), Theorem 19 (pp. 211–212, eqs. (7.24)–(7.27), majorant for BV functions), Theorem 20 (pp. 213–214, interval case, Erdős–Turán). Not independently re-read by the reviser. The earlier "unverified" marker is removed. |
| `borwein1991`, `borwein1992`, `tt2019`, `tao2016`, `mrt2015`, `heathbrown1984` | Metadata verified (Crossref; `tao2016` has article number e8; `tt2019` is *Journal de Théorie des Nombres de Bordeaux*); contents not examined beyond abstract/title. `heathbrown1984` is cited only for the existence of the asymptotic for `Σ d(n)d(n+1)`; its exact error term is **not** stated in the note. |
| `tt2025` | Read (abstract, Theorems 1.3, 1.7, 3.1, introduction); the referee read the v2 source `main2.tex`. Theorem numbers are those of **v2** (25 April 2026). Theorem 1.7 (`τ(n)=τ(n+1)`): the probability is (c_τ + O(log_2^{−c} x)) / (2√(π log_2 x)) (the first draft of the note wrote √(2π log_2 x), wrong by a factor √2; corrected). Theorem 3.1: case (i) (equidistributed, conditions (3.1)–(3.2)) and case (ii) (non-pretentious, condition (3.3): `exp(M(g_1; X², log^{1/125} X)) ≫ 𝓛`); (3.2) is attached to case (i) only. |
| `baileycrandall2002`, `aabb2013`, `vandehey2013`, `sibuya1991`, `gs1996` | New in the revision. The first three: metadata verified (Crossref / arXiv API) and described from the referee's zbMATH/Scholar findings; `baileycrandall2002` was additionally read in its author preprint (see above). `sibuya1991`: metadata verified (Crossref); full text read by the referee and text-searched by the reviser. `gs1996`: publisher and year only; contents not read. |
| Borwein 1991 and 1992 | P. Borwein, *On the irrationality of Σ(1/(q^n+r))*, J. Number Theory 37 (1991), 253–259, DOI 10.1016/S0022-314X(05)80041-1 (now cited as `borwein1991`; metadata only). The paper Crandall cites is *On the irrationality of certain series*, Math. Proc. Cambridge Philos. Soc. 112 (1992), 141–146 (`borwein1992`; Crossref abstract: irrational and not Liouville for integer q ≠ 0, ±1 and rational r ≠ 0, r ≠ −q^n). We did not read either text, so we cannot say which covers `q=2, r=−1` first. |
| Mira-acc gist, Mira Cult, Captain Sude | Public repositories/gists, cited by pinned commit; not peer-reviewed. |

## Credit for related public work (precise)

- **Erdős (1948)**, J. Indian Math. Soc. 12, 63–66: for every integer `|t|>1`, `f(1/t)` and `g(1/t)` are irrational, `f(x)=Σ x^n/(1−x^n)`, `g(x)=Σ x^n/(1−x^n) sin(nπ/2)`. At `t=2`, `f(1/2)=E`. (Read on the scan, p. 63.) Crandall's §7 attributes to it a run of zeros of length ≥ `c log^{1/10} N` among the first `N` bits.
- **Crandall (2012)**, INTEGERS 12, #A23 (received 11/5/11, accepted 2/25/12, published 3/1/12): the googol-th bit is 1; the §6 counts for 2^43 bits; open problems in §7 (2-normality, whether `11` occurs infinitely often).
- **Campbell (22 May 2026)**, arXiv:2605.24160 v1: the word `11` occurs infinitely often in the binary expansion of `E` (congruence construction in the spirit of Erdős and an Alford–Granville–Pomerance estimate). No lower frequency.
- **Captain Sude**, `erdos-borwein-disjunctivity` tag `v1.0.0`, `bd98789a177470cc4b3e33e6769e859f6144c906`: Lean `binaryDisjunctive_lambertE (hAGP : AGP) (hSupply : PrimeIntervalSupply)` (line 140 of `lean/ErdosBorwein/Main.lean`), i.e. disjunctivity **conditional** on two stated analytic inputs, with a paper claiming `N exp[−C_w (log log N)^3]` occurrences. `erdos-borwein-disjunctivity-elementary`, `d51e93e91ff43efef6918efdd4258bbd43bad7aa`, archive `erdos-borwein-fully-verified-20260908.zip` (SHA-256 `2c4642a6…972d60`, matches): `binaryDisjunctive_lambertE_unconditional` and `quantitative_occurrences_lambertE (ell v) (hv : v < 2^ell)` with `N·exp(−70000 (log log N)^3) ≤ #occurrences` for `N ≥ N₀(ell,v)`.
- **Mira Cult**, `Mira-Cult/math`, README at `149831943806a656c9efaa14cacbd9c915b2a2ba`: for fixed `7/12 < a ≤ 1` and fixed nonempty `w`, every sufficiently late window of `H ≥ N^a` digits after digit `N` has at least `c_{a,w} H` wholly contained occurrences. The README states that it still gives no limiting frequencies. (Audit of the proof is recorded in `notes/phase13/reviews/erdos-local-limit.md`; not redone for this note.)
- **Mira-acc gist** (`79be9a5d…`, rev `41b5a780…`, S06): quantitative lower bounds `N exp[−C_w (log log N)^2 log log log N]` for fixed words and `N exp[−(log N)^η]` for words of length up to `c (log_2 log N)^2` (read in the gist's executive summary); the gist itself notes that this is not normality.
- **Bailey–Crandall (2002)**, *Random generators and normal numbers*, Experiment. Math. 11 (2002), no. 4, 527–546, DOI 10.1080/10586458.2002.10504704 (Zbl 1165.11328): Section 5 (Conjecture 5.3 and the equivalence theorem that follows it) shows that E is 2-normal iff the sequence x_d = Σ_{k≤d} (2^{d mod k} − 1)/(2^k − 1) mod 1 is equidistributed. A reformulation of 2-normality; no digit frequency and no model of the type of `Q_∞`.
- **P. B. Borwein (1991)**, J. Number Theory 37 (1991), no. 3, 253–259, DOI 10.1016/S0022-314X(05)80041-1 (Zbl 0718.11029): irrationality of Σ 1/(q^n+r); metadata only.
- **Aragón Artacho–Bailey–Borwein–Borwein (2013)**, *Walking on real numbers*, Math. Intelligencer 35 (2013), no. 1, 42–60, DOI 10.1007/s00283-012-9340-x (Zbl 1282.11088): experimental digit-walk study of classical constants including E; no theorem about digit frequencies of E (as reported by the referee; the paper was not read by the reviser).
- **Vandehey (2013)**, *On an incomplete argument of Erdős on the irrationality of Lambert series*, Integers 13 (2013), #A58 (arXiv:1206.0340; Zbl 1284.11101): the Lambert series Σ d(n)x^n is irrational at x = 1/b for integers b < −1, finishing an incomplete argument of Erdős (arXiv abstract). Background to the Erdős (1948) citation; unrelated to digit statistics.
- **Sibuya (1991)**, *Bonferroni-type inequalities; Chebyshev-type inequalities for the distributions on [0,n]*, Ann. Inst. Statist. Math. 43 (1991), no. 2, 261–285, DOI 10.1007/BF00118635 (Zbl 0764.60022), and **Galambos–Simonelli (1996)**, *Bonferroni-type inequalities with applications*, Springer (Zbl 0869.60014): majorant–minorant polynomial method for sharp bounds on P(N=m) and P(N≥m) from binomial moments of a count on {0,…,n}. The referee (full read of Sibuya; summaries of Galambos–Simonelli) found no statement of the parity functional E(−1)^N or of the value Σ_{k≤r}(−2)^k/k!; the reviser's text search of the Sibuya PDF found no occurrence of "parity" or "Poisson". Theorem 7.1 fits this framework (dual polynomial q_r and primal law on {0,…,r} as a complementary-slackness pair) but the specific statement was not located.
- Recorded, not cited (tangential, irrationality or inequalities rather than digits; from the referee's zbMATH sweep): M. Merca, *A double inequality involving Erdős–Borwein constants*, Miskolc Math. Notes 16 (2015), 277–281 (Zbl 1340.26050); S. Murakami and Y. Tachiya, *Linear independence of certain infinite series with monomial orders*, Int. J. Number Theory 21 (2025), no. 8, 1777–1794 (Zbl 1579.11115). Not read by the reviser.
- **Tao–Teräväinen (2025/26)**, arXiv:2512.01739 v2: irrationality of `Σ ω(n)/2^n` (Theorem 1.3), almost-all-scales asymptotics for `P(ω(n)=ω(n+1))`, `P(Ω(n)=Ω(n+1))` and `P(τ(n)=τ(n+1))` (Theorem 1.7; for τ the denominator is `2√(π log_2 x)`), and a two-point quantitative correlation estimate for `1`-bounded multiplicative functions (Theorem 3.1). **Observation recorded in the note (not a theorem):** for `g_θ = e(θV)χ(U)` one has `g_θ(p) = e(θ)` at every prime, so the pretentious distance is `(1 − cos 2πθ) Σ 1/p ≫ R^{−2} log_2 X` for `1/R ≤ ‖θ‖ ≤ 1/2` (Section 4.1 of their paper uses the same prime values for `e(αΩ_{>w}(n))`); on the referee's reading case (ii) of Theorem 3.1 therefore applies at each fixed θ (condition (3.2) belongs to case (i) only), giving an `L^1`-in-θ almost-all-scales analogue of Hypothesis E by Fubini as in their eq. (4.4). Limitations: the exceptional set depends on θ; two-point only; `r ≥ 3` open. Not re-derived by the reviser.

## Entries

### Proposition 3.1: one-source mean and tail mean
- **Statement and hypotheses:** `U(m)` odd part of `τ(m)`; `E_{n∈[N,2N)} C(n+d) = μ + O(N^{-1/2+ε})` uniformly for `d ≤ N`; `E_I Y_D = μ + o(1)`, `μ = Π_p E odd(B_p+1)`.
- **Evidence:** Paper proof (Möbius convolution supported on squarefull integers). Lean supports only the finite reindexing (`arrival_sum`).
- **Earliest relevant literature:** none located specifically. The method is the standard expansion of a multiplicative function as `1 * a` with `a` supported on squarefull integers (cf. mean values of `τ` restricted to odd part).
- **Closest published results:** none checked.
- **Closest unpublished or public-repository results:** the same one-source mean appears in this repository's earlier notes (Phase 14); Mira Cult's local-limit estimates concern a different sampling measure (primes conditioned on an incidence).
- **Relation:** elementary; probably known. Priority not claimed.
- **Search record:** not searched beyond the web queries in the scope section.
- **Dependencies and outstanding review:** check the uniformity in `d` and the strip estimate (`O(log N)` integers).

### Theorem 4.2: certified enclosure `p_* ∈ [0.492450290, 0.492460864]`
- **Statement and hypotheses:** `p_*` is the first-digit probability under the comparison law `Q_∞` (independent Poisson(1) columns of i.i.d. marks `U_*`). Enclosure by integer lower bounds and a 48-column carry dynamic programme; also `μ ∈ [2.0762592, 2.0763285]`.
- **Evidence:** Finite certificate (`scripts/phase17_erdos_borwein_bias.py` §A, §D). Independent float cross-check in `crosscheck.py`. In the script `p_*` is enclosed directly from the 48-column carry DP (truncation charge 2(μ_max+1)p_0^48) and `E(−1)^{c_1}` from the carry into column 1 over columns 2..48 (truncation charge a multiple of that); the paper's method paragraph was corrected to say so (referee Finding 7). Proposition 2.2 applied to the `E(−1)^{c_1}` enclosure would give the slightly narrower [0.4924548, 0.4924563]; the wider direct enclosure is reported.
- **Earliest relevant literature:** none located. Crandall (2012) asks about 2-normality but proposes no probabilistic model.
- **Closest published results:** none located.
- **Closest unpublished or public-repository results:** this repository's earlier enclosure `[0.492230, 0.492685]` (Phase 14, `scripts/erdos_borwein_poisson.py`) is superseded. A search result mentions Poisson-model heuristics for the normality of π (in a paper by D. Bailey, `tools-walk.pdf`; not read); that concerns a different constant.
- **Relation:** apparently new in the sources examined (a computed constant of a heuristic model). The model is not claimed to describe `E`.
- **Search record:** web query (i) above.
- **Dependencies and outstanding review:** the mark law truncation/charging in the script; independent recomputation by interval arithmetic would be welcome.

### Theorem 5.1 and Theorem 5.4: the sharp 16-column threshold
- **Statement and hypotheses:** `Ψ_16` bounded statistic of the packed residue `R_16`; `limsup E_I Ψ_16 < 0.4962723` along a sequence of dyadic windows implies `limsup f_I < 1/2`; `E_{Q_16}Ψ_16 ≤ 0.4960081`. For `D ≤ 15` an exact countermodel class element with `f(1) ≥ 0.502823`; `f^sup_16 ≤ 0.499736`.
- **Evidence:** Theorem 5.1: Lean-supported paper proof (`carry_knapsack_le`); Theorem 5.4: finite certificate.
- **Earliest relevant literature:** none located for this specific question. The tools are a fractional-knapsack linear programme and a tail-mean (Markov-type) estimate.
- **Closest published results:** none located.
- **Closest unpublished or public-repository results:** this repository's Phase 14 `D=32` statement (TV > 0.006 under simple normality, registered as CC-30) is the direct predecessor; Mira Cult's and Captain Sude's results give positive lower densities and disjunctivity, and are compatible with both `f(1)=1/2` and `f(1)=p_*` (no overlap with this statement).
- **Relation:** strengthens an earlier internal statement (`D=32` to `D=16`) and shows its sharpness for this information set; apparently new in the sources examined.
- **Search record:** web queries (i), (iii).
- **Dependencies and outstanding review:** the tail-mean estimate (Prop. 3.1); the knapsack certificates for `D = 4,…,23`; that the abstract class `𝓘_D` is the right formalization of "information".

### Theorem 6.1: column hierarchy (`k ≤ 4`)
- **Statement and hypotheses:** product-density perturbations of `Q_∞` that preserve every `(K−1)`-column joint law (`K=2,…,5`) and move `f(1)` by at least 0.015 (certified).
- **Evidence:** Finite certificate.
- **Earliest relevant literature / closest published results:** the construction is the standard "product of centered functions" perturbation (as in constructions of distributions with prescribed marginals); no specific source located.
- **Closest unpublished or public-repository results:** none.
- **Relation:** apparently new as an application; the device is classical.
- **Search record:** none specific.
- **Dependencies and outstanding review:** certified shifts `s_K`.

### Theorem 7.1: parity Bonferroni inequality; Proposition 7.2; Theorems 7.4 and 7.5
- **Statement and hypotheses:** for odd `r`, `min E(−1)^N = Σ_{k≤r} (−2)^k/k!` over laws on `ℤ_{≥0}` with `E (N)_k = 1` for `1 ≤ k ≤ r`; first positive at `r = 5`. Order `≤ 4` fails on any number of columns; order `≤ 8` fails at `D = 16`; an explicit order-92 witness suffices at `D = 16`.
- **Evidence:** Theorem 7.1: Lean-supported paper proof (`parity_bonferroni_dual_le`). Theorem 7.4: finite certificate. Theorem 7.5: Lean-supported paper proof with a finite-certificate step.
- **Earliest relevant literature:** Bonferroni-type inequalities and the Jordan formula are classical. Sibuya (1991), Ann. Inst. Statist. Math. 43 (2), 261–285 (Theorems 2.1, 3.1, 3.2, 3.3, 7.1 in the referee's reading), develops the majorant–minorant polynomial method for sharp bounds on P(N=m) and P(N≥m) from binomial moments S_1,…,S_r of a count on {0,…,n}; Galambos–Simonelli (1996) systematize it (polynomial, geometric and linear-programming methods).
- **Closest published results:** the general framework above. The referee read Sibuya in full and found no statement of the parity functional `E(−1)^N` or of the value `Σ_{k≤r}(−2)^k/k!`; the identity `E(−1)^N = Σ_k (−2)^k S_k` is classical inclusion–exclusion. Galambos–Simonelli was not read.
- **Closest unpublished or public-repository results:** none.
- **Relation:** an instance, in method, of the known majorant–minorant framework (extended from {0,…,n} to ℤ_{≥0}); the specific statement (parity functional, value `e_r`, sign change at r = 5) and its use for digit statistics were not located. Priority not claimed. Proposition 7.2 (even order: infimum `e_{r−1}`, not attained, by an `L → ∞` construction) is of the same kind and was added after referee Finding 3; its evidence is a Lean-supported paper proof plus `even_order_check.py`.
- **Search record:** web query (ii); the Sibuya framework surfaced there; the referee's zbMATH Open and Google Scholar searches for parity / even-number Bonferroni bounds found nothing stating the specific bound.
- **Dependencies and outstanding review:** a probabilist should check whether Theorem 7.1 follows from Sibuya-type results and cite accordingly; the Jordan-truncation argument of Theorem 7.5.

### Propositions 8.2 and 8.3 (formerly Theorems 8.2 and 8.3): Selberg–Vaaler degree and the degree-110 barrier
- **Statement and hypotheses:** the degree-116 Selberg–Vaaler majorant of `1_{[1/2,1)}` has `Q_∞`-mean ≤ 0.4999592; a positive measure with the model's Fourier coefficients for `|m| ≤ 110` charges `[1/2,1]` with mass ≥ 0.500192.
- **Evidence:** **Numerical evidence** (IEEE floating point, round-to-nearest, with explicit radii and hand-chosen margins; not interval arithmetic). Relabelled from "finite certificate" after referee Finding 1. External input: the majorant property of Vaaler (1985), Theorems 6, 18, 19.
- **Earliest relevant literature:** Vaaler (1985), *Some extremal functions in Fourier analysis*, Bull. Amer. Math. Soc. (N.S.) 12 (1985), no. 2, 183–216, DOI 10.1090/S0273-0979-1985-15349-2 (Zbl 0575.42003): Theorem 6 (p. 193), Theorem 18 (p. 210), Theorem 19 (pp. 211–212), Theorem 20 (pp. 213–214); Selberg's earlier construction is attributed there.
- **Closest published results:** the majorant inequality itself (external input).
- **Closest unpublished or public-repository results:** none.
- **Relation:** the use of the majorant for a Fourier-side sufficiency criterion and the dual measure for the barrier are computations of ours; the extremal functions are inherited.
- **Search record:** none beyond bibliographic check.
- **Dependencies and outstanding review:** interval-arithmetic (or exact rational) recomputation of `φ(m)`, the degree-116 evaluation and the degree-110 quadrature weights. The referee verified that Theorem 19 applied to `f = 1/2 + ψ(x) − ψ(x−1/2)` gives the stated Fourier coefficients and `S^+_N(0) = S^+_N(1/2) ≥ 1`.

### Proposition 10.1: Crandall audit
- **Statement and hypotheses:** exact digits agree with Crandall's abstract and Table 1 (`e_{10^10}=e_{10^20}=0`); §6 tables are internally consistent; the orientation (0/1 labels) of the `2^43` counts cannot be decided from data below `2^24`.
- **Evidence:** finite certificate.
- **Earliest relevant literature:** Crandall (2012) §6–§7 (the only source of the table; Mitchell's output is not public to our knowledge).
- **Closest published results:** none.
- **Closest unpublished or public-repository results:** none located.
- **Relation:** an audit; no claim that the table is wrong. An earlier internal remark that labels appear interchanged is withdrawn.
- **Search record:** web query (iii) found no independent reproduction of Mitchell's counts.
- **Dependencies and outstanding review:** certified shell frequencies to `s ≈ 30`, or Mitchell's raw output.
