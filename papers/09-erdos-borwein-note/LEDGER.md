# Novelty and literature ledger: Erdős–Borwein research note (v1.0)

Language is qualified throughout: no search result proves novelty. "Apparently new in the sources examined" records only what we looked at. Human specialist review is outstanding; cross-model review is not independent human peer review.

## Scope of the search record (read this first)

What was actually done for this note (25 November 2026):

- Primary sources read in full or in the relevant parts: Erdős (1948) scan; Crandall (2012) journal PDF; Tao–Teräväinen arXiv:2512.01739v2 (abstract, Theorems 1.3, 1.7, 3.1, introduction); Campbell arXiv:2605.24160 (abstract page); Mira Cult's README at the pinned commit; Mira-acc gist revision `41b5a780…` (the S06 passages); Captain Sude `Main.lean` at `bd98789…` and the elementary archive (SHA-256 verified, theorem statements of `ElementaryMain.lean` and `ElementaryQuantitative.lean` read; Lean build not rerun).
- Bibliographic data (journal, volume, pages, DOI) checked against Crossref for Borwein (1992), Bailey–Crandall (2002, not cited), Vaaler (1985), Matomäki–Radziwiłł–Tao (2015), Tao (2016), Tao–Teräväinen (JTNB 2019), Heath-Brown (1984).
- Three general web searches (standard mode): (i) "Erdős–Borwein constant binary digits normality Poisson model divisor function digit frequency", (ii) "lower bound expectation (−1)^N given first r factorial moments Poisson parity Bonferroni inequality binomial moments", (iii) "Erdős–Borwein constant normal base 2 bits statistics Mitchell terabyte Crandall too many ones". They returned Campbell's preprint, MathWorld/Wikipedia/OEIS pages, and general Bonferroni-type literature (below). Nothing located stating our results.
- **Not done:** zbMATH Open, MathSciNet, Google Scholar and journal-archive searches; reference-trail following beyond Crandall's and Tao–Teräväinen's bibliographies. Before any priority statement the owner (or a reviewer) should run those searches. All "Relation" fields below are therefore provisional.
- Phase 19 notes (`literature.md`, `grids.md`) were read at the coordinator's instruction for EB-relevant remarks. They contain no Erdős–Borwein theorem and nothing cited here (one remark in `grids.md` observes that raw shifted prefixes of the divisor expansion are integral, grid size one; unused).

### Bibliography entries needing caution (see `references.bib`)

| Key | Status |
| --- | --- |
| `vaaler1985` | Metadata verified (Crossref). Full text blocked (HTTP 403 from ams.org); theorem number and page of the majorant used in Thm 8.2 **not verified**. |
| `borwein1992`, `tt2019`, `tao2016`, `mrt2015`, `heathbrown1984` | Metadata verified (Crossref); contents not examined beyond abstract/title. `heathbrown1984` is cited only for the existence of the asymptotic for `Σ d(n)d(n+1)`; its exact error term is **not** stated in the note. |
| `tt2025` | Read (abstract, Theorems 1.3, 1.7, 3.1, introduction). Theorem numbers are those of **v2** (25 April 2026). An earlier internal note quoted the `τ(n)=τ(n+1)` result as "Theorem 1.6"; in v2 it is **Theorem 1.7**. |
| Borwein "1991" | The commissioning brief says "Borwein 1991". Crossref lists P. Borwein, *On the irrationality of Σ(1/(q^n+r))*, J. Number Theory 37 (1991), 253–259, DOI 10.1016/S0022-314X(05)80041-1 (metadata only checked; not cited). The paper Crandall cites, and which we cite, is *On the irrationality of certain series*, Math. Proc. Cambridge Philos. Soc. 112 (1992), 141–146 (Crossref abstract: irrational and not Liouville for integer q ≠ 0, ±1 and rational r ≠ 0, r ≠ −q^n). We did not read either text, so we cannot say which covers `q=2, r=−1` first. |
| Mira-acc gist, Mira Cult, Captain Sude | Public repositories/gists, cited by pinned commit; not peer-reviewed. |

## Credit for related public work (precise)

- **Erdős (1948)**, J. Indian Math. Soc. 12, 63–66: for every integer `|t|>1`, `f(1/t)` and `g(1/t)` are irrational, `f(x)=Σ x^n/(1−x^n)`, `g(x)=Σ x^n/(1−x^n) sin(nπ/2)`. At `t=2`, `f(1/2)=E`. (Read on the scan, p. 63.) Crandall's §7 attributes to it a run of zeros of length ≥ `c log^{1/10} N` among the first `N` bits.
- **Crandall (2012)**, INTEGERS 12, #A23 (received 11/5/11, accepted 2/25/12, published 3/1/12): the googol-th bit is 1; the §6 counts for 2^43 bits; open problems in §7 (2-normality, whether `11` occurs infinitely often).
- **Campbell (22 May 2026)**, arXiv:2605.24160 v1: the word `11` occurs infinitely often in the binary expansion of `E` (congruence construction in the spirit of Erdős and an Alford–Granville–Pomerance estimate). No lower frequency.
- **Captain Sude**, `erdos-borwein-disjunctivity` tag `v1.0.0`, `bd98789a177470cc4b3e33e6769e859f6144c906`: Lean `binaryDisjunctive_lambertE (hAGP : AGP) (hSupply : PrimeIntervalSupply)` (line 140 of `lean/ErdosBorwein/Main.lean`), i.e. disjunctivity **conditional** on two stated analytic inputs, with a paper claiming `N exp[−C_w (log log N)^3]` occurrences. `erdos-borwein-disjunctivity-elementary`, `d51e93e91ff43efef6918efdd4258bbd43bad7aa`, archive `erdos-borwein-fully-verified-20260908.zip` (SHA-256 `2c4642a6…972d60`, matches): `binaryDisjunctive_lambertE_unconditional` and `quantitative_occurrences_lambertE (ell v) (hv : v < 2^ell)` with `N·exp(−70000 (log log N)^3) ≤ #occurrences` for `N ≥ N₀(ell,v)`.
- **Mira Cult**, `Mira-Cult/math`, README at `149831943806a656c9efaa14cacbd9c915b2a2ba`: for fixed `7/12 < a ≤ 1` and fixed nonempty `w`, every sufficiently late window of `H ≥ N^a` digits after digit `N` has at least `c_{a,w} H` wholly contained occurrences. The README states that it still gives no limiting frequencies. (Audit of the proof is recorded in `notes/phase13/reviews/erdos-local-limit.md`; not redone for this note.)
- **Mira-acc gist** (`79be9a5d…`, rev `41b5a780…`, S06): quantitative lower bounds `N exp[−C_w (log log N)^2 log log log N]` for fixed words and `N exp[−(log N)^η]` for words of length up to `c (log_2 log N)^2` (read in the gist's executive summary); the gist itself notes that this is not normality.
- **Tao–Teräväinen (2025/26)**, arXiv:2512.01739 v2: irrationality of `Σ ω(n)/2^n` (Theorem 1.3), almost-all-scales asymptotics for `P(ω(n)=ω(n+1))`, `P(Ω(n)=Ω(n+1))` and `P(τ(n)=τ(n+1))` (Theorem 1.7), and a two-point quantitative correlation estimate for `1`-bounded multiplicative functions (Theorem 3.1).

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
- **Evidence:** Finite certificate (`scripts/phase17_erdos_borwein_bias.py` §A, §D). Independent float cross-check in `crosscheck.py`.
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

### Theorem 7.1: parity Bonferroni inequality; Theorems 7.4 and 7.5
- **Statement and hypotheses:** for odd `r`, `min E(−1)^N = Σ_{k≤r} (−2)^k/k!` over laws on `ℤ_{≥0}` with `E (N)_k = 1` for `1 ≤ k ≤ r`; first positive at `r = 5`. Order `≤ 4` fails on any number of columns; order `≤ 8` fails at `D = 16`; an explicit order-92 witness suffices at `D = 16`.
- **Evidence:** Theorem 7.1: Lean-supported paper proof (`parity_bonferroni_dual_le`). Theorem 7.4: finite certificate. Theorem 7.5: Lean-supported paper proof with a finite-certificate step.
- **Earliest relevant literature:** Bonferroni-type inequalities and the Jordan formula are classical; Sibuya's *Bonferroni-type inequalities; Chebyshev-type inequalities for the distributions on [0, n]* (Ann. Inst. Statist. Math., apparently vol. 43 no. 2 from p. 261, inferred from the URL `ism.ac.jp/editsec/aism/pdf/043_2_0261.pdf`; **not read, metadata not verified**) treats sharp Bonferroni-type inequalities for given lower binomial moments by a majorant–minorant method and is the closest framework we found.
- **Closest published results:** the general framework above (sharp bounds for functionals of a count variable in terms of its first binomial moments). Whether the specific value `Σ_{k≤r}(−2)^k/k!` for `E(−1)^N` appears there is **unchecked**.
- **Closest unpublished or public-repository results:** none.
- **Relation:** possibly a special case of known extremal theory for given binomial moments; the specific statement and its use for digit statistics were not located. Priority not claimed.
- **Search record:** web query (ii); the Sibuya framework surfaced there.
- **Dependencies and outstanding review:** a probabilist should check whether Theorem 7.1 follows from Sibuya-type results and cite accordingly; the Jordan-truncation argument of Theorem 7.5.

### Theorems 8.2 and 8.3: Selberg–Vaaler degree and the degree-110 barrier
- **Statement and hypotheses:** the degree-116 Selberg–Vaaler majorant of `1_{[1/2,1)}` has `Q_∞`-mean ≤ 0.4999592; a positive measure with the model's Fourier coefficients for `|m| ≤ 110` charges `[1/2,1]` with mass ≥ 0.500192.
- **Evidence:** finite certificates (floating point with explicit radii).
- **Earliest relevant literature:** Vaaler (1985), *Some extremal functions in Fourier analysis*, Bull. AMS 12 (majorants/minorants of intervals; Selberg's earlier construction is attributed there; **theorem numbers not verified by us**).
- **Closest published results:** the majorant inequality itself (external input).
- **Closest unpublished or public-repository results:** none.
- **Relation:** the use of the majorant for a Fourier-side sufficiency criterion and the dual measure for the barrier are computations of ours; the extremal functions are inherited.
- **Search record:** none beyond bibliographic check.
- **Dependencies and outstanding review:** interval-arithmetic recomputation; confirm the majorant coefficient formula against Vaaler's text.

### Proposition 10.1: Crandall audit
- **Statement and hypotheses:** exact digits agree with Crandall's abstract and Table 1 (`e_{10^10}=e_{10^20}=0`); §6 tables are internally consistent; the orientation (0/1 labels) of the `2^43` counts cannot be decided from data below `2^24`.
- **Evidence:** finite certificate.
- **Earliest relevant literature:** Crandall (2012) §6–§7 (the only source of the table; Mitchell's output is not public to our knowledge).
- **Closest published results:** none.
- **Closest unpublished or public-repository results:** none located.
- **Relation:** an audit; no claim that the table is wrong. An earlier internal remark that labels appear interchanged is withdrawn.
- **Search record:** web query (iii) found no independent reproduction of Mitchell's counts.
- **Dependencies and outstanding review:** certified shell frequencies to `s ≈ 30`, or Mitchell's raw output.
