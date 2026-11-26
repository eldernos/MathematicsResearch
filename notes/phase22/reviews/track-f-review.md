# Independent Cross-Provider Audit: Phase 22 Track F (Permanent Objectives & 50-Constant Benchmark Suite)

- **Reviewer**: Independent cross-provider audit sub-agent (Gemini 4 Neon)
- **Date**: 2026-11-26
- **Scope**:
  1. `docs/research-objectives.md`
  2. `docs/benchmarks/SCHEMA.md`
  3. `docs/benchmarks/classical-constants.toml` (`BC-01`–`BC-50`)
  4. `docs/benchmarks/arithmetic-families.toml` (`BF-01`–`BF-25`)
- **Cross-checked against**: all 198 entries across `docs/registry/*.toml` (116 distinct registry identifiers cited), `scripts/portal.py`, numerical/identity verification scripts, and external mathematical literature.
- **Note on review status**: **Cross-model review is not independent human peer review.** This report records an automated cross-provider verification and does not substitute for refereeing by independent human mathematicians.

---

## Overall Verdict: **REVISE**

The mathematical core of Track F is strong and remarkably disciplined: all 50 constants (`BC-01`–`BC-50`) are genuinely proved irrational, all stated decimal prefixes and algebraic/analytic identities check out cleanly, all 116 cited `registry_ids` exist in `docs/registry/*.toml` with no `withdrawn` or `computation` entries, zero forbidden characters (`\`, `$`, `*`, `` ` ``, `|`) appear in any TOML string field, and the distributional statuses faithfully reflect the verified Phase 21 baseline without overclaiming.

However, **6 Major findings** (and 6 Minor polish items) prevent an immediate `ACCEPT`:
- an active `portal.py check` failure due to missing `docs/benchmarks/progress.md` and unimplemented benchmark checks in `scripts/portal.py` (**M1**);
- a policy contradiction between `docs/research-objectives.md` Rule 4 and how `evidence` is actually assigned across both TOML files (**M2**);
- three `evidence = "lean+paper"` assignments (`BC-45`, `BC-46`, `BF-21`) that violate `SCHEMA.md` because none of their listed `registry_ids` has registry status `lean+paper` (**M3**);
- a definition bug in `BF-24` (BBP-type constants) that admits trivial rational sums while declaring all four distributional statuses `open` (**M4**);
- two mathematical precision slips (`research-objectives.md` dropping $\mu' > \mu$ in the `CC-50` window bound, and `BF-05` dropping the integer scaling $L$ in `CR-04`) (**M5**);
- six `external_sources` entries omitting publication/release years in violation of `SCHEMA.md` (**M6**).

All six Major findings have direct, self-contained fixes.

---

## 1. Audit of `docs/research-objectives.md`

### 1.1 Definitions, Implication Chains, and Witnesses

- **Base-$b$ expansion & word occurrence (lines 12–18)**: Sound. With the canonical expansion not ending in an infinite run of $b - 1$, $d_{n+1}\cdots d_{n+L} = w \iff \{b^n x\} \in I_w$ (half-open $b$-adic interval of length $b^{-L}$).
- **Discrepancy & translation kernel $K_b$ (lines 22–45)**: Sound. The identity
  $$\sup_{y \in \mathbb{R}} |D_N(y + z; b) - D_N(y; b)| = 1 - D_N(z; b)$$
  is kernel-verified in `GF-05` (`NormalityChecker.SharpTranslation.sharp_translation_isGreatest`) and matches the definition $K_b = \{z : D_N(z; b) \to 1\}$.
- **Positive implication chains (lines 53–58)**:
  - `normal ⇒ L-normal ⇒ ℓ-normal (ℓ ≤ L) ⇒ simply normal`: **Valid.**
  - `normal ⇔ D⁺ = 0 ⇒ D⁺ < 1 ⇒ D⁻ < 1 ⇔ x ∉ K_b`: **Valid** (since $0 \le D_N \le 1$, $D_N \to 1 \iff D^- = 1$).
  - `normal ⇒ disjunctive`: **Valid.**
- **Counterexample / independence witness table (lines 60–72)**:
  - All 9 individual witnesses check out against their cited registry entries (`GF-03`, `GF-04`, `DS-01`, `CC-48`, `CC-04`, `CC-46`). In particular, for Row 3 (`DS-01`), alternating blocks of consecutive zero-phase shells and nonzero-phase shells whose block lengths both tend to $\infty$ satisfy $Z(p^{B_m})/p^{B_m} \ge 1 - p^{-k_m} \to 1$ and $Z(p^{C_m})/p^{C_m} \le p^{-l_m} \to 0$, giving $D^- = 0$ and $D^+ = 1$.
  - **Gap noted (Minor m1)**: Line 72 claims simple normality is independent of $K_b$, but no row explicitly witnesses **(not simply normal, not in $K_b$)** (note that $1/3 = 0.\overline{01}_2$ in Row 7 *is* simply normal in base 2).
- **Objective 4 limitation citations (lines 111–120)**: All cited registry IDs (`AC-10`, `CC-02`, `CC-43`, `CC-49`, `GF-17`, `GF-18`, `CC-50`, `AC-11`) exist and match their statements, except the dropped $\mu' > \mu$ quantifier on line 118 (**M5**) and the minor omission of `CC-42` alongside `CC-43` on line 114 (**m6**).

---

## 2. Verification of the 50 Classical Constants (`BC-01`–`BC-50`) and 25 Families (`BF-01`–`BF-25`)

### 2.1 Irrationality and Classical Attribution Audit

Every constant `BC-01`–`BC-50` was verified to be **genuinely proved irrational**, and every printed decimal prefix and identity was verified numerically to full displayed precision (including `BC-07`'s minimal polynomial, `BC-13`'s $\log((3+4i)/5)$ and Machin identity, `BC-21`'s $[0; 1, 2, 3, \dots] = I_1(2)/I_0(2) = 0.697774657964\dots$, `BC-24`/`BC-25`/`BC-26`'s $L$-series class-number values, `BC-33`/`BC-34`/`BC-38`/`BC-39`/`BC-40`/`BC-42`'s series and $q$-digamma identities).

#### Verification of the Specifically Flagged Attributions

| Constant(s) | Attribution in TOML | Verification Result |
| --- | --- | --- |
| `BC-21`: $[0; 1, 2, 3, \dots] = I_1(2)/I_0(2)$ | Siegel 1929 (algebraic independence of $J_0(\xi), J_0'(\xi)$ at nonzero algebraic $\xi$) | **Accurate.** $I_0(z) = J_0(iz)$ and $I_1(z) = I_0'(z) = i J_0'(iz)$, so $I_1(2)/I_0(2) = i J_0'(2i)/J_0(2i)$ with $\xi = 2i$ nonzero algebraic; Siegel (1929) proves algebraic independence of $J_0(\xi)$ and $J_0'(\xi)$, hence transcendence of the ratio. The recurrence $I_{n-1}(2)/I_n(2) = n + I_{n+1}(2)/I_n(2)$ confirms $[0; 1, 2, 3, \dots] = I_1(2)/I_0(2)$, and $a_n = n$ implies $\log a_{n+1} = o(\log q_n)$, hence $\mu = 2$. |
| `BC-45`: $\sum_{k \ge 0} 2^{-2^k}$ | Kempner 1916; Mahler 1929; Shallit 1979 (bounded partial quotients, so $\mu = 2$) | **Accurate.** Shallit (*J. Number Theory* **11** (1979), 209–217) treated $B(u, \infty) = \sum_{k \ge 0} u^{-2^k}$ including $u = 2$ (resolving zero partial quotients by contraction), proving bounded partial quotients (in $\{1, 2, 4, 6\}$) and hence $\mu = 2$. |
| `BC-19`, `BC-20`: $\Gamma(1/4)$, $\Gamma(1/3)$ | G. V. Chudnovsky; Nesterenko 1996 | **Mathematically accurate, year omitted (M6).** G. V. Chudnovsky (**1976**, *Dokl. Akad. Nauk Ukr. SSR*) proved algebraic independence of $\pi$ and $\Gamma(1/4)$ and of $\pi$ and $\Gamma(1/3)$ via CM elliptic periods; Nesterenko (**1996**) extended these to algebraic independence of $\{\pi, e^\pi, \Gamma(1/4)\}$ and $\{\pi, e^{\pi\sqrt{3}}, \Gamma(1/3)\}$. Add `1976` to both `arithmetic_nature` and `external_sources`. |
| `BC-49`, `BF-01`: $\alpha(2, 3)$ and Stoneham numbers | Stoneham 1973; Bailey–Crandall 2002; Ridout 1957 | **Accurate.** Stoneham (1973) proved $b$-normality of $\alpha(b, p)$ for odd primes $p$ when $b$ is a primitive root mod $p^2$ (covering $\alpha(2, 3)$ since $2$ is a primitive root mod $9$), and Bailey–Crandall (2002) proved $b$-normality for all coprime $b, c \ge 2$. Note that for $\alpha(2, 3)$ even Roth (1955) already implies transcendence (error $\approx q^{-3+o(1)}$), while Ridout (1957) is stronger and also covers $c = 2$. |
| `BC-42`: $\psi = \sum_{n \ge 1} 1/F_n$ | André-Jeannin 1989 (irrational) | **Accurate (no DNNS overclaim).** `BC-42` rightly credits only André-Jeannin (1989) for irrationality of $\sum_{n \ge 1} 1/F_n$ and does **not** falsely attribute transcendence to Duverney–Nishioka–Nishioka–Shiokawa (1996/1997), who proved transcendence for modularly expressible subseries such as $\sum 1/F_{2sn}$ and even powers $\sum 1/F_n^{2s}$, while transcendence of $\sum_{n \ge 1} 1/F_n$ itself remains open. (Recommend adding `"; transcendence open"` in **m3**.) |

#### Other Notable Attribution Checks
- `BC-01`–`BC-07`: Bailey–Borwein–Crandall–Pomerance (2004) ($\ge c N^{1/d}$ binary 1-bits) and Adamczewski–Bugeaud (2007) ($p(n)/n \to \infty$): **Accurate.**
- `BC-08` ($\pi$): Lambert (1761), Lindemann (1882), BBP (1997), Zeilberger–Zudilin (2020) ($\mu(\pi) \le 7.103205334137$): **Accurate.**
- `BC-12` ($\pi^2$): Legendre (1794, *Éléments de géométrie*) and Lindemann (1882): **Accurate.**
- `BC-14` ($e^\pi$): Citing Gelfond–Schneider (1934) is valid, though **Gelfond (1929)** first proved $e^\pi$ transcendental five years earlier (**m3**).
- `BC-16` ($e$): Euler (1737/1744) gave the continued fraction and irrationality; phrasing should avoid attributing the modern measure $\mu(e) = 2$ directly to Euler 1744 (**m3**).
- `BC-22` ($\zeta(3)$): Apéry (1978), transcendence open: **Accurate.**
- `BC-24`–`BC-26`: Dirichlet (1839) class number formula + Lindemann (1882): **Accurate.**
- `BC-27`–`BC-32`, `BC-36`, `BC-43`: Nesterenko (1996) algebraic independence of $P(q), Q(q), R(q)$ at algebraic $0 < |q| < 1$; Jacobi (1829) cube identity; Euler pentagonal number theorem (add year `1750` / `1760`, **M6**): **Accurate.**
- `BC-33`–`BC-35`: Duverney–Nishioka–Nishioka–Shiokawa (1996) (*Proc. Japan Acad.* 72, 202–203) and Nesterenko (1996): **Accurate.**
- `BC-37`–`BC-39`: Erdős (1948) for $E$; Borwein (1991, *J. Number Theory* 37, 253–259) for $\sum 1/(q^n + r)$ with integer $|q| > 1$ and nonzero rational $r \ne -q^n$ (covering $E_{\text{odd}}$ via $q=4, r=-2$ and $E_+$ via $q=2, r=1$): **Accurate.**
- `BC-40`, `BC-41`: Hamieh–Murty (2016, *Int. J. Number Theory* 12, 765–773, *"A Note on $q$-Analogues of Dirichlet $L$-Functions"*) proves transcendence for odd characters $\chi$ (both $\chi_4$ and $\chi_{-3}$ are odd). Note `BC-40` = $(\Theta_3(1/2)^2 - 1)/4$ was already transcendental by DNNS/Nesterenko (1996) (**m3**).
- `BC-44`: Davison–Shallit (1991, *Monatsh. Math.*) for Cahen's constant transcendence: **Accurate.**
- `BC-46`–`BC-48`: Liouville (1844), Champernowne (1933) / Mahler (1937), Copeland–Erdős (1946; transcendence open): **Accurate.**

### 2.2 Registry Cross-Reference & Schema Compliance Audit

Automated verification against all 198 entries in `docs/registry/*.toml` and all rules in `docs/benchmarks/SCHEMA.md` confirmed:
- Exact `[meta]` headers (`schema_version = 1`, `status_as_of = "Phase 21"`, `roster_size = 50`).
- Exact consecutive IDs `BC-01`–`BC-50` (50 entries) and `BF-01`–`BF-25` (25 entries), unique names, exact required field sets.
- Valid enum values and `radices_scope` patterns on all 75 entries.
- Zero forbidden characters (`\`, `$`, `*`, `` ` ``, `|`) across all string and list-of-string fields.
- All 116 cited registry IDs exist in `docs/registry/*.toml`; zero entries have status `withdrawn` or `computation`.
- All logical implication rules (SCHEMA § Mechanical checks, rule 6) and structural presence rules (rules 7–8) hold mechanically.
- Distributional statuses match the verified Phase 21 baseline conservatively without overclaiming (in particular `BC-37` keeps `discrepancy_status = "open"` and does not promote `CC-21` to $D^+(E; 2) < 1$ prior to independent verification, matching `GF-18`).

The specific violations and defects uncovered by the semantic and tooling checks are detailed below.

---

## 3. Detailed Findings

### Critical Findings

*None.*

---

### Major Findings

#### M1 — Missing `docs/benchmarks/progress.md` and Unimplemented `scripts/portal.py` Checks Cause `portal.py check` to Fail
- **Files**: [docs/research-objectives.md:152](file:///C:/Users/chaos/.t3/worktrees/MathematicsResearch/research-phase-20-gener-b08235755636abff/docs/research-objectives.md#L152), [docs/benchmarks/SCHEMA.md:10](file:///C:/Users/chaos/.t3/worktrees/MathematicsResearch/research-phase-20-gener-b08235755636abff/docs/benchmarks/SCHEMA.md#L10), [docs/benchmarks/SCHEMA.md:128-158](file:///C:/Users/chaos/.t3/worktrees/MathematicsResearch/research-phase-20-gener-b08235755636abff/docs/benchmarks/SCHEMA.md#L128-L158), [scripts/portal.py](file:///C:/Users/chaos/.t3/worktrees/MathematicsResearch/research-phase-20-gener-b08235755636abff/scripts/portal.py)
- **Finding**: Both `docs/research-objectives.md` and `docs/benchmarks/SCHEMA.md` link to `docs/benchmarks/progress.md` and state that `python3 scripts/portal.py build` generates it and `python3 scripts/portal.py check` enforces the eight mechanical benchmark checks. Running `python scripts/portal.py check --skip-figures` currently fails with:
  - `error: docs/benchmarks/SCHEMA.md: missing target progress.md`
  - `error: docs/research-objectives.md: missing target benchmarks/progress.md`
  and `scripts/portal.py` contains no benchmark loader, validator, or `progress.md` builder yet.
- **Actionable Fix**: Implement the benchmark validator (enforcing SCHEMA rules 1–8) and `docs/benchmarks/progress.md` generator in `scripts/portal.py`, run `python3 scripts/portal.py build`, and verify `python3 scripts/portal.py check` passes with exit code 0 before committing Track F.

#### M2 — Policy Contradiction on `External input` / `evidence = "external"` (Rule 4 vs. Registry & Benchmark Usage)
- **Files**: [docs/research-objectives.md:125-142](file:///C:/Users/chaos/.t3/worktrees/MathematicsResearch/research-phase-20-gener-b08235755636abff/docs/research-objectives.md#L125-L142), [docs/benchmarks/SCHEMA.md:114-122](file:///C:/Users/chaos/.t3/worktrees/MathematicsResearch/research-phase-20-gener-b08235755636abff/docs/benchmarks/SCHEMA.md#L114-L122), and entries `BC-27`–`BC-30`, `BC-34`, `BC-40`, `BC-41`, `BF-08`, `BF-11`, `BF-12`, `BF-15`, `BF-16`, `BF-19`, `BF-20`
- **Finding**: `docs/research-objectives.md` line 125 states *"Every result in the repository carries **exactly one** of these labels"*, puts `External input | inputs field | external` in the table (line 134), and Rule 4 (line 142) mandates: *"A result that rests on an external input carries that label even when the rest of the argument is kernel-verified."* Literally applied, this contradicts both the registry (`docs/registry/*.toml`, where `inputs` is an orthogonal metadata field on `lean+paper` and `paper` entries) and the benchmark TOMLs, where `BC-27`/`BC-28` (Euler's pentagonal number theorem), `BC-29` (Serre 1981/1985), `BC-30` (Jacobi 1829), `BC-34`/`BC-40`/`BC-41`/`BF-15` (Perelli–Pintz–Salerno 1985, Shiu 1980, Wirsing 1961, Selberg sieve), `BF-12` (Deligne–Serre 1974, Chebotarev 1926), `BF-16` (Wirsing/Dirichlet), `BF-19` (Titchmarsh), and `BF-20` (Ford–Luca–Pomerance) all rest on external published theorems listed in `inputs`/`external_sources`, yet carry `evidence = "lean+paper"` or `"paper"` rather than `"external"`. In practice, `evidence = "external"` is reserved for cases where the *distributional benchmark status itself* is a published/released external theorem not proved in the repository (`BC-37`, `BC-47`, `BC-48`, `BF-18`).
- **Actionable Fix**: Revise `docs/research-objectives.md` (§ Evidence labels table and Rule 4) and `docs/benchmarks/SCHEMA.md` (§ Evidence values) to separate the two concepts cleanly:
  1. `evidence = "external"` applies when a **distributional status itself** is established by an external theorem cited as a black box rather than proved in the repository (`BC-37`, `BC-47`, `BC-48`, `BF-18`).
  2. Named classical theorems used as **ingredients** inside an in-repository `lean+paper` or `paper` proof are recorded in the registry `inputs` field (and `external_sources`), without overriding the proof's `lean+paper`/`paper` label (while explicitly noting that a result resting on an external input is never labeled pure `lean`).

#### M3 — `evidence = "lean+paper"` Violates `SCHEMA.md` on `BC-45`, `BC-46`, and `BF-21`
- **Files**: [docs/benchmarks/classical-constants.toml:926-928](file:///C:/Users/chaos/.t3/worktrees/MathematicsResearch/research-phase-20-gener-b08235755636abff/docs/benchmarks/classical-constants.toml#L926-L928) (`BC-45`), [docs/benchmarks/classical-constants.toml:948-950](file:///C:/Users/chaos/.t3/worktrees/MathematicsResearch/research-phase-20-gener-b08235755636abff/docs/benchmarks/classical-constants.toml#L948-L950) (`BC-46`), [docs/benchmarks/arithmetic-families.toml:373-374](file:///C:/Users/chaos/.t3/worktrees/MathematicsResearch/research-phase-20-gener-b08235755636abff/docs/benchmarks/arithmetic-families.toml#L373-L374) (`BF-21`), [docs/benchmarks/SCHEMA.md:114-120](file:///C:/Users/chaos/.t3/worktrees/MathematicsResearch/research-phase-20-gener-b08235755636abff/docs/benchmarks/SCHEMA.md#L114-L120)
- **Finding**: `SCHEMA.md` line 119 states `evidence = "lean+paper"` means *"The weakest needed result has registry status `lean+paper`."* Yet `BC-45` (Kempner–Fredholm), `BC-46` (Liouville's constant), and `BF-21` (Lacunary 0–1 series) all set `evidence = "lean+paper"` while listing only `registry_ids = ["GF-01", "GF-02"]`, whose registry statuses are `GF-01` = `lean` and `GF-02` = `paper`. Neither is `lean+paper`. Moreover, `GF-01` proves the generic sparse linear-mass transfer in Lean, while applying it to lacunary 0–1 series and concluding simple nonnormality and non-disjunctivity is a written specialization (and `GF-02` is `paper`).
- **Actionable Fix**: Either change `evidence` to `"paper"` on `BC-45`, `BC-46`, and `BF-21` (reflecting that `GF-02` is `paper` and the lacunary specialization/digit-frequency/non-disjunctivity steps are written arguments), OR add a dedicated `lean+paper` registry entry for lacunary 0–1 series specializing `GF-01` and cite it. (Related transparency note: on `BC-29` $E_2^2$, `GF-04` and `GF-12` have bundle status `lean+paper`, but `GF-04` Scope explicitly states *"Nothing about $E_b^2$ (coefficients, support or $K_b$-membership) is formalized"* — add a brief note in `BC-29.notes` so readers are not misled into thinking $E_2^2$ itself is formalized.)

#### M4 — `BF-24` (BBP-Type Polylogarithmic Constants) Admits Rational Numbers Under All-`open` Statuses
- **File**: [docs/benchmarks/arithmetic-families.toml:424-433](file:///C:/Users/chaos/.t3/worktrees/MathematicsResearch/research-phase-20-gener-b08235755636abff/docs/benchmarks/arithmetic-families.toml#L424-L433)
- **Finding**: `BF-24.definition` defines the family as *"$\sum_{k \ge 0} p(k)/(q(k) b^k)$ for integer polynomials $p$ and $q$, with $q$ free of zeros at nonnegative integers"* while setting all four distributional statuses to `open`. As stated, this family includes rational constants — e.g. $p = 1, q = 1$ (giving $b/(b-1)$), $p = 0$ (giving $0 \in K_b$), and telescoping sums such as $\sum_{k \ge 0} \frac{(b-1)k + 2b - 1}{(k+1)(k+2)b^k} = b$ — which are provably nonnormal and non-disjunctive.
- **Actionable Fix**: Amend `BF-24.definition` to exclude rational sums explicitly, e.g.: *"Irrational constants of the form Σ_{k ≥ 0} p(k)/(q(k) b^k) for integer polynomials p and q with deg p < deg q and q free of zeros at nonnegative integers; this includes π, ln 2 and π² in suitable powers-of-two radices."*

#### M5 — Two Mathematical Precision Slips Against Cited Registry Statements (`research-objectives.md` Line 118 and `BF-05` Summary)
- **Files**: [docs/research-objectives.md:118](file:///C:/Users/chaos/.t3/worktrees/MathematicsResearch/research-phase-20-gener-b08235755636abff/docs/research-objectives.md#L118), [docs/benchmarks/arithmetic-families.toml:90](file:///C:/Users/chaos/.t3/worktrees/MathematicsResearch/research-phase-20-gener-b08235755636abff/docs/benchmarks/arithmetic-families.toml#L90)
- **Findings**:
  1. **Dropped strict inequality $\mu' > \mu$ (`docs/research-objectives.md:118`)**: The text states *"a finite irrationality exponent $\mu$ bounds every rational shadowing window by $(\mu - 1)N + \mu \log_2 q_N + O(1)$"*. This drops the $\mu' > \mu$ quantifier from `CC-50` (*"for any finite irrationality exponent $\mu' > \mu(\ln 2)$ ... $T_N \le (\mu' - 1)N + \mu' \log_2 q_N + O_{\mu'}(1)$"*). At $\mu' = \mu$ the $O(1)$ error term can fail: e.g. $\mu(e) = 2$ while convergents of $e$ satisfy $|e - p_n/q_n| \asymp (q_n^2 \log q_n / \log\log q_n)^{-1}$, adding an unbounded $\log\log q_N$ term.
  2. **Omitted integer scaling $L$ (`arithmetic-families.toml:90`, `BF-05.summary`)**: The text states *"Resonant sums have explicit weak limits $(1 - w)\lambda + w \delta_0$ along $N = S p^k$, and one sum can have two different limiting distributions (CR-04)."* However, `CR-04` Scope explicitly states: *"The limit is the weak limit of the empirical measures of the integer-scaled orbit $b^n L F$ modulo one, not of $F$ itself."*
- **Actionable Fix**:
  1. In `docs/research-objectives.md:118`, change to: *"a finite irrationality exponent μ implies that for every μ′ > μ, every rational shadowing window is bounded by (μ′ − 1)N + μ′ log₂ q_N + O_{μ′}(1)..."*
  2. In `arithmetic-families.toml:90`, change to: *"Integer-scaled orbits {bⁿ L F} of resonant sums have explicit weak limits (1 − w) λ + w δ_0 along N = S p^k, and one sum can have two different limiting distributions (CR-04)."*

#### M6 — Missing Publication/Release Years in Six `external_sources` Entries (Violates `SCHEMA.md` Line 49)
- **Files**: [docs/benchmarks/SCHEMA.md:49](file:///C:/Users/chaos/.t3/worktrees/MathematicsResearch/research-phase-20-gener-b08235755636abff/docs/benchmarks/SCHEMA.md#L49), `classical-constants.toml` (`BC-19`, `BC-20`, `BC-27`, `BC-28`, `BC-37`), `arithmetic-families.toml` (`BF-08`, `BF-18`)
- **Finding**: `SCHEMA.md` line 49 requires every `external_sources` string to name *"the author(s), the year and the statement."* The following entries omit the year:
  - `BC-19.external_sources[0]`: `"G. V. Chudnovsky: algebraic independence of π and Γ(1/4)"` (and `BC-19.arithmetic_nature`)
  - `BC-20.external_sources[0]`: `"G. V. Chudnovsky: algebraic independence of π and Γ(1/3)"` (and `BC-20.arithmetic_nature`)
  - `BC-27.external_sources[0]`, `BC-28.external_sources[0]`, `BF-08.external_sources[0]`: `"Euler, pentagonal number theorem..."`
  - `BC-37.external_sources[1]` and `BF-18.external_sources[2]`: `"Captain Sude, elementary Lean release: ..."`
- **Actionable Fix**: Add the missing years (`G. V. Chudnovsky 1976`, `Euler 1750` or `Euler 1750/1760`, and the release year/date + commit/identifier for Captain Sude's Lean release), and add a mechanical year-check (or explicit format convention) in `scripts/portal.py`.

---

### Minor Findings

#### m1 — Missing Witness for `(not simply normal, not in K_b)` in `docs/research-objectives.md` Independence Table
- **File**: [docs/research-objectives.md:60-72](file:///C:/Users/chaos/.t3/worktrees/MathematicsResearch/research-phase-20-gener-b08235755636abff/docs/research-objectives.md#L60-L72)
- **Finding**: Line 72 concludes that simple normality is independent of membership in $K_b$, but the table contains no explicit witness for *(not simply normal, not in $K_b$)* ($1/3 = 0.\overline{01}_2$ in Row 7 is simply normal in base 2).
- **Actionable Fix**: Add a row for *"Not simply normal, not disjunctive, not in $K_b$"* with witness $1/7 = 0.\overline{001}_2$ in base 2 (digit 1 has frequency $1/3 \ne 1/2$, the word `11` never occurs, and $D_\infty(1/7; 2) = 4/7 < 1$).

#### m2 — Imprecise Statement on Multiplicatively Independent Bases
- **File**: [docs/research-objectives.md:49](file:///C:/Users/chaos/.t3/worktrees/MathematicsResearch/research-phase-20-gener-b08235755636abff/docs/research-objectives.md#L49)
- **Finding**: *"Normality in base $b$ implies normality in every base $b^k$, but no implication is known between multiplicatively independent bases for the constants studied here."* Normality in base $b$ is in fact *equivalent* to normality in base $b^k$ (Maxfield 1953), whereas between multiplicatively independent bases the general implication is *provably false* (Schmidt 1960), not merely unknown; what is open is second-base normality of the explicit constants studied here.
- **Actionable Fix**: Reword to: *"Normality in base b is equivalent to normality in every base b^k; between multiplicatively independent bases no general implication holds (Schmidt 1960), and no explicit constant studied here is known to be normal in two multiplicatively independent bases."*

#### m3 — Historical Attribution & Open-Transcendence Consistency Polish
- **File**: [docs/benchmarks/classical-constants.toml](file:///C:/Users/chaos/.t3/worktrees/MathematicsResearch/research-phase-20-gener-b08235755636abff/docs/benchmarks/classical-constants.toml)
- **Findings**:
  1. `BC-14` ($e^\pi$): Credit **Gelfond (1929)** first (with Gelfond–Schneider 1934 as the general theorem), since Gelfond proved $e^\pi$ transcendental five years before 1934.
  2. `BC-16` ($e$): Change `"Euler 1744: continued fraction ..., hence irrationality and μ(e) = 2"` to `"Euler 1744: continued fraction ..., proving irrationality (and implying μ(e) = 2)"` to avoid anachronistically attributing the irrationality exponent $\mu(e) = 2$ to Euler 1744.
  3. `BC-38`, `BC-39`, `BC-42`, `BC-48`: Add `"; transcendence open"` to `arithmetic_nature` to match `BC-22` and `BC-37` (particularly helpful on `BC-42` $\psi = \sum 1/F_n$ and `BC-48` Copeland–Erdős).
  4. `BC-40` ($L_{\chi_4}(2)$): Note DNNS/Nesterenko (1996) alongside Hamieh–Murty (2016) for consistency with `BC-34`, since $L_{\chi_4}(2) = (\Theta_3(1/2)^2 - 1)/4$.
  5. `BC-33` ($\Theta_3(1/2)$): Cite `GF-17` (which kernel-verifies `deriv_thetaThree_discrepancy_tendsto_one`, giving $\Theta_3(1/b) \in K_b$ directly at $j=0$) inside `discrepancy_summary` alongside `GF-01`, `GF-02`.

#### m4 — `registry_ids` Scope Alignment (`BC-36`, `BC-43`, `BC-37`, and Inline Cross-References)
- **Files**: [docs/benchmarks/SCHEMA.md:48](file:///C:/Users/chaos/.t3/worktrees/MathematicsResearch/research-phase-20-gener-b08235755636abff/docs/benchmarks/SCHEMA.md#L48), `classical-constants.toml` (`BC-09`, `BC-23`, `BC-36`, `BC-37`, `BC-43`, `BC-46`), `arithmetic-families.toml` (`BF-01`)
- **Finding**:
  - `BC-36` ($E_4(1/2)$) and `BC-43` ($\sum \sigma(n) 2^{-n}$) have all four statuses `open` and `barrier_status = "no_barrier_recorded"`, yet list `registry_ids = ["GF-08", "GF-17"]`, whereas `SCHEMA.md` line 48 restricts `registry_ids` to entries *"that prove a status or a barrier for this constant."*
  - `BC-37` includes `CC-35` (conditional on Mira Cult's theorem) and `CC-47` (mesoscopic correlation conditional on Kubilius K2) in `registry_ids`.
  - Four entries mention comparative registry IDs inline that are not in `registry_ids`: `BC-09` (`LS-01`), `BC-23` (`DS-03`, `DS-10`), `BC-46` (`GF-10`, `OP-09`), `BF-01` (`ST-10`).
- **Actionable Fix**: Broaden `SCHEMA.md` line 48 to *"Registry identifiers (`docs/registry/*.toml`) that prove a status, barrier, or structural reduction for this constant"* (covering `BC-36`/`BC-43`/`BC-37`), and note in `SCHEMA.md` that comparative cross-references in `notes`/`open_frontier` need not be added to `registry_ids` (while still being checked for existence in `docs/registry/*.toml`).

#### m5 — `barrier_status = "resolved"` Paired with `discrepancy_status = "partial"` on `BF-05` and `BF-10`
- **Files**: [docs/benchmarks/SCHEMA.md:108,140](file:///C:/Users/chaos/.t3/worktrees/MathematicsResearch/research-phase-20-gener-b08235755636abff/docs/benchmarks/SCHEMA.md#L108), `arithmetic-families.toml` (`BF-05`, `BF-10`)
- **Finding**: Under `SCHEMA.md` line 140, `barrier_status = "resolved"` holds whenever `full_normality ∈ {proved_normal, proved_nonnormal, classified}` and `discrepancy_status ≠ open`. This allows `BF-05` and `BF-10` to be marked `resolved` even though `discrepancy_status = "partial"` (exact all-prefix $D^+/D^-$ of resonant sums in `BF-05` and non-all-minus signs in `BF-10` remain open).
- **Actionable Fix**: Either clarify in `SCHEMA.md` line 108 that for families `resolved` means full normality is completely decided and discrepancy is at least partially settled, or tighten `resolved` to require `discrepancy_status ∉ {open, partial}` (changing `BF-05` and `BF-10` to `no_barrier_recorded`).

#### m6 — Small Clarity Improvements in `SCHEMA.md`, `research-objectives.md`, and `BF-21`
- **Files**: [docs/benchmarks/SCHEMA.md:153](file:///C:/Users/chaos/.t3/worktrees/MathematicsResearch/research-phase-20-gener-b08235755636abff/docs/benchmarks/SCHEMA.md#L153), [docs/research-objectives.md:114](file:///C:/Users/chaos/.t3/worktrees/MathematicsResearch/research-phase-20-gener-b08235755636abff/docs/research-objectives.md#L114), [docs/benchmarks/arithmetic-families.toml:366](file:///C:/Users/chaos/.t3/worktrees/MathematicsResearch/research-phase-20-gener-b08235755636abff/docs/benchmarks/arithmetic-families.toml#L366)
- **Actionable Fixes**:
  1. `SCHEMA.md:153`: Add a sentence noting that the four objective rows in the `progress.md` summary table overlap (e.g., `BC-27` $E_2$ and `BC-30` $E_2^3$ are simultaneously proved simply normal [Objective 1], proved nonnormal [Objective 2], and in $K_2$ [Objective 3]), so the counts do not sum to 50.
  2. `docs/research-objectives.md:114`: Cite `([CC-42](results.md#cc-42), [CC-43](results.md#cc-43))` together for the balanced algebraic trace-source 5/12 lower bound.
  3. `arithmetic-families.toml:366` (`BF-21.definition`): Specify *"a strictly increasing sequence of positive integers $(n_k)$"* (and note $k \ge 0$ for $\sum_{k \ge 0} 2^{-2^k}$ to match `BC-45`).

---

## Post-Repair Verification

- **Date**: 2026-11-26
- **Files re-audited**:
  1. [docs/research-objectives.md](file:///C:/Users/chaos/.t3/worktrees/MathematicsResearch/research-phase-20-gener-b08235755636abff/docs/research-objectives.md)
  2. [docs/benchmarks/SCHEMA.md](file:///C:/Users/chaos/.t3/worktrees/MathematicsResearch/research-phase-20-gener-b08235755636abff/docs/benchmarks/SCHEMA.md)
  3. [docs/benchmarks/classical-constants.toml](file:///C:/Users/chaos/.t3/worktrees/MathematicsResearch/research-phase-20-gener-b08235755636abff/docs/benchmarks/classical-constants.toml)
  4. [docs/benchmarks/arithmetic-families.toml](file:///C:/Users/chaos/.t3/worktrees/MathematicsResearch/research-phase-20-gener-b08235755636abff/docs/benchmarks/arithmetic-families.toml)
  5. [docs/benchmarks/progress.md](file:///C:/Users/chaos/.t3/worktrees/MathematicsResearch/research-phase-20-gener-b08235755636abff/docs/benchmarks/progress.md)
- **Command verified**: `python -B scripts/portal.py check --strict --skip-figures` exited `0`:
  `Portal verified: 198 registered results, 247 Markdown files, links, anchors, identifiers, topics and figures.`
- **Independent count check**: Recomputed all `docs/benchmarks/progress.md` tables directly from the TOML files:
  - Objective summary: Objective 1 = `5`, Objective 2 = `10`, Objective 3 = `14`, Objective 4 = `11`, All four open = `35` — exact match.
  - Per-category counts across all 8 categories — exact match on every cell (`Total`, `Normal`, `Nonnormal`, `In K_b`, `Barrier proved`, `All open`).

### Resolution Checklist

| Finding | Status | Verification |
| --- | --- | --- |
| **M1** (`progress.md` / `portal.py check`) | **Resolved** | `docs/benchmarks/progress.md` generated; `python -B scripts/portal.py check --strict --skip-figures` exits `0`. |
| **M2** (Rule 4 / `external` policy) | **Resolved** | `docs/research-objectives.md:124-144` and `docs/benchmarks/SCHEMA.md:114-124` cleanly separate repo proof labels from black-box `external` statuses and classical `inputs`. |
| **M3** (`lean+paper` evidence consistency) | **Resolved** | `BC-45`, `BC-46`, `BF-21`—and consistently `BC-33` and `BC-50`—now carry `evidence = "paper"` under the tightened `SCHEMA.md:114,143` rule; `BC-29.notes` transparently records that nothing specific to $E_b^2$ is formalized in Lean. |
| **M4** (`BF-24` excluding rationals) | **Resolved** | `arithmetic-families.toml:426` restricts `BF-24` to irrational numbers with $\deg p < \deg q$. |
| **M5** ($\mu' > \mu$ and $L$-scaling) | **Resolved** | `docs/research-objectives.md:119` restores $\mu' > \mu$ and $O_{\mu'}(1)$; `BF-05.summary` (`arithmetic-families.toml:90`) specifies the integer-scaled orbits $\{b^n L F\}$. |
| **M6** (missing years in `external_sources`) | **Resolved** | All 6 entries now carry four-digit years (`G. V. Chudnovsky 1976`, `Euler 1750 (published 1760)`, `Captain Sude 2026, release erdos-borwein-disjunctivity-elementary (8 September 2026, commit d51e93e)`), enforced mechanically by `SCHEMA.md:146`. |
| **m1–m6** (all 6 minor items) | **Resolved** | Added `1/7` witness (`research-objectives.md:69`); Maxfield 1953 / Schmidt 1960 precision (`:49`); `Gelfond 1929`, `Euler 1744`, `; transcendence open`, `DNNS 1996` on `BC-40`, `GF-17` on `BC-33`; `registry_ids` wording and rule 9 (`SCHEMA.md:48,147`); `resolved` tightened to exclude `partial` discrepancy (`BF-05`, `BF-10` updated to `no_barrier_recorded`); overlapping-count note, `CC-42` citation, and `BF-21` positive-integer index wording. |

### Updated Verdict: **ACCEPT**

All Major and Minor findings are cleanly resolved with zero regressions. **Cross-model review is not independent human peer review.**
