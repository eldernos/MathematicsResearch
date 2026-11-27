# Cross-Provider Verification Check: Paper XI Phase 23 Refresh

**Verdict: ACCEPT**

Audited files (read-only):
- `papers/11-generating-functions-digits/paper.tex` (2,661 lines)
- `papers/11-generating-functions-digits/VERIFICATION.md` (203 lines)
- `notes/phase23/reviews/phase22-analytic-audit-classgroups-sieve.md` (121 lines)

*Cross-model review is not independent human peer review.*

---

## Checklist Results

### 1. §5.4 (Theorem 5.14 proof) propagation of Phase 23 Audit 1 repairs — PASS
- **Ramified primes (`paper.tex:1609–1611, 1619, 1633–1635, 1650`):** Both parts (a) and (b) now fix $P_0 \ge \max_{p \mid \Delta} p$ so that every ramified prime is recorded in the local pattern $\pi$ and $w_\psi(\pi)$, ensuring the genus $\gamma$ is determined by $\pi$ and the parities $(m_g \bmod 2)_g$.
- **Common finite modulus replacing exact-count conditioning (`paper.tex:1625–1641, 1651–1656`):** Part (a) removes the exact-count conditioning on $m^{\rm rest}_c$ and replaces it with a single even modulus $M$ divisible by $T_0 = T q_0^{a(H)}$, by $2$, and by the orders in $(\mathcal O/\mathfrak m^t)^\times$ of all unit bases $\psi(\eta_{g_{\rm o}})$ across all coordinates $g$. The bad event $v_{q_0}(h_0 a_C(n)) \ge H$ factors through $\mathbf m(n) \bmod M$; Selberg–Delange gives asymptotic uniformity on the genus-compatible coset $R_\gamma \subset (\mathbb Z/M\mathbb Z)^{\{g\}}$; and the lines $\mathbf r + j\mathbf w$ ($w_{g_1}=1$, supported on $G^2$) partition $R_\gamma$ into fibres of exact size $M$ with at most $\varepsilon M$ bad residues each. Part (b) likewise removes $2^{m_K^>}$ within each fixed kernel $K$ to leave $2$-adic unit bases and applies Lemma 5.13 with the common finite modulus $M$ before taking the union bound over kernels and selecting the minimizer last.
- **Syntax & math:** No mathematical slips or LaTeX syntax errors found.

### 2. Construction-radix scope (`paper.tex:255` & `paper.tex:2036–2037`) — PASS
- **`paper.tex:255` (Theorem F(ii)):** Tightened from *"not simply normal in any base"* to *"not simply normal in base~$b$"*.
- **`paper.tex:2036–2037` (Theorem 7.6, statement beginning at `L2023` / item (a) at `L2026`):** Tightened from *"not simply normal in any base, and in base $2$ its digit $0$ has frequency $1$"* to *"not simply normal in base~$b$, and in base~$2$ (for $b=2$) its digit~$0$ has frequency~$1$"*.
- No unrelated-radix overclaims remain.

### 3. `VERIFICATION.md` Lean pins, release honesty, environment, and disclaimer — PASS
- **Phase 22 Lean 4 declarations (`L22` at `0342f1f`):** All **19** cited `L22` links (15 in `NormalityChecker/SimpleNormalityKernel.lean`, 1 in `NormalityChecker/RadixPowerTower.lean`, 3 in `NormalityChecker/Phase22Cores.lean`) were verified programmatically against both `git show 0342f1f:...` and the active worktree files. Every declaration name and line number matches exactly:
  - `SimpleNormalityKernel.lean`: `interior_fixed_point_margins` (`L320`), `floor_eq_repunit_of_near` (`L406`), `floor_eq_zero_or_top_of_near` (`L414`), `exists_fixed_center_of_deficit` (`L459`), `exists_fixed_center_of_deficit_le` (`L640`), `word_dichotomy_of_deficit` (`L732`), `finite_digit_dichotomy` (`L841`), `not_simply_normal_of_mem_kernel` (`L1049`), `not_normalIn_of_mem_kernel` (`L1169`), `kernel_eventual_dichotomy` (`L1192`), `otherWordCount_le_badTailCount` (`L1710`), `badTail_card_le_linear_mass` (`L2028`), `asymptotic_oriented_tail_transfer` (`L2260`), `nonneg_sparse_zeros_tendsto_one` (`L2334`), `not_simply_normal_of_nonneg_sparse` (`L2386`).
  - `RadixPowerTower.lean`: `coprime_rat_cylinder_margin` (`L928`).
  - `Phase22Cores.lean`: `atom_ne_grid` (`L397`), `eulerAutomaton_iterate_eq` (`L623`), `cubeHeadSum_add_period` (`L758`).
- **Pre-release honesty:** `VERIFICATION.md:3, 155, 196` explicitly note that `paper.tex` still requires `pdflatex` + `bibtex` recompilation and `\evidence{...}` synchronization in §7 before any release.
- **Build/test environment:** `VERIFICATION.md:159, 170` point reproduction to Linux / remote host `hail`, with zero mentions of WSL.
- **Peer-review disclaimer:** `VERIFICATION.md:7` explicitly states `Cross-model review is not independent human peer review.`

### 4. Python LaTeX structural check (`paper.tex` + `references.bib`) — PASS
- Balanced `\begin{...}` / `\end{...}`: **0 errors**.
- Internal references (`\ref` / `\cref` / `\Cref` / `\eqref`): **145** `\label` definitions, **244** reference groups, **0** undefined labels.
- Citations against `papers/11-generating-functions-digits/references.bib`: **38** bib entries, **57** citation groups, **0** undefined citation keys.

---

## Non-Blocking Cosmetic Observations (optional for pre-release polish)
1. `paper.tex:1652` uses the notation $2^{m_K^>}$ in Theorem 5.14(b) without explicitly defining the superscript $>$ (meaning split primes $p > P_0$ with $[\mathfrak p]_{\rm o} \in K$, clear from part (a)).
2. `VERIFICATION.md:155` lists Lemmas 7.1–7.2, Theorems 7.3–7.4, Lemma 7.5 and Lemma 7.13 as still labeled `Paper proof` in `paper.tex`; Theorem 7.6 (`paper.tex:2023`, `\label{thm:nonneg}`) is also currently `\evidence{Paper proof}` in `paper.tex` and should be included when synchronizing §7 `\evidence{...}` macros before release (the checklist item at `VERIFICATION.md:196` already covers all of §7).
