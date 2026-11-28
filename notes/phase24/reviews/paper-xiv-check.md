# Cross-Provider Verification Report: Candidate Paper XIV

- **Target:** Unreleased Candidate Paper XIV (`papers/14-dense-digit-mass-lambert/{paper.tex,references.bib,VERIFICATION.md,LEDGER.md}`)
- **Worktree:** `C:\Users\chaos\.t3\worktrees\MathematicsResearch\research-phase-20-gener-b08235755636abff`
- **Audit Mode:** Read-only cross-provider verification (Gemini 4 auditing Claude Opus 5.5)
- **Date:** 28 November 2026
- **Verdict:** **ACCEPT WITH MINOR POLISH**

> **Cross-model review is not independent human peer review.** This report records an automated cross-provider audit of structural, formal-citation, scope, and mathematical-fidelity properties; no independent human specialist has reviewed the manuscript.

---

## 1. Archived Release Integrity — PASS

Checked via `git status --short` and `git diff --name-status HEAD -- papers/ docs/registry/papers.toml`:

- `papers/manifest.toml` — **unmodified**
- `papers/SHA256SUMS` — **unmodified**
- `papers/alphaxiv-records.toml` — **unmodified**
- `docs/registry/papers.toml` — **unmodified**
- Archived release directories (`papers/01..10`, `papers/07-synthetic-expansions/`) — **all unmodified**
- The only tracked file under `papers/` with working-tree edits is `papers/13-reciprocals-and-kernel-tower/paper.tex` (an unreleased candidate draft, not an archived release). `papers/14-dense-digit-mass-lambert/` is untracked and contains no `paper.pdf`, `metadata.toml`, or `submission/` directory.

---

## 2. LaTeX Structural Integrity — PASS

An independent Python structural parser verified `papers/14-dense-digit-mass-lambert/paper.tex` and `references.bib` (stripping LaTeX comments and handling escaped delimiters):

| Check | Result |
| --- | --- |
| Balanced braces (`paper.tex`) | **PASS** (final depth `0`, min depth `0`) |
| Balanced braces (`references.bib`) | **PASS** (final depth `0`, min depth `0`) |
| Balanced `\begin`/`\end` environments | **PASS** (`114` pairs, `0` unclosed, `0` nesting errors) |
| Balanced display math `\[`/`\]` & no `$$` | **PASS** (`29`/`29`, `0` nesting errors, `0` `$$`) |
| Balanced inline `$` across body paragraphs | **PASS** (`136` paragraphs, `0` odd-dollar paragraphs) |
| Duplicate `\label` keys | **PASS** (`68` labels, `0` duplicates) |
| Undefined `\ref`/`\cref`/`\Cref`/`\eqref` targets | **PASS** (`125` calls, `154` targets, `0` undefined) |
| Bibliography entries & `\cite` resolution | **PASS** (`15` bib entries, `0` duplicates; `20` `\cite` calls / `21` keys, `0` undefined, `0` uncited) |

---

## 3. Lean Declaration Accuracy, Scope Discipline, and Mathematical Fidelity — PASS (1 minor polish item)

### 3.1 Lean Declaration & Commit-Hash Audit
- **Working-tree citations (`\leanW`):** All `75` `\leanW{name}{line}` citations in `paper.tex` (`38` distinct declarations) resolve to the exact theorem declaration on the exact line of working-tree `NormalityChecker/DigitMassTransfer.lean` (`0` mismatches).
- **Private declarations cited in `VERIFICATION.md`:** All `4` (`ebTail_bounds` L1951, `digitSum_two_le_log` L1935, `erdosBorwein_count_le` L2028, `popcount_word_identity` L2237) resolve to the exact lines.
- **Module hygiene:** `NormalityChecker/DigitMassTransfer.lean` exports `62` theorems and contains `0` `sorry`, `admit`, or `axiom` tokens outside comments.
- **Pinned citations (`\leanT`, `\leanU`):** All `7` commit-pinned citations (`Phase22Cores.erdosBorweinPlusCoeff_eq` at `8ca43095887858bf9697b6a8332c6a6dd0b0cda3` L1052; `Basic.shift` L15, `Basic.frequency` L18, `BinaryDiscrepancy.radixDiscrepancy` L11, `BinaryDiscrepancy.discrepancy_lt_one_iff_transitions` L229, `HigherOrderTower.OrderNormal` L69, `SimpleNormalityKernel.wordFreq` L73 at `cb395159c6e343c60c1413719cdfc8429e15af2c`) resolve accurately via `git show`.
- **Zero fake commit hashes:** Only the two genuine commit objects above appear across `paper.tex`, `VERIFICATION.md`, and `LEDGER.md` (both verified via `git cat-file -t` -> `commit`). Working-tree `NormalityChecker/DigitMassTransfer.lean` is explicitly marked uncommitted and pending commit pinning before release; no commit hash is attributed to it anywhere.

### 3.2 Scope Discipline
- Evidence labels are strictly separated across `paper.tex`, `VERIFICATION.md`, and `LEDGER.md`:
  - **Kernel-verified** is restricted to Theorem A and Lemmas 2.2, 2.4, Theorem 4.1 (plus the explicitly delineated sub-parts of Lemmas 2.1, 2.3, Theorems 2.5, 2.6, Proposition 2.10, Lemma 3.1, Corollary 3.3, Proposition 3.4).
  - Lemma 2.3 explicitly separates the kernel-verified recursion `signedWeight` from the paper-proved / finitely-checked identification with $\wpm$.
  - Theorem 6.1 (Theorem D(i)) is accurately labeled **Lean-supported paper proof**.
  - External inputs (`SengeStraus73`, `Stewart80`, `Tenenbaum`, `Reitwiesner1960`, `Wirsing1967`, `Topacogullari17`, `Maxfield53`) and conditional status (Proposition 7.4 / Theorem E(iii)) are explicitly labeled.
  - Finite measurements (Table 6 and the base-10 $E(100)$ prefix) are explicitly quarantined as non-evidence.
  - Benchmark roster `BC-01`…`BC-50` (including `BC-37`–`BC-39`) is explicitly left unchanged.
- *Informational note (not an error):* In `DigitMassTransfer.lean`, the type signature of `erdosBorwein_two_pow_lowerDiscrepancy_pos` (L2194) is `∃ δ > 0, ∀ᶠ N in atTop, δ ≤ radixDiscrepancy 2 (...) N`, with `1/120` supplied inside the proof (L2197) and directly obtainable from `erdosBorwein_two_pow_radixDiscrepancy_eventually_ge` (L2161) at `ε = 1/120`. The claim in Theorem A(iv) and Theorem 4.1 is therefore mathematically sound and kernel-backed, though `1/120` is explicit in L2161/L2197 rather than in L2194's type signature.

### 3.3 Mathematical Fidelity to Accepted Track A and Track E §3
- **Track A (`notes/phase24/dense-digit-mass-and-lambert.md`):** All constants, inequalities, tables, and proofs match faithfully:
  - $\Ctrue \in [1.339103, 1.339116]$, $C \in [1.4035953, 1.4035958] < 29/20$, $H \in [1.903838, 1.903848]$;
  - Table 1 ($E(2^k)$, $k \in \{3,4,5,6,8,10,16,64\}$), Table 2 ($\tau_b$ families, $b=3..10$), Table 3 ($E_+(2^k)$, $k \in \{4,5,6,8,16\}$), cubic-character bounds ($M_\chi = 7, 9, 13$), $E_{\mathrm{odd}}$, $E^*$, and the $E(4)$/$E^*(4)$ carry-density thresholds.
- **Track E §3 (`notes/phase24/classical-constants-and-joint-numerators.md`):**
  - Independent CRT enclosure $\Ctrue \in [1.337765, 1.346123]$ and $D^- \ge 0.05129$ (Remark 4.3).
  - Four-state transducer (Table 4) with stationary law $(\frac{1}{6}, \frac{1}{3}, \frac{1}{3}, \frac{1}{6})$, $A_L = \frac{1}{3} - \frac{7 - (-1/2)^{L-1}}{18L}$, $A_{16} = \frac{324039}{1048576}$, two separate floor inequalities (Theorem 6.8) and counterexample to the mixed inequality (Remark 6.9).
  - Unconditional nonnormality of $E_+(2^k)$ for $k \ge 3$ (including $E_+(8)$) with $D^-(E_+(2^k); 2) \ge 2.34 \times 10^{-7}$ (Theorem D(iii), Theorem 6.10).
  - Simple nonnormality of $E_+(8)$ explicitly marked **Open** (Theorem D(iii), Remark 6.11, Table 5, Question 8.2).
  - $E(2)$, $E(4)$, $E_+(2)$, and $E_+(4)$ explicitly marked **Open** (Abstract, Theorem E(iv), Table 5, Questions 8.1–8.2).
- **Minor Polish Item 1 (`paper.tex` L606, Remark 6.11):** The text reads `The prefix measurement $f_1\approx0.334$ for $E_+(8)$ in \Cref{tab:measure} is a finite measurement only.` However, Table 6 (`\Cref{tab:measure}`, L712, from Track A §11 at $N = 2^{17}$) reports $f_1 = 0.33718$ for $E_+(8)$ (the value `0.3342` comes from Track E §3.4 at $M = 6000$). Update `0.334` to `0.337` to match Table 6.

---

## 4. Hygiene & Disclaimers — PASS (1 minor polish item)

- **`pdflatex`/`bibtex` pending notice:** Explicitly stated in `paper.tex` (L755), `VERIFICATION.md` (L7, L116, L119), and `LEDGER.md` (L78).
- **Verbatim disclaimer `"Cross-model review is not independent human peer review."`:**
  - `paper.tex` L755: **PASS** (present verbatim).
  - `VERIFICATION.md` L5: **PASS** (present verbatim).
  - **Minor Polish Item 2 (`LEDGER.md` L3):** Currently reads `**Cross-model review is not independent human peer review**, and no human specialist has read the proofs.` (uses a comma rather than a period, so the exact sentence with trailing period is not matched verbatim). Change to `**Cross-model review is not independent human peer review.** No human specialist has read the proofs.`

---

## Verdict

**ACCEPT WITH MINOR POLISH**

Candidate Paper XIV is structurally sound, preserves all archived release files untouched, cites every working-tree and pinned Lean 4 declaration accurately with zero fake commit hashes and disciplined evidence-label separation, and faithfully reflects accepted Track A and Track E §3 results (including the open status of $E(2)$, $E(4)$, $E_+(2)$, $E_+(4)$, and simple nonnormality of $E_+(8)$). Two tiny polish fixes are recommended before release compilation:
1. `papers/14-dense-digit-mass-lambert/paper.tex` L606: align `0.334` to `0.337` so it matches Table 6 (`0.33718` at $N = 2^{17}$).
2. `papers/14-dense-digit-mass-lambert/LEDGER.md` L3: end the bolded disclaimer sentence with a period so `"Cross-model review is not independent human peer review."` appears verbatim across all three files.

**Cross-model review is not independent human peer review.**
