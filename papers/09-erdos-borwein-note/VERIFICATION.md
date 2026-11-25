# Verification map: Finite-statistic thresholds and statistical obstructions for the binary digits of the Erdős–Borwein constant (research note, v1.0)

Lean commit: `e4809cf561573aef588e6ffc491a35cdb79fd9ec` (research-checkpoint-18). Line numbers below were checked with `git show e4809cf:<file>`; the declaration lines are the `theorem` lines.

Base for pinned links: `https://github.com/eldernos/MathematicsResearch/blob/e4809cf561573aef588e6ffc491a35cdb79fd9ec/`

Lean declarations used:

- [`carry_knapsack_le`](https://github.com/eldernos/MathematicsResearch/blob/e4809cf561573aef588e6ffc491a35cdb79fd9ec/NormalityChecker/Phase17DiscrepancyBounds.lean#L375): for `D r c : ℕ`, `lam ≥ 0`: `1[2^(D-1) ≤ (r+c) % 2^D] ≤ 1[2^(D-1) ≤ r] + lam*c + 1[r < 2^(D-1)] * max 0 (1 - lam*(2^(D-1) - r))` (reals).
- [`parity_bonferroni_dual_le`](https://github.com/eldernos/MathematicsResearch/blob/e4809cf561573aef588e6ffc491a35cdb79fd9ec/NormalityChecker/Phase17DiscrepancyBounds.lean#L432): for `m n : ℕ`, `∑_{k<2m+2} (-2)^k * C(n,k) ≤ (-1)^n` in `ℤ`.
- [`source_phase`](https://github.com/eldernos/MathematicsResearch/blob/e4809cf561573aef588e6ffc491a35cdb79fd9ec/NormalityChecker/ErdosBorweinArrivals.lean#L16), [`arrival_sum`](https://github.com/eldernos/MathematicsResearch/blob/e4809cf561573aef588e6ffc491a35cdb79fd9ec/NormalityChecker/ErdosBorweinArrivals.lean#L41), [`one_bit_carry`](https://github.com/eldernos/MathematicsResearch/blob/e4809cf561573aef588e6ffc491a35cdb79fd9ec/NormalityChecker/ErdosBorweinArrivals.lean#L86) (finite reindexing and phase identities; used only as supporting facts, see Lemma 2.1 and Proposition 3.1).

Build record: `notes/phase18/verification.md` (axiom audit accepts only `propext`, `Classical.choice`, `Quot.sound`; independent kernel replay of all 248 module files). A full `lake build` was **not** run for this note.

## Theorem verification map

Numbers are those of the compiled `paper.pdf`. Evidence labels follow `papers/WAVE2-CONTRACT.md`. Theorems that are implications whose hypothesis is a statement about the actual constant (Theorems 5.1, 7.5, 8.2) carry the label of their proof; the label **Conditional** is used where the conclusion needs a hypothesis that nobody has proved (Corollary 5.3).

| # | Statement (short) | Evidence label | Lean declarations | External inputs | Reproduction |
| --- | --- | --- | --- | --- | --- |
| Lemma 2.1 | Digit identity: `2^n E = integer + Σ_d C(n+d) 2^{-d}`; digit n+1 is the top bit of `(R_D + ⌊Y_D⌋) mod 2^D` | Paper proof | none (the exponential analogue and the reindexing are `source_phase`, `arrival_sum`) | none | elementary; exact digits and column counts are exercised by `scripts/erdos_borwein_arrivals.py`, `scripts/phase16_erdos_borwein.py` (self-checks) |
| Prop. 2.2 | `p_* = 1/2 − (1/2) e^{-2} E(−1)^{c_1}` | Paper proof | none | none | consistent with `scripts/phase17_erdos_borwein_bias.py` §D and `crosscheck.py` §3 |
| Prop. 3.1 | One-source mean of `U` (via Möbius convolution supported on squarefull integers) and tail mean `E_I Y_D = μ + o(1)` | Paper proof | none (`arrival_sum` is the finite reindexing step) | none (elementary; counting squarefull integers) | `crosscheck.py` §1 recomputes μ; finite check of the mean mark total: `scripts/phase16_erdos_borwein.py` (mean C ≈ 2.0755 at s = 23) |
| Lemma 4.1 | Depth truncation: `P(R_D = r) ≤ p_0^D`; first digit ≠ top bit of `R_D` with prob ≤ `2μ p_0^D` | Paper proof | none | none | elementary |
| Thm 4.2 | `μ ∈ [2.0762592, 2.0763285]`, `E(−1)^{c_1} ∈ [0.111481733, 0.111502881]`, `p_* ∈ [0.492450290, 0.492460864]` | Finite certificate | none | none | `python -B scripts/phase17_erdos_borwein_bias.py` (§A, §D; ≈ 20 s; all assertions pass). Independent float cross-check: `python -B papers/09-erdos-borwein-note/crosscheck.py` (§1–§3: μ = 2.07632, E(−1)^{c_1} = 0.111493, p_* = 0.492456, inside the enclosures) |
| Thm 5.1 | If `limsup E_I Ψ_16(R_16) < 0.4962723` then `limsup f_I < 1/2`; `E_{Q_16} Ψ_16 ≤ 0.4960081` | Lean-supported paper proof. Lean steps: `carry_knapsack_le` (the pointwise dual inequality with λ = 1/557). Paper steps: Lemma 2.1, Prop. 3.1(c), averaging. Finite-certificate step: `E_{Q_16}Ψ_16 ≤ 0.4960081` and `μ ≤ 2.0763285` (Thm 4.2) | [`carry_knapsack_le`](https://github.com/eldernos/MathematicsResearch/blob/e4809cf561573aef588e6ffc491a35cdb79fd9ec/NormalityChecker/Phase17DiscrepancyBounds.lean#L375) | none | `scripts/phase17_erdos_borwein_bias.py` §C prints "D=16 LP dual certificate: lambda = 1/557, value <= 0.49973577" and "E_Q16[Psi_16] <= 0.49600807"; `crosscheck.py` §2 gives 0.4960055 (float, truncated, as expected slightly below the certified upper bound) |
| Cor. 5.2 | Simple normality ⇒ `liminf d_TV(L(R_16), Q_16) ≥ 2.6×10^{-4}` | Lean-supported paper proof (same steps as Thm 5.1 plus prefix subtraction) | `carry_knapsack_le` | none | as Thm 5.1 |
| Cor. 5.3 | If `L(R_16) → Q_16` along a sequence of windows then `limsup f_I < 1/2` | Conditional (hypothesis: convergence in law of `R_16` to `Q_16` along a sequence of dyadic windows; unproved) | `carry_knapsack_le` | none | as Thm 5.1 |
| Thm 5.4 | Class `𝓘_D` (first D columns iid copies of J; later columns mean ≤ μ): `f^sup_D ≥ 0.502823` for all `D ≤ 15`, `f^sup_16 ≤ 0.499736`; table for D = 4…23 | Finite certificate | none (the upper bound uses the same dual inequality, `carry_knapsack_le`, for general D) | none | `scripts/phase17_erdos_borwein_bias.py` §C (output table "D= 4 … D=23", "RESULT C") |
| Thm 6.1 | Product perturbations `1 + ε ∏ g_i(C_i)` for K = 2,…,5 preserve all (K−1)-column laws and give `f(1) = 1/2` and `f(1) > 1/2` | Finite certificate (positivity and exact preservation are one-line paper arguments in the proof; the shifts `s_K` are certified numerically) | none | none | `scripts/phase17_erdos_borwein_bias.py` §E (sets S_i listed in the script; "RESULT E") |
| Thm 7.1 | Parity Bonferroni: for odd r and Poisson factorial moments up to r, `E(−1)^N ≥ e_r = Σ_{k≤r}(−2)^k/k!`, attained by an explicit law on `{0..r}`; `e_r > 0` iff `r ≥ 5` | Lean-supported paper proof. Lean step: `parity_bonferroni_dual_le` (pointwise `q_r(n) ≤ (−1)^n`). Paper steps: `E q_r(N) = e_r` and the primal law `w_n = (1/n!) Σ_{j≤r−n} (−1)^j/j!` | [`parity_bonferroni_dual_le`](https://github.com/eldernos/MathematicsResearch/blob/e4809cf561573aef588e6ffc491a35cdb79fd9ec/NormalityChecker/Phase17DiscrepancyBounds.lean#L432) | none | exact fractions: `scripts/phase17_erdos_borwein_bias.py` §F; `crosscheck.py` §4 (primal laws, e_r for r = 1,…,11, dual inequality on n < 300) |
| Thm 7.4 | (a) every `r ≤ 4`, every D: class `𝓘_{D,r}` has a law with `f(1) = 1/2` (exact rational laws ρ_3, ρ_4); (b) `D = 16`: `r ≤ 8` fails (f ≥ 0.5000126); (c) `D = 17`: `r ≤ 6` fails | Finite certificate | none | none | `scripts/phase17_erdos_borwein_bias.py` §F ("RESULT F1"); `crosscheck.py` §4 rechecks ρ_3, ρ_4, L^{(12)} and their parities in exact arithmetic. Parts (b), (c) rely on the script's certified knapsack with modified column-1 parity; not independently recomputed |
| Thm 7.5 | If Poisson factorial moments up to order 92 of the 16-column marked counts converge along a sequence of windows, then `limsup f_I ≤ 0.499856`; hence `9 ≤ r_min(16) ≤ 92` | Lean-supported paper proof. Lean step: `carry_knapsack_le` (the dual for the carry). Paper steps: Jordan-inversion truncation, Vandermonde collapse, pointwise `Φ ≥ Ψ_16`. Finite-certificate step: excess `≤ 1.197×10^{-4}` (exact fractions for `K ≤ 360`, `4^K` tail bound beyond) | `carry_knapsack_le` | none | `scripts/phase17_erdos_borwein_bias.py` §F ("RESULT F2"); `crosscheck.py` §4 floats the excess at 1.19675×10^{-4} for K ≤ 360 |
| Prop. 8.1 | `φ(m) = exp κ(m)`, `φ(2m) = φ(m)`, `A_I(2m) = A_I(m) + O(m/N)` | Paper proof | none | none | consistent with the printed `phi(m)` table in `scripts/phase17_erdos_borwein_bias.py` §G (`phi(2m) = phi(m)`) |
| Thm 8.2 | `E_{Q_∞} S^+_{116} ≤ 0.4999592` (so 58 odd harmonics suffice if `A_I(m) → φ(m)`) | Finite certificate (floating point with explicit radii, see note below) | none | Selberg–Vaaler majorant inequality `S^+_N ≥ 1_{[1/2,1)}` quoted from J. D. Vaaler, *Some extremal functions in Fourier analysis*, Bull. AMS 12 (1985), 183–216 (theorem number and page **not verified**: full text unavailable to us) | `scripts/phase17_erdos_borwein_bias.py` §G ("RESULT G1"); `crosscheck.py` §5 checks the majorant property on a 2^18 grid (not a proof) |
| Thm 8.3 | Probability measure ρ with `ρ̂(m) = φ(m)` (|m| ≤ 110) and `ρ([1/2,1]) ≥ 0.500192`; no trigonometric majorant of degree ≤ 110 certifies | Finite certificate (floating point with explicit radii) | none | none | `scripts/phase17_erdos_borwein_bias.py` §G ("RESULT G2"; 221 embedded atoms) |
| Prop. 10.1 | Agreement of exact digits with Crandall's abstract and Table 1 (bits at 10^10, 10^20); internal consistency of the §6 tables; prefix frequencies 0.500678, 0.495743, 0.494216 | Finite certificate | none | Crandall, INTEGERS 12 (2012) #A23, abstract, Table 1 (p. 7) and §6 (pp. 7–9), read from the journal PDF | `scripts/phase17_erdos_borwein_bias.py` §H; `scripts/phase16_erdos_borwein.py --smin 20 --smax 23` (prefix 2^22, 2^24) |

**Note on floating-point certificates (Thm 8.2, 8.3).** Section G of the Phase 17 script evaluates `φ(m)` in IEEE doubles with a hand-derived radius (series truncation at 64 columns, missing mark mass, uncertainty of μ, and absolute margins of 1e-10…1e-12 for rounding) plus a 1e-9 safety margin. This is not interval arithmetic. The margins are 4.1×10^{-5} (degree 116) and a quadrature-weight lower bound of 3.2×10^{-3}. We call it a finite certificate, but it is weaker than the exact-integer certificates of Theorems 4.2, 5.1, 5.4, 6.1, 7.4 and 7.5. An interval-arithmetic recomputation is an open task.

## What is completely kernel-verified

Nothing in this note is completely kernel-verified. Lean verifies the two pointwise inequalities `carry_knapsack_le` and `parity_bonferroni_dual_le` and the finite identities `source_phase`, `arrival_sum`, `one_bit_carry`. Every probabilistic step, the tail mean, all dynamic-programming and linear-programming certificates, and the Fourier computations are written proofs or computations.

## External analytic dependencies

- Selberg–Vaaler majorant inequality (Thm 8.2): J. D. Vaaler, Bull. Amer. Math. Soc. 12 (1985), 183–216. Statement and theorem number not verified by us; sanity-checked numerically on a grid in `crosscheck.py`.
- Crandall's published counts and Table 1 (Prop. 10.1): used as data, read from the journal PDF.
- No deep analytic theorem is used for Theorems 5.1, 5.4, 6.1, 7.1, 7.4, 7.5. The tail mean (Prop. 3.1) uses only elementary counting of squarefull integers.
- Not dependencies: Tao–Teräväinen (2025) and the other correlation results cited in Section 9 are described, not used.

Human specialist review is outstanding. Cross-model review (by models from other providers) is not independent human peer review.

## Reproduce

From the repository root (all commands use the Python standard library except `crosscheck.py`, which needs `numpy`):

```sh
python -B scripts/phase17_erdos_borwein_bias.py          # ~20 s; §A–§H; ends with "all assertions passed"
python -B scripts/erdos_borwein_poisson.py               # earlier 32-column enclosure [492230, 492685] millionths
python -B scripts/erdos_borwein_arrivals.py              # exact counts on [2^18, 2^19): 67135 63695 63696 67618
python -B scripts/phase16_erdos_borwein.py --smin 20 --smax 23   # shell frequencies and prefix 2^24 (~40 s)
python -B papers/09-erdos-borwein-note/crosscheck.py     # independent cross-check (~10 s), ends with "all cross-checks passed"
wsl -d Ubuntu -- bash papers/wsl-build.sh 09-erdos-borwein-note   # build paper.pdf
```

These runs were performed for this note in the worktree at the research-checkpoint-18 baseline (exit code 0 for each). Lean was not rebuilt. To inspect a declaration statement: `git show e4809cf:NormalityChecker/Phase17DiscrepancyBounds.lean | sed -n 375,400p`.
