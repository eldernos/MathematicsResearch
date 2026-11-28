# Phase 26 Track G: External Dirichlet GRH Verification, Lambert Window Extensions (`GF-48` Continuation), and Primary-Source Provenance Audit

Phase 26, Track G (Parts G1, G2, and G3), branched on `research/phase-26-arithmetic-amplification`. Companion exact verification script: [`scripts/phase26_grh_windows.py`](../../scripts/phase26_grh_windows.py) (standard library only; `18,955` pure `int`/`Fraction` exact certificates, `127` bookkeeping/format consistency checks, and `19` isolated `[finite]` illustrations; exit code `0`). Primary repository sources built upon: [`notes/phase25/grh-lambert-windows.md`](../phase25/grh-lambert-windows.md) (`GF-48`), [`papers/06-multiplicative-lambert/paper.tex`](../../papers/06-multiplicative-lambert/paper.tex) (*Paper VI*, `CC-48`), [`notes/phase20/coefficient-transfer.md`](../phase20/coefficient-transfer.md) and [`notes/phase20/lambert-leading-constant.md`](../phase20/lambert-leading-constant.md) (`GF-05`), [`notes/phase21/radix-lambert.md`](../phase21/radix-lambert.md) (`GF-12`), [`notes/phase22/radix-thresholds-and-class-groups.md`](../phase22/radix-thresholds-and-class-groups.md) (`GF-21`), [`notes/phase22/odd-characters-and-kernel-quotient.md`](../phase22/odd-characters-and-kernel-quotient.md) (`GF-22`), [`notes/phase25/historical-provenance-lambert.md`](../phase25/historical-provenance-lambert.md) (Track H2), [`notes/phase25/external-dialogue-summary.md`](../phase25/external-dialogue-summary.md) (Track H3), and [`docs/research-objectives.md`](../../docs/research-objectives.md).

> **Evidence and review policy.** All evidence labels strictly follow [`docs/research-objectives.md`](../../docs/research-objectives.md) (`Kernel-verified`, `Lean-supported paper proof`, `Paper proof`, `Finite certificate`, `Conditional`, `External input`, `Open`). **Unconditional** theorems and **Dirichlet-GRH-dependent** theorems are strictly separated throughout. Although an external Lean 4 proof of RH and Dirichlet GRH (`lsernau/grh-lean`, commit `72fead102f663d5c7a407964a13dc0cf9d977207`, following Alpöge's 20 November 2026 release) has passed six independent formal kernels, no human mathematician has read it through and it is neither peer-reviewed nor formalized inside this repository (§1.5–§1.6). Consequently, **zero** Dirichlet-GRH deductions here are `Kernel-verified` in this repository, **zero** of the 50 classical benchmark statuses `BC-01`…`BC-50` change, finite digit statistics are never asymptotic evidence, and **cross-model review is not independent human peer review**. No external contact or endorsement has occurred.

---

## Summary of Results

| # | Track | Result | Evidence Label |
| --- | --- | --- | --- |
| **G1** | §1 | **Primary-source verification of external RH / Dirichlet GRH Lean proofs** (`alpo.ge/remark.pdf`, `lsernau/grh-lean@72fead10`, MIT/Waterloo/Lean FRO logs): exact verbatim Lean signatures, Lean `v4.35.0` / Mathlib `56a00585`, 3 standard axioms only, 6-kernel acceptance, exact Dirichlet-only scope (excludes ERH/Hecke/automorphic $L$-functions), documented caveats, and formal evidence-classification policy for `GF-48` and Phase 26 | Primary-source audit (`[R]`) + accounting consistency checks (`C1`) |
| **G2.1A** | §2–3.1 | **Paper VI at $H = \sqrt{N}(\log N)^C$ under GRH($q_0$):** replacing Brun–Titchmarsh in Paper VI's far tail (I3) by elementary Lemma E.2 breaks the $a > 1/2$ far-tail wall (`Remark B.1`), giving $R$-isolated planting and window disjunctivity on $[N, N + \lceil\sqrt{N}(\log N)^C\rceil)$ for **every fixed $C > 2$** with $\#_w(N, H) \gg_{w, C} H(\log\log N)^\delta/\log N$ and $1 - D_{N,H}(L) \gg_C (\log\log N)^{1+\delta}/\log N$ (and $H \ge K\sqrt{N}(\log N)^2$ at $C = 2$ with $m = 1$) | Conditional / External-GRH (`GRH(q_0)`) |
| **G2.1B** | §2–3.1 | **Method barrier at $H = \sqrt{N}(\log N)^C$ and $t = 2$ CRT threshold for `GF-22` under Dirichlet GRH:** NO fixed power $C > 0$ works for `GF-22`'s CRT construction (since $\varphi(q') \gg (\log N)^C$); the **threshold of the $t = 2$ CRT method** is $H \ge \sqrt{N}\exp(C_0 \log\log N \cdot \log\log\log N)$ for every $C_0 > d/\log b$ (halved from $2d/\log b$ via Theorem G2.4A; further lowerable to $\alpha_*(\chi)d/\log b$ via $t = t_*$ moment optimization), beating every $N^{1/2+\varepsilon}$ | Paper proof (method barrier); Conditional / External-GRH (positive range) |
| **G2.2A** | §2–3.2 | **Unconditional almost-all-window word counts and $R$-isolated planting below $1/2$ for Paper VI:** averaging bad planted pairs $(m, p)$ globally and using the primary-verified log-free character zero-density bound of Thorner–Zaman (2024, Thm. 2.1, combining Huxley 1975 + Jutila 1977, Thm. 1) + uniform Vinogradov–Korobov zero-free region gives **unconditionally** for every fixed **$1/6 < a \le 1$** and almost all $N \in [X, 2X]$: $R$-isolated planting, full two-sided word counts $\#_w(N, H) \asymp H/(\log X)^\kappa$, and window discrepancy gap $1 - D_{N,H}(L) \asymp (\log\log X)/(\log X)^\kappa$ (repositioned as a word-count / planting theorem distinct from Hooley / MR II support asymptotics; `a > 1/7` — and `2/15` in $T$-aspect — with Chen–Gupta–Li `2507.08296v2` `[R]` + Jutila 1977 $\sigma$-split) | Lean-supported paper proof (unconditional; published inputs) |
| **G2.2A′** | §2–3.2 | **GRH($q_0$) almost-all-window word counts and $R$-isolated planting for Paper VI down to $\theta > 0$ and $(\log X)^{2+\varepsilon}$:** Selberg's (1943) mean-square method in progressions gives $R$-isolated planting, full-order word counts, and window discrepancy gap for almost all $N \in [X, 2X]$ at **$H = X^\theta$ for every fixed $\theta > 0$**, and almost-all window disjunctivity ($\#_w(N, H) \gg_w H/\log X$) for every $H/(\log X)^2 \to \infty$ (in particular $H = (\log X)^{2+\varepsilon}$) | Conditional / External-GRH (`GRH(q_0)`) |
| **G2.2C** | §2–3.2 | **Unconditional `GF-22` on EVERY window $N^a \le H \le N$ for $7/12 < a \le 1$:** applying short-interval PNT machinery in progressions (Thorner–Zaman 2024 Thm. 2.1 / Huxley 1975 + Jutila 1977 Thm. 1 log-free zero density near $\sigma = 1$, two-family Landau–Page avoidance for $|t| \le 10$, and uniform Vinogradov–Korobov zero-free region — classical Montgomery 1971/1994, explicit via Khale 2024 Thm. 1.1) to our CRT moduli $q' = q Q_\nu = N^{o(1)}$ upgrades Phase 25 Proposition D.2 from $N\exp(-c_3\sqrt{\log N})$ to **every fixed $a > 7/12$** unconditionally (resolving Phase 25 Open Question 6 with margin; $a > 4/7$ — and $17/30$ in $T$-aspect — via `2507.08296v2` `[R]` + Jutila 1977 $\sigma$-split) | Paper proof (unconditional; published inputs) |
| **G2.2D** | §2–3.2 | **Unconditional almost-all windows for `GF-22` below $1/2$ ($1/6 < a \le 1$):** averaging the tail sum globally over $N \in [X, 2X]$ eliminates Lemma E.2's $\sqrt{N}$ wall; combined with Thorner–Zaman (2024, Thm. 2.1) / Huxley 1975 + Jutila 1977 (Thm. 1) + Landau–Page + Vinogradov–Korobov mean-square bounds, `GF-22` holds for almost all $N \in [X, 2X]$ at every fixed **$1/6 < a \le 1$** ($a > 1/7$ — and $2/15$ in $T$-aspect — via `2507.08296v2` `[R]` + Jutila 1977 $\sigma$-split) | Paper proof (unconditional; published inputs) |
| **G2.2B** | §2–3.2 | **Dirichlet-GRH almost-all windows for `GF-22` down to sub-polynomial $X^{o(1)}$:** Selberg's mean-square variance in progressions (explicit $\varphi(q')^2$ law) + averaged tail yields `GF-22` for almost all $N \in [X, 2X]$ whenever $H \ge \exp(C_1 \log\log X \cdot \log\log\log X)$ with $C_1 > 2d/\log b$ (in particular every $H = X^\theta$, $\theta > 0$) | Conditional / External-GRH (Dirichlet GRH) |
| **G2.3** | §2–3.3 | **Exact leading window discrepancy constants matching `GF-12`:** localizing the sub-threshold width law (with a new multiplicative Shiu bound on $2^{v_q(c(n))}$) gives the **unconditional self-normalized exact law** $1 - D_{N,H}(L_c(b); b) = (1 + \omega_b + o(1))(\kappa/\log b)(S(N,H)/H)\log\log N$ for all $b = 2^k$ and all sub-threshold $b \ne 2^k$ ($\delta \le \delta^*_b$) whenever $S(N,H) \gg_a H/(\log N)^\kappa$; matches `GF-12`'s explicit constant $C_f$ **unconditionally on all windows** $N\exp(-c_1\sqrt{\log N}) \le H \le N$, **unconditionally on almost all windows** at every fixed $a > 0$ via Matomäki–Radziwiłł II (`arXiv:2007.04290` preprint `[R]`; and Hooley 1994 gives the order of magnitude for $\chi_{-4}$), and **under GRH($q_0$)** on **all windows** $\sqrt{N}\exp(C_2 \log N / \log\log N) \le H \le N$ (all $a > 1/2$, contour at $\sigma_1 = \frac{1}{2} + c/\log\log N$) | Lean-supported paper proof (unconditional ranges); Preprint-input paper proof (almost-all $a > 0$ explicit constant via MR II); Conditional / External-GRH ($a > 1/2$ all-window explicit constant) |
| **G2.4A** | §2–3.4 | **Universal second-moment Shiu reduction for `GF-22` / cubic $L_\pm(b)$:** for **every** nonprincipal $\chi \bmod q$ of order $h \ge 2$ and every nonzero additive $\Phi : \mathbb{Z}[\zeta_h] \to \mathbb{Z}$, Galois trace duality $|\Phi(c_\chi(n))|^2 \le K_\Phi \sum_{\sigma \in \operatorname{Gal}(\mathbb{Q}(\zeta_h)/\mathbb{Q})} |c_{\chi^\sigma}(n)|^2$ + universal identity $\kappa_2(\chi^\sigma) = 2$ + Shiu on each $|c_{\chi^\sigma}|^2$ + Chebyshev cuts $L$ **in half** (from $2\log_b\log N$ to $\log_b\log N$), reducing the $t = 2$ CRT exponent from $2d/\log b$ to **$d/\log b$** ($6/\log 2 \to 3/\log 2$ for $L_\pm(2)$); strict log-convexity proves $t = 2$ is the unique asymptotic global minimizer, and an exact Fourier series proves $\alpha_*(\chi) < 1$ strictly for every $h \ge 2$ | Paper proof (unconditional; Shiu input) + Exact certificate (`C6`, incl. $h = 5$ Galois test) |
| **G2.4B** | §2–3.4 | **Single-class CRT & arbitrary-union zero-block covering barriers for odd-order characters:** because $P(2) \in [0.452238, 0.452338] < 1/2$ (and $P_{\mathcal{P}'}(2) \in [0.422597, 0.422697]$ for cubic mod 7), for all $L \ge L_0(\chi)$: **(1)** every single CRT zero-block system (even with optimal prime reuse) satisfies $\log Q \ge d_{\min}(1 - P_{\mathcal{P}'}(2) - o(1))L\log L$, and **(2)** a union bound over **all** zero blocks $\mathcal{Z}_\chi(L) = \{n : c_\chi(n+1) = \dots = c_\chi(n+L) = 0\}$ yields upper natural density (and window density on $H \ge N^a$, $a > 1/2$, or almost all windows) $\le \exp(-\frac{1 - P_{\mathcal{P}'}(2) - o(1)}{2} L\log L)$, blocking $H/(\log N)^C$ and $cH$ for **any** method detecting zero blocks of length $L \ge c\log_b\log N$ (single CRT class, arbitrary union of CRT classes, or squarefull/Selberg sieve) | Paper proof + Exact certificate (`C6`) |
| **G2.5** | §2–3.5 | **Audit of unconditional short-interval prime inputs in APs:** confirms Baker–Harman–Pintz `0.525` (2001) and Guth–Maynard `17/30` (`arXiv:2405.20552v2` `[R]`) are proved for $q_0 = 1$ only; Kumchev `0.53` (2002) remains the sharpest published lower bound for $(\mathrm{P}_\nu)$ in APs ($q_0 \ge 3$), PPS `7/12` (1985) and Thorner–Zaman `7/12` (2024, *Math. Z.* **306** `[R]`, via Huxley 1975 + Jutila 1977 `[R]`) supply two-sided asymptotics, and Chen–Gupta–Li `arXiv:2507.08296v2` (`[R]`, unrefereed preprint) gives $A = 7/3$ uniformly ($4/7$ all / $1/7$ almost all) and $T$-exponent $30/13$ for $q = U^{o(1)}$ ($17/30$ / $2/15$) when paired with Jutila (1977) on $[\frac{4}{5}, 1]$ | Literature audit (`[R]`/`[A]`/`[S]`) |
| **G3** | §4 | **Six-topic external literature & provenance audit** (mesoscopic shifted-divisor LLTs incl. Hooley 1971–1994 & Matomäki–Radziwiłł II `2007.04290` `[R]`; short-interval primes in APs incl. Jutila 1977 & Thorner–Zaman 2024; generalized Lambert classifications incl. Mira Cult & Captain Sude; constructive badly approximable normal numbers; Toeplitz determinants & OPUC orbit measures; Padé/Hankel methods for $\ln 2$) | Literature & provenance audit |

---

## 0. Definitions and Notation

Logarithms $\log$ are natural unless a base $b$ is written ($\log_b x = \log x / \log b$), and $LL := \log\log N$, $\ell_N := \log_b\log N$. Primes are denoted $p, \ell, q$; $\tau(n)$ is the divisor function; $\omega(n)$ is the number of distinct prime factors; $v_p(n)$ is the $p$-adic valuation.

- **Arithmetic prime functions:** For integers $q \ge 1$ and $\gcd(u, q) = 1$,
  ```math
  \psi(x; q, u) = \sum_{\substack{n \le x \\ n \equiv u \ (q)}} \Lambda(n), \qquad
  \theta(x; q, u) = \sum_{\substack{p \le x \\ p \equiv u \ (q)}} \log p, \qquad
  \pi(x; q, u) = \sum_{\substack{p \le x \\ p \equiv u \ (q)}} 1.
  ```
  For a Dirichlet character $\chi \bmod q$ induced by primitive $\chi^* \bmod q^*$, $\psi(x, \chi) = \sum_{n \le x} \chi(n)\Lambda(n)$, and $N(\sigma, T, \chi) := \#\{\rho = \beta + i\gamma : L(\rho, \chi) = 0,\ \beta \ge \sigma,\ |\gamma| \le T\}$ (counted with multiplicity).
- **GRH hypotheses:** For an integer $q \ge 1$, **GRH($q$)** asserts that for every Dirichlet character $\chi \bmod q$, every zero $\rho$ of $L(s, \chi)$ with $0 < \Re(\rho) < 1$ satisfies $\Re(\rho) = 1/2$ (equivalently, $L(s, \chi) \ne 0$ for $\Re(s) > 1/2$, except the pole $s = 1$ of the principal character; equivalently, RH for $\zeta_{\mathbb{Q}(\zeta_q)}(s)$). **Dirichlet GRH** is GRH($q$) for every $q \ge 1$.
- **Paper VI multiplicative Lambert class `(H1)`–`(H4)`** (`papers/06-multiplicative-lambert/paper.tex` §1.1): fixed $q_0 \ge 3$, $\gcd(a_0, q_0) = 1$, $\delta \in (0, 1)$, $\kappa := 1 - \delta \in (0, 1)$, prime set $S$ (disjoint from divisors of $q_0$) containing every $p \equiv a_0 \pmod{q_0}$ with $\sum_{p \le x,\, p \in S} 1/p = \delta\log\log x + O(1)$; multiplicative $c : \mathbb{N} \to \mathbb{Z}_{\ge 0}$ with $c(1) = 1$, $c(p^e) \le e + 1$, $c(p) = 2$ on $S$, $c(p) = 0$ on $\mathcal{Q} := \{p \text{ prime} : p \nmid q_0,\ p \notin S\}$, and $c(p_0^{2u}) = 2u + 1$ for one $p_0 \in S$ and all $u \ge 0$. Set $L_c(b) := \sum_{n \ge 1} c(n) b^{-n}$ (writing $L := L_c(2)$ in base $2$), $x_n := \{b^n L_c(b)\}$, and $S(N, H) := \#\{N < n \le N + H : c(n) > 0\}$.
- **Window word counts and window discrepancy:** For a base-$b$ word $w = w_1 \cdots w_k$ of value $u = \sum_{i=1}^k w_i b^{k-i}$ with cylinder $I_w = [u b^{-k}, (u+1)b^{-k})$,
  ```math
  \#_w(N, H) := \#\{N \le n < N + H : \{b^n x\} \in I_w\}, \qquad D_{N, H}(x; b) := D_H(\{b^N x\}; b),
  ```
  where $D_H(y; b) = \sup_{0 \le s < t \le 1} \bigl|H^{-1}\#\{0 \le n < H : \{b^n y\} \in [s, t)\} - (t - s)\bigr|$ is the extreme interval discrepancy. Note that $\{b^n \{b^N x\}\} = \{b^{N+n} x\}$, so $D_{N, H}(x; b)$ is the exact extreme discrepancy of the moving window $(\{b^n x\})_{N \le n < N + H}$.
- **Strict quantifier separation:**
  - **Every sufficiently late window ("all windows"):** holds for **all** integers $N \ge N_0$ (and all $H$ in the stated range).
  - **Almost all windows ("almost all starts $N \in [X, 2X]$"):** for every $X \ge X_0$ and each $H$ in the stated range (e.g. $H \in [X^a, X]$), holds for all integers $N \in [X, 2X] \cap \mathbb{Z} \setminus \mathcal{E}(X, H)$, where the exceptional set $\mathcal{E}(X, H)$ depends on $H$ and satisfies $|\mathcal{E}(X, H)| = o(X)$ as $X \to \infty$ **uniformly** in $H$. **Simultaneity in $H$ is not claimed and does not follow** from the proofs below (covering $[X^a, X]$ by $O(\log X)$ dyadic lengths $H$ multiplies an $O(X(\log\log X)^{1+\kappa}/(\log X)^\kappa)$ exceptional set by $\log X$, which is not $o(X)$ when $\kappa < 1$).
- **`GF-22` dense character Lambert data** (`notes/phase22/odd-characters-and-kernel-quotient.md` §5): $\chi \bmod q$ nonprincipal of order $h \ge 2$, $G := \operatorname{Gal}(\mathbb{Q}(\zeta_h)/\mathbb{Q})$ of order $\varphi(h)$, $c_\chi = 1 * \chi : \mathbb{N} \to \mathbb{Z}[\zeta_h]$, $\Phi : \mathbb{Z}[\zeta_h] \to \mathbb{Z}$ nonzero **additive** (necessary by `GF-48` Proposition E), $c_\Phi = \Phi \circ c_\chi$, $C_\Phi = \max_j |\Phi(\zeta_h^j)|$, $x = F_b(c_\Phi) = \sum_{n \ge 1} c_\Phi(n) b^{-n}$, $T_P = \sum_{k \ge 1} c_\Phi(P + k) b^{-k}$, and $d \ge 2$ the exact order of $\chi(g_0) \ne 1$ for a chosen kill residue $g_0 \in (\mathbb{Z}/q\mathbb{Z})^\times$ (in particular $d = 3$ for cubic $L_\pm(b)$ mod $7$).
- **Reading labels:** `[R]` primary text directly read/fetched; `[A]` abstract or publisher metadata directly verified; `[S]` secondary literature summary; `[M]` our own mathematical deduction.

---

## 1. Track G1: Primary-Source Verification of External RH / Dirichlet GRH Formal Proofs & Evidence Policy

All primary sources below were fetched and inspected directly on **28 November 2026** (`[R]`).

### 1.1 Chronology and Immutable Primary Artifacts

1. **Original announcement and 17M-line release (20 November 2026):**
   - Primary document: Levent Alpöge, `https://alpo.ge/remark.pdf` (`[R]`, 4 pages, 245,114 bytes, extracted verbatim). Announces a Lean 4 formalization of RH and GRH for Dirichlet $L$-functions discovered and formalized with Anthropic's Claude, released as a 14-part archive `https://alpo.ge/lean.tar.gz.part01`…`part14` (assembled `lean.tar.gz`: 239,275,554 bytes, SHA-256 `9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc` per Waterloo log).
   - Scale & toolchain: **175,187 files**, **17,374,215 total lines** (15,531,759 code lines, zero comments), compiled under **Lean `v4.33.1`** (commit `819816b2`, 21 August 2026) and **Mathlib commit `0df444a3`**. Export size: 61,570,595,788 bytes (SHA-256 `5ea74b91…244e`), 1,468,418 declarations in `con-leche` / 1,484,729 in `nanoda` (different closure roots).
   - Method overview in `remark.pdf`: describes an iterated chain of $\sim \sqrt{X}$ theta lifts between totally definite unitary groups $U(X_0) \to U(X_1) \to \dots \to U(X_m)$ inspired by Stepanov's multiplicity method over function fields, coupled with seesaw/Bessel periods, Bost slope inequalities, relative trace formulas, weakened Vandiver/Selmer arguments, and Iwasawa/Behrend tower choices. Alpöge explicitly states that he has not yet written a human-readable paper and has not mastered every technical neighborhood of the proof.

2. **Lean FRO and Mathlib Initiative joint statement (21 November 2026, 13:55):**
   - Primary post: `https://leanprover-community.github.io/blog/posts/riemann-hypothesis/` (`[R]`, read verbatim). Certifies that all four criteria of Kevin Buzzard's 12 November 2026 verification checklist (`xenaproject.wordpress.com/2026/11/12/and-the-proof-is-checked-in-lean/`) are met—(i) statement accuracy (`RiemannHypothesis` in Mathlib), (ii) clean community compilation reproducing an identical raw export, (iii) independent statement matching via `comparator` and `con-leche --compare` against an isolated Mathlib-only challenge file, and (iv) validation of the inert proof export by Lean's official kernel plus independent checkers including `con-leche` and `con-ron` (which carry formal soundness proofs relative to set theory)—and expresses "full confidence that Alpöge's proof of the Riemann Hypothesis is correct."

3. **Shortened rewriting `lsernau/grh-lean` (25 November 2026):**
   - Primary repository: `https://github.com/lsernau/grh-lean` (`[R]`, GitHub API + raw files fetched directly).
   - **Exact immutable Git commit SHA:** **`72fead102f663d5c7a407964a13dc0cf9d977207`** (sole commit, SSH-signed by Luke Sernau, timestamp `2026-11-25T20:38:07Z`, Git tree SHA `5eb1240f03e791edd3fc7aa84a3a7d8dc3997b7f`, `git archive HEAD` SHA-256 `9138cf2f5862e64f823ed676e8d37333c0717e1a13cd8f74f6b735ab2d1ba57c`; Apache 2.0, Copyright 2026 Anthropic, PBC).
   - **Exact Lean toolchain** (`grh/lean-toolchain` and `grh-compact/lean-toolchain`, identical): **`leanprover/lean4:v4.35.0`** (official release commit `eb6cafb7`).
   - **Exact Mathlib commit SHA** (`grh/lake-manifest.json` and `grh-compact/lake-manifest.json`, identical): **`56a005855ea17e0b0958f73ec801ae140b0a1679`** (13 October 2026), with pinned transitive dependencies `batteries` (`66e469188fe07963e5cf666c7d4433f45b8131c5`), `aesop` (`4a174c490d8707121c4a9290800489f105d85e07`), `Qq` (`dce0ad79c486cb1fb504af04f953c3466b0c6db8`), `Cli` (`c24fe6078c630e89b489bffe59b3e20ac30d12c8`), `plausible` (`dfa4f38190d07c37e315953e08b90fe2d95b3c24`), `importGraph` (`a41f0e9a4dea23188ea9cc1c41ac9f8bbafe0b93`), `proofwidgets` (`df72b022e558978a1c50264cfc4d7fec86fa8e04`), and `LeanSearchClient` (`d6b4c7be5be75ec4917c873ac50c756dc1436372`).
   - **Two Lake projects inside `lsernau/grh-lean`:**
     - **Readable edition (`grh/`):** 803 `.lean` files under `src/` (`src/Lib` 495, `src/New` 306, plus `Statements.lean`, `Main.lean`), **477,124 total lines** / **299,902 code lines** (`98.0691%` code reduction vs. Alpöge original, certified in `C1`), export 4,485,867,644 bytes (SHA-256 `baf221c8…6fc1`), 216,571 declaration records (`165,163` Mathlib/core + `51,408` project; `216,568` in `lean4lean`).
     - **Compact edition (`grh-compact/`):** 794 `.lean` files under `src/` (`src/Lib` 573, `src/New` 219, plus `Statements.lean`, `Main.lean`), **112,827 total lines** / **76,149 code lines** (`99.5097%` code reduction vs. Alpöge original, certified in `C1`), export 5,172,274,528 bytes (SHA-256 `ab7b4223…115b`), 204,583 declaration records (`165,163` Mathlib/core + `39,420` project; `204,580` in `lean4lean`).

### 1.2 Exact Verbatim Lean 4 Theorem Signatures

Fetched directly from `lsernau/grh-lean` at commit `72fead102f663d5c7a407964a13dc0cf9d977207` (`grh/src/Statements.lean` and `grh-compact/src/Statements.lean` are byte-identical; `grh/src/Main.lean` and `grh-compact/src/Main.lean` prove the exact same five declarations):

**`src/Statements.lean`** (imports ONLY `Mathlib`):
```lean
import Mathlib

def RiemannZetaZerosOnLine : Prop :=
  ∀ s : ℂ, riemannZeta s = 0 → (¬∃ n : ℕ, s = -2 * ((n : ℂ) + 1)) → s ≠ 1 → s.re = 1 / 2

def DirichletLNonvanishingRightOfHalf : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ),
    1 / 2 < s.re → (χ ≠ 1 ∨ s ≠ 1) → DirichletCharacter.LFunction χ s ≠ 0

def DirichletLZerosOnLine : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ),
    0 < s.re → s.re < 1 → DirichletCharacter.LFunction χ s = 0 → s.re = 1 / 2

def PrimitiveDirichletLZerosOnLine : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive →
    ∀ s : ℂ, 0 < s.re → s.re < 1 → DirichletCharacter.LFunction χ s = 0 → s.re = 1 / 2
```

**`src/Main.lean`**:
```lean
theorem riemannHypothesis : RiemannHypothesis := New.zeta_zeros_on_line New.grh
theorem riemannZeta_eq_zero_re : RiemannZetaZerosOnLine := riemannHypothesis
theorem LFunction_ne_zero_of_half_lt_re : DirichletLNonvanishingRightOfHalf := New.grh
theorem LFunction_eq_zero_re : DirichletLZerosOnLine := New.zeros_on_line New.grh
theorem LFunction_eq_zero_re_of_isPrimitive : PrimitiveDirichletLZerosOnLine :=
  fun N _ χ _ ↦ LFunction_eq_zero_re N χ
```

**Mathlib's `RiemannHypothesis`** (verified verbatim from `math.mit.edu/~drew/grh/audit.log` and `shortgrh/explicit-statements.out`, declared in `Mathlib.NumberTheory.LSeries.RiemannZeta`):
```lean
def RiemannHypothesis : Prop :=
  ∀ (s : ℂ), riemannZeta s = 0 → (¬∃ n, s = -2 * (↑n + 1)) → s ≠ 1 → s.re = 1 / 2
```

### 1.3 Axiom Dependencies and Independent Multi-Kernel Verification Matrix

All five theorems in both the original 17M-line release (`audit.log`) and both editions of `lsernau/grh-lean@72fead10` (`compact-axioms.log`, `readable-axioms.log`, `mrubinst.github.io`) depend strictly on the three standard axioms:
```text
'riemannHypothesis'                   depends on axioms: [propext, Classical.choice, Quot.sound]
'riemannZeta_eq_zero_re'              depends on axioms: [propext, Classical.choice, Quot.sound]
'LFunction_ne_zero_of_half_lt_re'     depends on axioms: [propext, Classical.choice, Quot.sound]
'LFunction_eq_zero_re'                depends on axioms: [propext, Classical.choice, Quot.sound]
'LFunction_eq_zero_re_of_isPrimitive' depends on axioms: [propext, Classical.choice, Quot.sound]
```
No `sorryAx`, `Lean.ofReduceBool`, `Lean.ofReduceNat`, `Lean.trustCompiler`, or custom axioms appear (all 15 axioms in the environment reside in `Init`).

| Checker / Audit | Original 17M-line (MIT `~drew/grh/`, Waterloo `grh-lean-verification`) | `lsernau/grh-lean@72fead10` Readable (`grh/`) | `lsernau/grh-lean@72fead10` Compact (`grh-compact/`) |
| --- | --- | --- | --- |
| **Full build** | Pass (175,187 modules, Lean `v4.33.1`, sandboxed rebuild matches export byte-for-byte) | Pass (803 modules, 9,852 jobs, Lean `v4.35.0`, MIT sandboxed) | Pass (794 modules, 9,843 jobs, Lean `v4.35.0`, MIT sandboxed + Waterloo) |
| **Lean kernel replay (`leanchecker`)** | Pass (175,187/175,187 MIT + Waterloo; `--from-export` v4.36.0 accepts, 82.6 GiB) | Pass (803/803, 12m00s, MIT) | Pass (794/794, 12m08s MIT + Waterloo) |
| **Lean paranoid kernel** | Pass (`leanchecker-paranoid --from-export` v4.36.0, 98.8 GiB) | Pass (via `lake comparator --paranoid`, MIT machine B) | Pass (MIT machines A & B + Waterloo) |
| **`nanoda` (Rust kernel)** | Pass (MIT 27m42s; Waterloo 1,484,729 decls) | Pass (MIT machine B, 2 passes) | Pass (MIT machines A & B + Waterloo) |
| **`lean4lean` (Lean-in-Lean kernel)** | Pass (175,187/175,187; 5 modules needed raised step limit) | Pass on MIT machine B (332 GB RAM); stopped at 70 GB guard on 128 GB machine A | Pass (~7 GB RAM; MIT machines A & B + Waterloo) |
| **`con-leche` (verified relative to set theory)** | Pass (`master` `cd2eceab`: 1,468,418 decls `--verified`; `--compare` `5dc36dc1` justifies all 5) | Pass (`lake comparator --paranoid` + standalone `--compare`) | Pass (`lake comparator --paranoid` + standalone 204,583 decls, 1m52s) |
| **`con-ron` (Rust port of `con-leche`)** | Pass (`master` `3f22699b` `--compare`: 1,468,418 sol / 51,692 chal) | Pass (`lake comparator --paranoid` + standalone `--compare`) | Pass (`lake comparator --paranoid` + standalone 204,583 decls, 1m15s) |
| **`Comparator` / `lake comparator`** | Pass (`Comparator v4.33.0` + `lake comparator` v4.36.0: `"Your solution is okay!"`) | Pass (MIT machine B `--paranoid` 4h10m + plain 39m03s: `"Your solution is okay!"`) | Pass (MIT machine A 2h32m, machine B 2h11m, Waterloo 5h [no-sandbox]: `"Your solution is okay!"`) |

**External arithmetic corollary note (`schoenfeld-rh-lean`):** MIT's `~drew/shortgrh/` also records that `github.com/AndrewVSutherland/schoenfeld-rh-lean` (commit `0e52d7b1`) composed with `grh-compact` (`72fead10`) passed `lake comparator --paranoid` on 26 November 2026 (all 6 kernels, 206,292 declarations), establishing Schoenfeld's (1976) explicit bound $|\psi(x) - x| < \sqrt{x}\log^2 x / (8\pi)$ for $x \ge 73.2$ as a Lean theorem using Mathlib only. Crucially, this covers **$q = 1$ ($\zeta(s)$) only**, NOT Dirichlet progressions $\psi(x; q, u)$.

### 1.4 Exact Mathematical Scope of the Proved $L$-Functions

The five theorems cover **strictly and exclusively**:
- The Riemann zeta function $\zeta(s)$ (`riemannZeta`), and
- Every Dirichlet $L$-function $L(s, \chi)$ (`DirichletCharacter.LFunction χ s`) for **every modulus $N \ge 1$** (`[NeZero N]`) and **every Dirichlet character $\chi : (\mathbb{Z}/N\mathbb{Z})^\times \to \mathbb{C}^\times$** (primitive or imprimitive, principal or nonprincipal, real or complex) in the open critical strip $0 < \Re(s) < 1$ (and nonvanishing on $\Re(s) > 1/2$ except at $s = 1$ for $\chi = 1$).

By Artin's factorization of abelian Dedekind zeta functions $\zeta_K(s) = \prod_\chi L(s, \chi^*)$ (not formalized inside `grh-lean`), this algebraically implies RH for $\zeta_K(s)$ for every abelian number field $K/\mathbb{Q}$ (in particular every cyclotomic field $\mathbb{Q}(\zeta_q)$).

**Explicit exclusions (NOT proved by `grh-lean`):**
1. **No Extended Riemann Hypothesis (ERH)** for non-abelian number fields $K/\mathbb{Q}$ (Dedekind zeta functions $\zeta_K(s)$ where $K/\mathbb{Q}$ is non-abelian; Alpöge explicitly states on p. 1 of `remark.pdf` that ERH is not yet proved).
2. **No Hecke $L$-functions** $L(s, \psi)$ for Grössencharaktere of number fields $K \ne \mathbb{Q}$ (e.g., imaginary quadratic class-group / CM characters).
3. **No non-abelian Artin $L$-functions** (e.g., $A_4, S_4, A_5$ Galois representations).
4. **No automorphic $L$-functions** $L(s, \pi)$ on $\mathrm{GL}_n$ ($n \ge 2$), modular-form $L$-functions (weight-1 exotic forms, weight-$k \ge 2$ cusp forms, elliptic-curve $L$-functions, Ramanujan $\Delta$), or symmetric-power $L$-functions.
5. **No zeros on $\Re(s) \le 0$** (recall that imprimitive Dirichlet characters have infinitely many Euler-factor zeros on $\Re(s) = 0$).
6. **No explicit-formula prime bounds in arithmetic progressions** inside `grh-lean` itself (Theorem A for $\psi(x; q, u)$ remains a written classical analytic deduction from `DirichletLZerosOnLine`).

### 1.5 Documented Caveats and Resolved Anomalies in the Verification Record

1. **No human peer review and no complete human-readable proof:** Both `lsernau/grh-lean/README.md` (*"The proof has passed machine checks only... No mathematician has read it through, and no paper comes with it"*) and MIT's caveats explicitly emphasize that passing kernel checks guarantees formal derivability in Lean's type theory from the 3 standard axioms and Mathlib's definitions, **not** human comprehension or refereed publication. Rubinstein's 45-page outline (v1.5, 27 Nov 2026) and 265-page draft (v2, 22 Nov 2026) are incomplete working study guides that still reduce main theorems to Lean inputs.
2. **Semantic audit of Mathlib definitions across versions:** Trusting the mathematical meaning relies on checking that Mathlib's `riemannZeta`, `DirichletCharacter.LFunction`, `DirichletCharacter.IsPrimitive`, `HurwitzZeta.hurwitzZeta`, `Complex.Gamma`, and `mellin` match standard complex-analytic definitions. MIT's `compare-closures.py` confirms that all top-level definitions are identical between Mathlib `0df444a3` (v4.33.1) and `56a00585` (v4.35.0), while 10,750 of 50,232 shared lower-level declarations changed across the two Mathlib versions without a formal cross-version equivalence proof.
3. **Documented build/checker anomalies (all resolved and non-logical):**
   - *Original 17M-line build:* 1 of 175,187 `.olean` files (`LocModel.olean`) varied non-deterministically in 38 bytes due to a parallel elaboration bound-variable naming race in `BBtop.eq_1` (Lean issue `#15498`, fixed in PR `#15499` / v4.36.0); the proof export does not contain `BBtop.eq_1` and was byte-identical across sandboxed rebuilds. Five modules required raising `lean4lean`'s default step limit on `decide +kernel`. Older `con-leche`/`con-ron` binaries bundled in v4.36.0 exited with code 2 (unsupported reflexive inductive type); `master` builds (`cd2eceab`, `3f22699b`) accepted all 1,468,418 declarations.
   - *Shortened `lsernau/grh-lean@72fead10`:* On `grh/` (readable), `lean4lean` peaked at 332 GB RAM (stopped by MIT's 70 GB memory guard on 128 GB machine A; passed on machine B). On `grh-compact/`, Waterloo's `lake comparator --paranoid` ran with `--inadvisably-no-sandbox` due to cluster AppArmor restrictions (MIT's runs on both machines A and B were fully bubblewrap-sandboxed).

### 1.6 Rigorous Evidence-Classification Policy for `GF-48` and Phase 26 Corollaries

Applying [`docs/research-objectives.md`](../../docs/research-objectives.md) (Rules 2, 3, 4) and [`docs/benchmarks/SCHEMA.md`](../../docs/benchmarks/SCHEMA.md):
1. **Never `Kernel-verified` in this repository:** Even though Dirichlet GRH itself has a multi-kernel-verified external Lean 4 proof (`lsernau/grh-lean@72fead10`), **no** corollary in `GF-48` or Phase 26 Track G is a `Kernel-verified` theorem of `MathematicsResearch`, because neither `grh-lean` nor the analytic bridge (`DirichletLZerosOnLine` $\implies$ Theorem A / Selberg variance $\implies$ Lambert window planting) is formalized inside `NormalityChecker`.
2. **Conservative classification recommendation for `GF-48` and Phase 26:** Keep every Dirichlet-GRH-dependent deduction **strictly separated** from unconditional theorems and labeled **`Conditional / External-GRH (Dirichlet GRH — machine-verified externally in Alpöge–Claude 2026 / lsernau/grh-lean@72fead10, pending human peer review)`**. Under [`docs/research-objectives.md`](../../docs/research-objectives.md) Rule 2, a release that no human mathematician has read through is not yet a peer-reviewed published theorem; therefore it should **not** silently promote `Conditional` claims into unconditional `Paper proof` status or authorize any change on `BC-01`…`BC-50`. Once the mathematical community completes human verification / refereed publication (or if the repository owner explicitly adopts multi-kernel-verified external Lean artifacts as qualifying `External input` under Rule 4), the label transitions cleanly to `Paper proof` with `inputs = ["Dirichlet GRH (Alpöge–Claude 2026 / lsernau/grh-lean@72fead10)"]` — while STILL preserving strict separation between unconditional and GRH-dependent results.

---

## 2. Track G2: Precise Statements (Lambert Window Extensions)

Every result below either holds **unconditionally** (zero GRH) or specifies the exact Dirichlet GRH hypothesis (`GRH(q_0)` vs. `Dirichlet GRH`).

### 2.1 Critical Boundary $H = \sqrt{N}(\log N)^C$ under Dirichlet GRH (G2.1)

**Theorem G2.1A (Paper VI at $H = \sqrt{N}(\log N)^C$; Conditional / External-GRH on `GRH(q_0)`).**
Assume Paper VI's `(H1)`–`(H4)` and **GRH($q_0$)** (with Corollary A.2 constant $C_2$). Fix a binary word $w$ of length $k \ge 1$ and value $u$, and a constant $C_R \ge 0$.
1. **Every fixed $C > 2$:** There exist $N_0 = N_0(w, C, C_R)$ and $c_1 = c_1(w, C) > 0$ such that for all integers $N \ge N_0$, all $\sqrt{N}(\log N)^C \le H \le N$, and all $0 \le R \le C_R \log\log N$,
   ```math
   \#\{N \le n < N + H : n \text{ is } R\text{-isolated for } w\} \ge c_1 \frac{H (\log\log N)^\delta}{\log N}.
   ```
   Consequently, every word $w$ containing a $1$ satisfies $H(\log\log N)^\delta/\log N \ll_{w,C} \#_w(N, H) \ll H/(\log N)^\kappa$, every binary word occurs in every window $[N, N + \lceil\sqrt{N}(\log N)^C\rceil)$ for $N \ge N_0(w, C)$, and the window discrepancy gap satisfies
   ```math
   \frac{(\log\log N)^{1+\delta}}{\log N} \ll_C 1 - D_{N, H}(L; 2) \ll \frac{\log\log N}{(\log N)^\kappa}.
   ```
2. **Sharp endpoint $C = 2$ (fixed word):** For every $K > 4\sqrt{2}\, C_2 \varphi(q_0) p_0^u$, the same $R$-isolated planting holds with $m = 1$ ($b = p_0^{2u}$) on $K\sqrt{N}(\log N)^2 \le H \le N$, giving $\#_w(N, H) \gg_{w, K} H/\log N$ (and $1 - D_{N, H}(L; 2) \gg_K (\log\log N)/\log N$ for $K > 4\sqrt{2}\, C_2 \varphi(q_0) p_0$).
3. **Continuous interpolation to full order:** For any fixed $\alpha \in (0, 1)$, on $\sqrt{N}\exp(\frac{1}{2}(\log N)^\alpha)(\log N)^3 \le H \le N$, planting with $M = \exp(\frac{1}{2}(\log N)^\alpha)$ yields $\#_w(N, H) \gg_{w, \alpha} H (\log N)^{\alpha\delta - 1}$. Reaching the full Paper VI order $H/(\log N)^\kappa$ via single-prime planting requires $\log M \asymp \log N$, i.e. $H \ge N^{1/2 + \varepsilon}$.

**Theorem G2.1B (`GF-22` method barrier at $H = \sqrt{N}(\log N)^C$ and threshold of the $t = 2$ CRT method).**
Let $\chi \bmod q$ be nonprincipal of order $h \ge 2$, $\Phi : \mathbb{Z}[\zeta_h] \to \mathbb{Z}$ nonzero additive, $b \ge 2$, $w$ a base-$b$ word, and $d \ge 2$ the exact order of $\chi(g_0) \ne 1$.
1. **Polylogarithmic method barrier (Paper proof, unconditional):** In `GF-22`'s CRT construction (even after the factor-2 improvement of Theorem G2.4A), the modulus $q' = q Q(N, w)$ satisfies $\log \varphi(q') \sim (\alpha d/\log b)\log\log N \cdot \log\log\log N$ ($\alpha = 2$ in `GF-48`; $\alpha = 1$ in Theorem G2.4A; $\alpha = \alpha_*(\chi) < 1$ under moment optimization), so $\varphi(q') / (\log N)^C \to \infty$ for **every** fixed $C > 0$. Consequently, **no** fixed power $C > 0$ makes $H = \sqrt{N}(\log N)^C$ admissible in either Step 5′ (Theorem A prime supply) or Step 6′ (Lemma E.2 Markov tail) of this CRT method. (For odd-order characters, Theorem G2.4B(2) further rules out arbitrary zero-block unions/sieves of length $L \ge c\log_b\log N$.)
2. **Threshold of the $t = 2$ CRT method (Conditional / External-GRH on Dirichlet GRH):** For every fixed constant $C_0 > d/\log b$ (resp. $C_0 > 2d/\log b$ without Theorem G2.4A's Shiu second-moment step; optimizing the Shiu moment at $t = t_*$ via Theorem G2.4A lowers this threshold further to $C_0 > \alpha_*(\chi) d/\log b$), uniformly for
   ```math
   \sqrt{N}\exp\bigl(C_0 \log\log N \cdot \log\log\log N\bigr) \le H \le N \qquad (N \ge N_0(w, C_0)),
   ```
   every base-$b$ word $w$ satisfies $\#_w(N, H) \ge H\exp(-C_w \log\log N \cdot \log\log\log N) \to \infty$, beating every fixed power $N^{1/2 + \varepsilon}$.

### 2.2 Almost-All-Window Results Below Exponent $1/2$ and Unconditional `GF-22` Upgrades (G2.2)

*(Positioning note on G2.2A and G2.2A′: For the multiplicative **support count** $S(N, H)$ alone on almost all short intervals, Hooley (1994) already established the order of magnitude $S(N, H) \asymp H/\sqrt{\log X}$ for sums of two squares ($c = 1 * \chi_{-4}$) down to $H/\sqrt{\log X} \to \infty$, and Matomäki–Radziwiłł II (`arXiv:2007.04290` `[R]`) established the full asymptotic $S(N, H) \sim C_f H/(\log X)^\kappa$ for general sparse multiplicative supports down to $H/(\log X)^\kappa \to \infty$ (see §4.1 and Theorem G2.3(2)). Theorems G2.2A and G2.2A′ are **word-count and $R$-isolated planting** theorems for the base-$2$ expansion of $L_c(2)$: controlling prescribed finite binary words $w$ and window disjunctivity requires locating $R$-isolated starts $n = bp - j_0$ via primes in progressions, which does not follow from $S(N, H)$ alone.)*

**Theorem G2.2A (Paper VI unconditional almost-all-window word counts and $R$-isolated planting below $1/2$; Lean-supported paper proof).**
Assume Paper VI's `(H1)`–`(H4)` (zero GRH). Let $A = 12/5$ via the log-free zero-density estimate of **Thorner–Zaman (2024, *Math. Z.* **306**, Theorem 2.1)** `[R]` (combining **Huxley 1975** away from $\sigma = 1$ with **Jutila 1977, *Math. Scand.* **41**, Theorem 1** `[R]` on $[\frac{4}{5}, 1]$), so $\vartheta_* := 1 - 2/A = \mathbf{1/6}$. Fix any **$1/6 < a \le 1$**, any binary word $w$ of length $k \ge 1$, and any $C_R \ge 0$. For every $X \ge X_0(w, a, C_R)$ and each $H \in [X^a, X]$, for **almost all** integer starts $N \in [X, 2X]$ (all $N \notin \mathcal{E}(X, H)$ with $|\mathcal{E}(X, H)| = o(X)$ uniformly in $H$, not simultaneously in $H$):
1. $\#\{N \le n < N + H : n \text{ is } R\text{-isolated for } w\} \gg_{w, a} H / (\log X)^\kappa$ (for $0 \le R \le C_R\log\log X$);
2. if $w$ contains a $1$, then $\#_w(N, H) \asymp_{w, a} H/(\log X)^\kappa$, and $H - \#_{0^k}(N, H) \asymp_{k, a} H/(\log X)^\kappa$;
3. the window discrepancy gap satisfies $1 - D_{N, H}(L; 2) \asymp_a (\log\log X)/(\log X)^\kappa$.

*(Preprint addendum `[R]`: splitting $\sigma \in [\frac{1}{2}, 1]$ at $\sigma_0 = \frac{4}{5}$ and pairing **Jutila 1977, Theorem 1** `[R]` on $[\frac{4}{5}, 1]$ with the unrefereed preprint **Chen–Gupta–Li `arXiv:2507.08296v2`** `[R]` on $[\frac{1}{2}, \frac{4}{5}]$ lowers $\vartheta_*$ from $1/6$ to $\mathbf{1/7}$ via its uniform exponent $A = 7/3$, and to $\mathbf{2/15}$ via its Theorem 2 $T$-aspect exponent $30/13$ at fixed $q_0$.)*

**Theorem G2.2A′ (Paper VI almost-all-window word counts and $R$-isolated planting under `GRH(q_0)` down to $\theta > 0$ and $(\log X)^{2+\varepsilon}$; Conditional / External-GRH).**
Assume `(H1)`–`(H4)` and **GRH($q_0$)**.
1. **Power windows $H = X^\theta$, every fixed $\theta \in (0, 1]$:** All three conclusions (1)–(3) of Theorem G2.2A hold for **almost all** $N \in [X, 2X]$ (uniformly for $X^\theta \le H \le X$).
2. **Polylogarithmic windows $H / (\log X)^2 \to \infty$ (in particular $H = (\log X)^{2+\varepsilon}$ for any $\varepsilon > 0$):** For every binary word $w$, for **almost all** $N \in [X, 2X]$, $\#_w(N, H) \gg_w H/\log X \to \infty$ (in particular $w$ occurs in almost all windows $[N, N + \lceil(\log N)^{2+\varepsilon}\rceil)$).

**Theorem G2.2C (Unconditional `GF-22` on EVERY window $N^a \le H \le N$ for $7/12 < a \le 1$; Paper proof).**
Let $\chi, \Phi, b, w$ be as in Theorem G2.1B (zero GRH). Applying standard short-interval PNT machinery in progressions — specifically the log-free zero-density estimate of **Thorner–Zaman (2024, *Math. Z.* **306**, Theorem 2.1)** `[R]` (combining **Huxley 1975** with **Jutila 1977, Theorem 1** `[R]` on $[\frac{4}{5}, 1]$; see also Thorner–Zaman Theorem 1.1 & Remark 1.3), two-family Landau–Page avoidance ($|t| \le 10$), and the uniform Vinogradov–Korobov zero-free region ($|t| \ge 10$; classical non-explicit shape in Montgomery 1971 p. 176 / 1994 Ch. 9, explicit constants via **Khale 2024, Theorem 1.1** `[R]`) — to our Landau–Page-avoiding CRT moduli $q' = q Q_\nu = N^{o(1)}$, for **every fixed $7/12 < a \le 1$**, uniformly for all $N \ge N_0(w, a)$ and **every** window $N^a \le H \le N$,
```math
\#_w(N, H) \ge H \exp\bigl(-C_w \log\log N \cdot \log\log\log N\bigr)
```
with any fixed $C_w > d/\log b$ (using Theorem G2.4A; or $C_w > 2d/\log b$ using Lemma E.2 directly). This applies standard short-interval PNT techniques in progressions to `GF-22`'s growing CRT moduli (provisional priority, Rule 5), upgrading Phase 25 Proposition D.2 from $H \ge N\exp(-c_3\sqrt{\log N})$ to every fixed $a > 7/12$ unconditionally. *(Preprint addendum `[R]`: pairing **Jutila 1977, Theorem 1** `[R]` on $[\frac{4}{5}, 1]$ with **Chen–Gupta–Li `arXiv:2507.08296v2`** `[R]` on $[\frac{1}{2}, \frac{4}{5}]$ lowers $7/12$ to $4/7$ via its uniform $A = 7/3$, and to $17/30$ via its Theorem 2 $T$-aspect exponent $30/13$ since $q' = U^{o(1)}$.)*

**Theorem G2.2D (Unconditional `GF-22` on almost all windows below $1/2$, $1/6 < a \le 1$; Paper proof).**
In the setting of Theorem G2.2C (zero GRH), for **every fixed $1/6 < a \le 1$** and each $H \in [X^a, X]$, for **almost all** integer starts $N \in [X, 2X]$ ($N \notin \mathcal{E}(X, H)$, $|\mathcal{E}(X, H)| = o(X)$ uniformly in $H$), $\#_w(N, H) \ge H\exp(-C_w \log\log X \cdot \log\log\log X)$ (and down to $1/7 < a \le 1$, resp. $2/15 < a \le 1$ in $T$-aspect, when pairing Jutila 1977 on $[\frac{4}{5}, 1]$ with `arXiv:2507.08296v2` `[R]`).

**Theorem G2.2B (Dirichlet-GRH `GF-22` on almost all windows down to sub-polynomial $X^{o(1)}$; Conditional / External-GRH).**
Assume Dirichlet GRH. For every fixed $C_1 > 2d/\log b$ (resp. $C_1 > 4d/\log b$ without Theorem G2.4A) and each window length $\exp(C_1 \log\log X \cdot \log\log\log X) \le H \le X$ (in particular **$H = X^\theta$ for every fixed $\theta > 0$**), for **almost all** integer starts $N \in [X, 2X]$, $\#_w(N, H) \ge H\exp(-C_w \log\log X \cdot \log\log\log X)$.

### 2.3 Exact Leading Window Discrepancy Constants (G2.3)

**Theorem G2.3 (Window Sub-Threshold Width Law & `GF-12` Window Constants).**
Assume $c$ lies in Paper VI's class `(H1)`–`(H4)` (with split prime density $\delta \in (0, 1)$, $\kappa = 1 - \delta$), and fix an integer radix $b \ge 2$ and fixed $0 < a \le 1$. Put $\omega_b = 0$ if $b = 2^k$, and $\omega_b = \frac{\delta\log 2}{\kappa}$ if $b \ne 2^k$. For $b = 2^s b'$ ($b' > 1$ odd), let $\beta_b = \log b / \log b' \ge 1$ and $\delta^*_b = \beta_b / (\beta_b + \log 2)$ (`GF-21` Theorem B1; for odd $b$, $\delta^*_b = \frac{1}{1+\log 2} = 0.590616\ldots$; for $b = 6, 10, 12$, $\delta^*_b \approx 0.701754, 0.673632, 0.765433$).
1. **Unconditional self-normalized exact window law (Lean-supported paper proof):** Whenever $N^a \le H \le N$ and the local support count satisfies $S(N, H) \gg_a H/(\log N)^\kappa$ — which holds unconditionally for **all** windows with $a > 0.53$ by Paper VI `thm:kumchev`, for **almost all** $N \in [X, 2X]$ with $a > 1/6$ by Theorem G2.2A, for **almost all** $N \in [X, 2X]$ at **every fixed $a > 0$** for $\chi_{-4}$ (sums of two squares) by published **Hooley (1994)** `[S]` and for all `(H1)`–`(H4)` by **Matomäki–Radziwiłł II (`arXiv:2007.04290`, Corollary 1)** `[R]` (preprint), and under `GRH(q_0)` for all windows $a > 1/2$ and almost all windows $a > 0$ — if either $b = 2^k$ or $\delta \le \delta^*_b$, then
   ```math
   1 - D_{N, H}(L_c(b); b) = \sup_{x \in \mathbb{R}} \bigl|D_{N, H}(x + L_c(b); b) - D_{N, H}(x; b)\bigr| = \bigl(1 + \omega_b + o(1)\bigr) \frac{\kappa}{\log b} \cdot \frac{S(N, H)}{H} \log\log N.
   ```
2. **Explicit `GF-12` constants on windows:** Suppose further that $S$ is a union of reduced residue classes modulo $q_0$ (in particular $c = 1 * \chi$ for any real nonprincipal $\chi \bmod q_0$, with $\delta = \kappa = 1/2$ and Landau–Wirsing constant $C_\chi$, where $C_{\chi_4} = K = 0.76422365\ldots$, or Paper VI `ex:quarter` with $\delta = 1/4$). Then
   ```math
   1 - D_{N, H}(L_c(b); b) \sim \begin{cases} \dfrac{C_f \kappa}{\log b} \dfrac{\log\log N}{(\log N)^\kappa}, & b = 2^k, \\[2ex] \dfrac{C_f (\kappa + \delta\log 2)}{\log b} \dfrac{\log\log N}{(\log N)^\kappa}, & b \ne 2^k,\ \delta \le \delta^*_b \end{cases}
   ```
   holds:
   - **(a) Unconditionally on ALL windows** (Lean-supported paper proof) uniformly for all $N\exp(-c_1\sqrt{\log N}) \le H \le N$ (via the zero-free Selberg–Delange Hankel contour);
   - **(b) Under `GRH(q_0)` on ALL windows** (Conditional / External-GRH) uniformly for all $\sqrt{N}\exp\bigl(C_2 \frac{\log N}{\log\log N}\bigr) \le H \le N$ — in particular for **every fixed $a > 1/2$** (via the uniform two-sided GRH bound for $\log L$ on the branch-free contour $\sigma_1 = \frac{1}{2} + c/\log\log N$);
   - **(c) Unconditionally on ALMOST ALL windows for every fixed $0 < a \le 1$** (Paper proof using the unrefereed preprint input **Matomäki–Radziwiłł II, `arXiv:2007.04290`, Corollary 1** `[R]`) for all $N \in [X, 2X] \setminus \mathcal{E}(X, H)$ with $|\mathcal{E}(X, H)| = o(X)$ uniformly in $X^a \le H \le X$.

### 2.4 Sharpened `GF-22` Lower Bounds and the CRT / Union Zero-Block Barriers (G2.4)

**Theorem G2.4A (Universal Second-Moment Shiu Reduction for `GF-22` / Cubic $L_\pm(b)$; Paper proof).**
Let $\chi \bmod q$ be **any** nonprincipal Dirichlet character of order $h \ge 2$, let $G = \operatorname{Gal}(\mathbb{Q}(\zeta_h)/\mathbb{Q})$, and let $\Phi : \mathbb{Z}[\zeta_h] \to \mathbb{Z}$ be **any** nonzero additive map. Every Galois conjugate $\chi^\sigma := \sigma \circ \chi$ ($\sigma \in G$) is nonprincipal of order $h$ and satisfies the universal exact identity
```math
\kappa_2(\chi^\sigma) := \frac{1}{\varphi(q)} \sum_{\gcd(r, q) = 1} |1 + \chi^\sigma(r)|^2 = 2.
```
By trace duality on $\mathbb{Q}(\zeta_h)/\mathbb{Q}$ (equivalently Vandermonde inversion on the $\mathbb{Z}$-basis $\{1, \zeta_h, \dots, \zeta_h^{\varphi(h)-1}\}$), there exists a unique $\beta_\Phi \in \mathbb{Q}(\zeta_h)$ such that $\Phi(z) = \operatorname{Tr}_{\mathbb{Q}(\zeta_h)/\mathbb{Q}}(\beta_\Phi z) = \sum_{\sigma \in G} \sigma(\beta_\Phi)\sigma(z)$ for all $z \in \mathbb{Z}[\zeta_h]$, giving the exact Galois-conjugate bounds
```math
|\Phi(c_\chi(n))| \le C'_\Phi \sum_{\sigma \in G} |c_{\chi^\sigma}(n)|, \qquad |\Phi(c_\chi(n))|^2 \le K_\Phi \sum_{\sigma \in G} |c_{\chi^\sigma}(n)|^2,
```
with $C'_\Phi := \max_{\sigma \in G} |\sigma(\beta_\Phi)|$ and $K_\Phi := \operatorname{Tr}_{\mathbb{Q}(\zeta_h)/\mathbb{Q}}(\beta_\Phi \overline{\beta_\Phi}) \in \mathbb{Q}_{>0}$. Applying Cauchy–Schwarz, Shiu's theorem to each of the $\varphi(h)$ multiplicative functions $|c_{\chi^\sigma}|^2$, and Chebyshev's inequality to $|T_{Au+L}|$ in Step 6′ of `GF-22` (for any $N^a \le H \le N$ with $a > 0$) reduces the required zero-block length $L(N)$ from $2\log_b\log N + O_w(1)$ to **$\log_b\log N + O_{q, \Phi, w, a}(1)$**, halving the $t = 2$ CRT exponent constant universally from $2d/\log b$ to **$d/\log b$**:
```math
\#_w(N, H) \ge H \exp\Bigl(-\bigl(\tfrac{d}{\log b} + \varepsilon\bigr) \log\log N \cdot \log\log\log N\Bigr)
```
for every $\varepsilon > 0$ (for cubic $L_\pm(2)$: $6/\log 2 \approx 8.656$ drops to $3/\log 2 \approx 4.328$). For general $t \ge 1$, Hölder's inequality + Shiu on each $|c_{\chi^\sigma}|^t$ yields $b^L \gg (\log N)^{\kappa_t(\chi)/t}$ with $\alpha_*(\chi) := \inf_{t \ge 1} \kappa_t(\chi)/t$: as $h \to \infty$, $t = 2$ is proved by strict log-convexity to be the **unique global minimizer** of $\kappa_t(\infty)/t$, while for every finite integer $h \ge 2$ an exact Fourier-series identity proves $\kappa'_2(h) \ne 1$ and hence **$\alpha_*(\chi) < 1$ strictly** (with optimal $t_* < 2$ for even $h$ and $t_* > 2$ for odd $h$; e.g. $\alpha_* \approx 0.9421$ at $h = 2$, $0.9979$ at $h = 3$).

**Theorem G2.4B (Single-Class CRT and Arbitrary-Union Zero-Block Covering Barriers for Odd-Order Characters; Paper proof + Exact certificate).**
Let $\chi \bmod q$ have odd order $h \ge 3$, so every prime $p \in \mathcal{P}' := \{p \nmid q : \chi(p) \ne 1\}$ has order $d_p \ge d_{\min} \ge 3$ and forces $c_\chi(n) = 0$ only when $v_p(n) \equiv d_p - 1 \pmod{d_p}$ (in particular $p^{d_p - 1} \mid n$, hence $p^2 \mid n$). Let $P(2) = \sum_{p \text{ prime}} p^{-2} \in [0.452238, 0.452338] < 1/2$ (`C6`), and let $P_{\mathcal{P}'}(2) = \sum_{p \in \mathcal{P}'} p^{-2} \le P(2)$ (for cubic mod 7, $P_{\mathcal{P}'}(2) \in [0.422597, 0.422697]$). For any integer $L \ge 1$, put
```math
m(L) := L - \sum_{\substack{p \in \mathcal{P}' \\ p \le \sqrt{L}}} \left(\left\lfloor \frac{L}{p^{d_p - 1}} \right\rfloor + 1\right) \ge \bigl(1 - P_{\mathcal{P}'}(2) - o(1)\bigr) L,
```
so there exists an explicit threshold $L_0(\chi)$ (e.g. $L_0 = 20$ for cubic mod $7$; at $L = 10$ the lower bound gives $m(10) = 5 = L/2$) such that $m(L) > \frac{1}{2} L$ for all $L \ge L_0(\chi)$. Then:
1. **Single CRT congruence class (allowing arbitrary prime reuse):** For **any** finite system of CRT congruences modulo $Q = \operatorname{lcm}_{1 \le j \le L} p_j^{e_j + 1}$ enforcing $v_{p_j}(m_0 + j) \equiv d_{p_j} - 1 \pmod{d_{p_j}}$ for all $j \in \{1, \dots, L\}$, at least $m(L)$ offsets require pairwise **distinct** primes $p > \sqrt{L}$ dividing $Q$ to power at least $d_{\min} \ge 3$. Hence
   ```math
   \log Q \ge d_{\min} \bigl(1 - P_{\mathcal{P}'}(2) - o(1)\bigr) L \log L, \qquad \frac{1}{Q} \le \exp\Bigl(-d_{\min}\bigl(1 - P_{\mathcal{P}'}(2) - o(1)\bigr) L \log L\Bigr).
   ```
2. **Union bound over ALL zero blocks (blocking arbitrary unions of CRT classes and squarefull/Selberg sieves):** Let $\mathcal{Z}_\chi(L) := \{n \in \mathbb{N} : c_\chi(n + 1) = \dots = c_\chi(n + L) = 0\}$. For every $L \ge L_0(\chi)$, the upper natural density of $\mathcal{Z}_\chi(L)$ satisfies
   ```math
   \overline{d}\bigl(\mathcal{Z}_\chi(L)\bigr) := \limsup_{X \to \infty} \frac{|\mathcal{Z}_\chi(L) \cap [1, X]|}{X} \le \binom{L}{m(L)} \left(\sum_{\substack{p \in \mathcal{P}' \\ p > \sqrt{L}}} \frac{1}{p^2}\right)^{m(L)} \le \exp\Bigl(-\frac{1 - P_{\mathcal{P}'}(2) - o(1)}{2}\, L \log L\Bigr)
   ```
   (exponent $\frac{1 - P_{\mathcal{P}'}(2)}{2} > 0.288$ for cubic mod $7$, and universally $\frac{1 - P(2)}{2} > 0.273$ — smaller than the single-class exponent $d_{\min}(1 - P_{\mathcal{P}'}(2))$ by a factor $2 d_{\min} \ge 6$, reflecting the sum over all choices of large primes). Moreover, for any fixed $c > 0$ and $L \ge c\log_b\log N$, the same bound $|\mathcal{Z}_\chi(L) \cap (N, N + H]| \le H\exp(-\frac{1 - P_{\mathcal{P}'}(2) - o(1)}{2} L\log L)$ holds on **every** long window with $H \ge N^a$ ($a > 1/2$, in particular on prefixes $[1, N]$) and on **almost all** windows $(N, N + H]$ ($N \in [X, 2X]$, any $H \ge 1$).

Consequently, whenever $L \ge c\log_b\log N$ (for any fixed $c > 0$), **no** method relying on detecting zero blocks of length $L$ — whether a single CRT congruence system, an arbitrary union of CRT classes, or any Paper-VI-style Selberg / squarefull sieve counting elements of $\mathcal{Z}_\chi(L)$ — can reach count $H/(\log N)^C$ or positive lower density $c' H$.

---

## 3. Complete Proofs

### 3.1 Proofs of Theorems G2.1A and G2.1B ($H = \sqrt{N}(\log N)^C$)

*Proof of Theorem G2.1A.* We modify Paper VI's `prop:planting` (`papers/06-multiplicative-lambert/paper.tex:775-892`) at three points: the small-factor cutoff $M$, the far-tail cutoff $J$, and the bound on $\sum_{p \in \mathcal{P}_m} c(bp + h)$ in (I3).

**Step 1 (Parameters and prime supply under `GRH(q_0)`).**
Fix $C > 2$, pick $\varepsilon = \min(1/10, C - 2) > 0$, and put $B := 2(C - 2) - \varepsilon > 0$ and $M := (\log N)^B$. Let $\mathcal{M}(M)$ be the set of squarefree integers $m \le M$ whose prime factors lie in $S' := S \setminus \{p_0\}$ and with $\omega(m) \le 2\log\log N$. Put
```math
C_J := \max\left(4,\ \left\lceil \frac{B + 2}{\log 2} \right\rceil\right), \qquad J := \lceil C_J \log\log N \rceil, \qquad z_0 := (\log N)^2.
```
For each $m \in \mathcal{M}(M)$, set $b = p_0^{2u} m \le p_0^{2u}(\log N)^B$, $j_0 = k + 2 + \omega(m) \le J$, $X = (N + j_0 - 1)/b \in [N/(2b), 2N/b]$, $Y = H/b \ge \sqrt{N}(\log N)^C / b$, and $\mathcal{P}_m = \{p \in (X, X+Y] : p \equiv a_0 \pmod{q_0}\}$. By Corollary A.2 of `GF-48` (Conditional on `GRH(q_0)`),
```math
\theta(X+Y; q_0, a_0) - \theta(X; q_0, a_0) \ge \frac{Y}{\varphi(q_0)} - C_2 \sqrt{X}\log^2(2 q_0 X) \ge \frac{\sqrt{N}}{b}\left(\frac{(\log N)^C}{\varphi(q_0)} - C_2\sqrt{2 p_0^{2u}}(\log N)^{B/2}\log^2(4 q_0 N)\right).
```
Since $B/2 + 2 = C - \varepsilon/2 < C$ (verified across 360 grid values in `C2`), the error is at most $\frac{1}{4} Y/\varphi(q_0)$ for $N \ge N_0(w, C)$, and dividing by $\log(2X) \le \frac{3}{2}\log N$ yields $|\mathcal{P}_m| \ge \frac{Y}{2\varphi(q_0)\log N}$ uniformly in $m \in \mathcal{M}(M)$ and $\sqrt{N}(\log N)^C \le H \le N$.

**Step 2 (Small-factor sum).**
Repeat Paper VI `lem:small` (`paper.tex:654-671`) with $M = (\log N)^B$ in place of $N^\theta$ and $z_1 = M^{1/8}$: $\Pi := \sum_{m \in \mathcal{R}} 1/m = \prod_{p \in S',\, p \le z_1}(1 + 1/p) \asymp_B (\log\log N)^\delta$; the truncation tail $m > M$ is at most $\Pi(\frac{1}{8} + O(1/\log M)) \le \frac{1}{4}\Pi$ by Mertens; and Rankin's trick gives $\sum_{m \in \mathcal{R},\, \omega(m) > 2\log\log N} 1/m \ll (\log N)^{-2\log 2}(\log\log N)^{2\delta} = o(\Pi)$ since $2\log 2 > 1$ (`C2`). Hence $\sum_{m \in \mathcal{M}(M)} 1/m \ge \frac{1}{2}\Pi \asymp_B (\log\log N)^\delta$.

**Step 3 (Nearby vanishing (I2)).**
Since $Y \ge \sqrt{N}(\log N)^{C - B} \gg_w N^{1/2 - o(1)}$, we have $p > X > b$, $p \nmid m$, $p \ne p_0$, and for `lem:selberg` with $z = Y^{1/4}$ and $w_{\mathrm{sieve}} = z^{1/8} = Y^{1/32} > z_0 = (\log N)^2$, every shift $h = j - j_0$ ($j \in [1 - R, J] \setminus \{j_0\}$) satisfies $1 \le |h| \le (C_J + C_R + 1)\log\log N < z_0$. Paper VI's sieve bound applies verbatim, yielding at most $O_{C, C_R}(Y(\log\log N)^{1+\kappa}(\log N)^{-1-\kappa}) = o(Y/\log N)$ failures of (I2).

**Step 4 (Far tail (I3) via elementary Lemma E.2 — bypassing Brun–Titchmarsh).**
For $J < j \le N$ put $h = j - j_0 \ge 1$. As $p$ runs over $\mathcal{P}_m \subset (X, X + Y]$, $n' = bp + h$ runs injectively over integers in $(bX + h, bX + H + h]$ in the residue class $h \bmod b$, with right endpoint $X_1 = bX + H + h < 3N$. By **Lemma E.2** of `GF-48` (`notes/phase25/grh-lambert-windows.md` §2.5, elementary with zero analytic inputs):
```math
\sum_{p \in \mathcal{P}_m} c(bp + h) \le \sum_{\substack{bX + h < n' \le bX + H + h \\ n' \equiv h \ (b)}} \tau(n') \le 2\sqrt{3N} + \frac{2H}{b}\tau(\gcd(h, b))\Bigl(1 + \frac{1}{2}\log 3N\Bigr) \le 2\sqrt{3N} + 2 Y h (1 + \log 3N).
```
For $j > N$, $|\mathcal{P}_m| \le Y + 1$ and $c(bp + h) \le 2N + j$. Using the exact geometric identity $\sum_{j > J} j 2^{-j} = (J + 2) 2^{-J}$ (`C2`),
```math
\sum_{p \in \mathcal{P}_m} E(bp - j_0) \le \bigl(2\sqrt{3N} + 2 Y (1 + \log 3N)\bigr)(J + 2) 2^{-J} + O(Y N 2^{-N}).
```
By Markov's inequality, (I3) ($E(bp - j_0) < 2^{-k-2}$) fails for at most $O_k((\sqrt{N} + Y\log N) J 2^{-J}) + O(YN 2^{-N})$ primes of $\mathcal{P}_m$. Since $2^{-J} \le (\log N)^{-C_J \log 2}$:
- $Y (\log N) J 2^{-J} \ll Y (\log\log N) (\log N)^{1 - C_J \log 2} = o(Y/\log N)$ because $C_J \log 2 \ge 4\log 2 > 2$ (`C2`);
- $\sqrt{N} J 2^{-J} = Y \cdot \frac{b}{(\log N)^C} J 2^{-J} \ll_w Y (\log\log N) (\log N)^{B - C - C_J \log 2} = o(Y/\log N)$: this requires only $B - C - C_J \log 2 < -1$ (i.e. $B + 1 - C - C_J \log 2 < 0$), which holds for **every $C > -1$** since $C_J \log 2 \ge B + 2$ (confirming that the Lemma E.2 far tail is never the bottleneck; `C2` checks both the necessary `< 0` bound across $C > -1$ and the stronger `< -1` margin for $C > 2$).

**Step 5 (Assembly, critical $C = 2$, and interpolation).**
Subtracting (I2) and (I3) failures leaves $\ge \frac{Y}{4\varphi(q_0)\log N}$ $R$-isolated primes per $m \in \mathcal{M}(M)$. Injectivity of $(m, p) \mapsto bp - j_0$ (`paper.tex:884-886`) and Step 2 give $\gg_{w, C} H(\log\log N)^\delta/\log N$ $R$-isolated starts in $[N, N+H)$. The word bounds follow from `lem:isolated` and Paper VI `prop:upper` (unconditional for all $H \ge N^{1/2}$). The window discrepancy lower bound follows identically to `GF-48` Proposition C using `Phase17DiscrepancyBounds.one_sub_discrepancy_ge_of_separated_mass` with $R = \lfloor \frac{\kappa}{2}\log_2\log N \rfloor$, giving $\Delta = R|\mathcal{G}|/H \gg_C (\log\log N)^{1+\delta}/\log N$. For Part 2 ($C = 2$), set $m = 1$ ($b = p_0^{2u}$ fixed, $B = 0$); Step 1 holds whenever $K/\varphi(q_0) > 4 C_2 \sqrt{2 p_0^{2u}}$, i.e. $K > 4\sqrt{2}\, C_2 \varphi(q_0) p_0^u$. For Part 3 ($\alpha \in (0, 1)$), set $M = \exp(\frac{1}{2}(\log N)^\alpha)$ and $J = \lceil 10\log\log N \rceil$: on $H \ge \sqrt{N}\exp(\frac{1}{2}(\log N)^\alpha)(\log N)^3$, every $m \in \mathcal{M}(M)$ satisfies $b \le p_0^{2u} M$, so the GRH error-to-main-term ratio in Step 1 is $\ll_w \exp(-\frac{1}{4}(\log N)^\alpha)/\log N \to 0$, Step 2 gives $\sum_{m \in \mathcal{M}(M)} 1/m \asymp_\alpha (\log M)^\delta = 2^{-\delta}(\log N)^{\alpha\delta}$ (since $2\alpha\delta - 2\log 2 < \alpha\delta$ for all $\alpha, \delta \in (0, 1)$), Step 3 applies verbatim because $Y = H/b \gg_w \sqrt{N}(\log N)^3$, and in Step 4 we have $\sqrt{N}/Y = b/(H/\sqrt{N}) \le p_0^{2u}(\log N)^{-3} \ll_w 1$, so $J = \lceil 10\log\log N \rceil$ kills both terms of (I3) since $10\log 2 > 2$. Summing over $m \in \mathcal{M}(M)$ yields $\#_w(N, H) \gg_{w, \alpha} H(\log N)^{\alpha\delta - 1}$. ∎

*Proof of Theorem G2.1B.*
1. In `GF-22` (`notes/phase25/grh-lambert-windows.md` §2.5), $q' = q\prod_{j \in J} p_j^d$ with $s = |J| = W' + f + L$ and $L = (\alpha/\log b)\log\log N + O_w(1)$ ($\alpha = 2$ via Lemma E.2, or $\alpha = 1$ via Theorem G2.4A). By PNT mod $q$, $p_j \sim \varphi(q) j\log j$, so $\log \varphi(q') = \log q' + O_q(\log\log\log N) = (\frac{\alpha d}{\log b} + o(1))\log\log N \cdot \log\log\log N$. For any fixed $C > 0$, $\log((\log N)^C) = C\log\log N = o(\log \varphi(q'))$, so $\varphi(q')/(\log N)^C \to \infty$. At $H = \sqrt{N}(\log N)^C$, the main term $Y/\varphi(q') \asymp_w \sqrt{N}(\log N)^C/\varphi(q')$ of Step 5′ is $o(\sqrt{N}\log^2 N)$ (swallowed by Theorem A's error $O(\sqrt{U}\log^2(2q'U))$), and the Lemma E.2 additive Markov term $\asymp_w \sqrt{N}/(\log N)^\alpha$ exceeds $Y/(\varphi(q')\log N) \asymp_w \sqrt{N}(\log N)^{C-1}/\varphi(q')$ by $\varphi(q')/(\log N)^{C+\alpha-1} \to \infty$.
2. Conversely, take $H \ge \sqrt{N}\exp(C_0 \log\log N \cdot \log\log\log N)$ with $C_0 > \alpha d/\log b$. Then $Y/\varphi(q') = (H/A)/\varphi(q') \ge \sqrt{N}\exp((C_0 - \alpha d/\log b - o(1))\log\log N \cdot \log\log\log N) \gg \sqrt{U}\log^2(2q'U)$, so Step 5′ yields $|\mathcal{U}| \ge Y/(2\varphi(q')\log 2U)$ under Dirichlet GRH (`C3` confirms Step 5′ dominates Step 6′ by $(\log N)^3$). With $\alpha = 1$ (Theorem G2.4A, where $H \ge \sqrt{N}$ satisfies Shiu's hypothesis with $\sigma = 1/2$ and $q' = N^{o(1)} < H^{1/2}$), Steps 6′–7′ hold verbatim and yield $\#_w(N, H) \ge Y/(4\varphi(q')\log 2U) \ge H\exp(-C_w \log\log N \cdot \log\log\log N)$. ∎

---

### 3.2 Proofs of Theorems G2.2A, G2.2A′, G2.2C, G2.2D, and G2.2B (Almost-All Windows & Unconditional `GF-22`)

#### Lemma 3.1 (Selberg Mean-Square Prime Variance in Progressions under `GRH(q)`).
Assume **GRH($q$)**, let $\gcd(a_0, q) = 1$, $T \ge 4$, $2 \le Y \le T$, and $\delta := Y / (6T) \in (0, 1/6]$. Put $\widetilde{E}_\psi(t, \delta; q, a_0) := \psi(t(1+\delta); q, a_0) - \psi(t; q, a_0) - \delta t/\varphi(q)$. Then
```math
\int_T^{3T} \bigl|\widetilde{E}_\psi(t, \delta; q, a_0)\bigr|^2 dt \ll T Y \log^2(q T) + T \log^4(q T),
```
with an absolute implied constant independent of $q, a_0, T, Y$. In particular, for $Y \ge \log^2(q T)$, the bound is $\ll T Y \log^2(q T)$.

*Proof.* By orthogonality and primitive reduction ($\chi \bmod q$ induced by $\chi^* \bmod q^*$, error $O(\omega(q)\log 4T) = O(\log q \log T)$) and Cauchy–Schwarz across $\chi \bmod q$,
```math
\int_T^{3T} \bigl|\widetilde{E}_\psi(t, \delta; q, a_0)\bigr|^2 dt \le \frac{2}{\varphi(q)} \sum_{\chi \bmod q} \int_T^{3T} \bigl|\widetilde{E}_\psi(t, \delta; \chi^*)\bigr|^2 dt + O\bigl(T \log^2(q) \log^2(4T)\bigr).
```
For each primitive $\chi^* \bmod q^*$, the truncated explicit formula (Davenport Chs. 17 & 19) with truncation height $U = T$ gives
```math
\widetilde{E}_\psi(t, \delta; \chi^*) = -\sum_{|\gamma| < T} c(\rho) t^\rho + O\bigl(\log^2(q^* T)\bigr), \qquad c(\rho) := \frac{(1+\delta)^\rho - 1}{\rho}.
```
Under GRH($q$), $\rho = \frac{1}{2} + i\gamma$, so $|(1+\delta)^\rho - 1| = |\rho \int_1^{1+\delta} u^{\rho-1} du| \le |\rho|\delta$ and $|(1+\delta)^\rho - 1| \le \sqrt{1+\delta} + 1 < 3$, giving $|c(\rho)| \le \min(\delta, 3/|\rho|)$. Writing $t^\rho = t^{1/2} e^{i\gamma \log t}$ and substituting $u = \log t$ (noting $t \le 3T$ so $t \, du = dt$):
```math
\int_T^{3T} \left|\sum_{|\gamma| < T} c(\rho) t^\rho\right|^2 dt \le 9 T^2 \int_{\log T}^{\log 3T} \left|\sum_{|\gamma| < T} c(\rho) e^{i\gamma u}\right|^2 du \ll T^2 \sum_{|\gamma_1|, |\gamma_2| < T} \frac{|c(\rho_1)| |c(\rho_2)|}{1 + (\gamma_1 - \gamma_2)^2},
```
bounding $\mathbf{1}_{[\log T, \log 3T]}$ by a majorant $w \ge 0$ with $|\widehat{w}(\xi)| \ll (1 + \xi^2)^{-1}$. By AM–GM ($|c(\rho_1)c(\rho_2)| \le \frac{1}{2}(|c(\rho_1)|^2 + |c(\rho_2)|^2)$) and zero counting (X2) ($\sum_{\gamma_2} (1 + (\gamma_1 - \gamma_2)^2)^{-1} \ll \log(q^*(|\gamma_1| + 2))$):
```math
\sum_{|\gamma| < T} |c(\rho)|^2 \log\bigl(q^*(|\gamma| + 2)\bigr) \ll \delta^2 \sum_{|\gamma| \le 1/\delta} \log\bigl(q^*(|\gamma| + 2)\bigr) + \sum_{1/\delta < |\gamma| < T} \frac{\log\bigl(q^*(|\gamma| + 2)\bigr)}{\gamma^2} \ll \delta \log^2(q^* T).
```
Multiplying by $T^2$ gives $\ll T^2 \delta \log^2(q T) \asymp T Y \log^2(q T)$, while the $O(\log^2(q^* T))$ truncation term squared and integrated over $[T, 3T]$ contributes $O(T \log^4(q T))$. Averaging over $\chi \bmod q$ preserves the uniform bound. ∎

#### Lemma 3.2 (Unconditional Mean-Square Prime Variance via Log-Free Zero Density + Vinogradov–Korobov + Landau–Page).
Let $q' \ge 3$ satisfy $\log q' \le (\log T)^{1/2}$ and assume that no $\chi \bmod q'$ has a zero in $\sigma \ge 1 - c_0/\log(12 q')$, $|t| \le 10$ (guaranteed by two-family Landau–Page avoidance). Let $A = 12/5$ via the **log-free** zero-density estimate of **Thorner–Zaman (2024, *Math. Z.* **306**, Paper No. 54, `arXiv:2108.10878v2`, Theorem 2.1, eq. (2.1))** `[R]` (combining Huxley 1975 away from $\sigma = 1$ with **Jutila 1977, *Math. Scand.* **41**, Theorem 1, eq. (1.7)** `[R]` near $\sigma = 1$):
```math
N_{q'}(\sigma, U) := \sum_{\chi \bmod q'} N(\sigma, U, \chi) \ll_{\varepsilon} (q' U)^{(\frac{12}{5} + \varepsilon)(1-\sigma)} \qquad (0 \le \sigma \le 1,\ \varepsilon > 0).
```
Fix $a > 1 - 2/A = 1/6$ and let $Y = T^a$, $\delta = Y/(6T)$. Then for $T \ge T_0(a)$,
```math
\frac{1}{T (Y / \varphi(q'))^2} \int_T^{3T} \bigl|\widetilde{E}_\psi(t, \delta; q', a_0)\bigr|^2 dt \ll_a \varphi(q') \exp\bigl(-c'(a)(\log T)^{1/3}(\log\log T)^{-1/3}\bigr) + \frac{\varphi(q')^2 \log^2(q' T)}{Y}.
```
*(More generally, the same bound holds for any $a > 1 - 2/A$ whenever a zero-density estimate $N_{q'}(\sigma, U) \ll_{\varepsilon'} (q' U)^{A(1-\sigma) + \varepsilon'}$ with $A \ge 2$ is available on $\sigma \in [\frac{1}{2}, \frac{4}{5}]$, by splitting at $\sigma_0 = \frac{4}{5}$ and applying Jutila 1977 Theorem 1 on $[\frac{4}{5}, 1]$.)*

*Proof.* Set $\varepsilon_0 := \frac{1}{2}(a - (1 - 2/A)) > 0$ (for $A = 12/5$: $\varepsilon_0 = \frac{1}{2}(a - 1/6)$) and truncation height $U := \delta^{-1} T^{\varepsilon_0} = 6 T^{1 - a + \varepsilon_0} \le T$ (for large $T$). By orthogonality and Cauchy–Schwarz over $\chi \bmod q'$,
```math
\frac{1}{T(Y/\varphi(q'))^2} \int_T^{3T} \bigl|\widetilde{E}_\psi(t, \delta; q', a_0)\bigr|^2 dt \ll \frac{\varphi(q')}{T Y^2} \sum_{\chi \bmod q'} \int_T^{3T} \bigl|\widetilde{E}_\psi(t, \delta; \chi^*)\bigr|^2 dt + \frac{\varphi(q')^2 \log^2 q' \log^2 T}{Y^2}.
```
In the truncated explicit formula at height $U$, the truncation error $O(T \log^2(q' T)/U)$ contributes $\ll \varphi(q')^2 \frac{T^2 \log^4(q' T)}{Y^2 U^2} \ll \varphi(q')^2 T^{-2\varepsilon_0} \log^4(q' T)$; since $\log q' \le (\log T)^{1/2}$, both this truncation term and the imprimitive-reduction term $O(\varphi(q')^2 \log^2 q' \log^2 T / Y^2)$ are strictly absorbed into the first displayed term $\varphi(q')\exp(-c'(a)(\log T)^{1/3}(\log\log T)^{-1/3})$ for large $T$. For the zero sum, Gallagher's mean-value step with $c(\rho) \ll \min(\delta, |\gamma|^{-1})$ (valid uniformly for $0 < \beta < 1$) and AM–GM on $T^{\beta_1 + \beta_2} \le \frac{1}{2}(T^{2\beta_1} + T^{2\beta_2})$ yields:
```math
\frac{\varphi(q')}{T Y^2} \sum_{\chi \bmod q'} \int_T^{3T} \left|\sum_{|\gamma| < U} c(\rho) t^\rho\right|^2 dt \ll \varphi(q') \log(q' T) \sum_{\chi \bmod q'} \sum_{|\gamma| < U} \min\left(1, \frac{1}{\delta^2 |\gamma|^2}\right) T^{2(\beta - 1)}.
```
Split into $\beta \le 1/2$ and $\beta > 1/2$:
- For $\beta \le 1/2$: $T^{2(\beta - 1)} \le T^{-1}$, and each character has $\ll \delta^{-1}\log(q' T)$ weighted zeros, contributing $\ll \varphi(q')^2 \frac{\log^2(q' T)}{\delta T} \asymp \frac{\varphi(q')^2 \log^2(q' T)}{Y}$.
- For $\beta > 1/2$: combine the $|t| \le 10$ hypothesis ($c_0/\log(12 q') \gg (\log T)^{-1/2}$) with the uniform Vinogradov–Korobov zero-free region for $10 \le |t| \le U$ — only the classical non-explicit shape $\sigma \ge 1 - c'/(\log q' + (\log|t|)^{2/3}(\log\log|t|)^{1/3})$ (Montgomery 1971 p. 176 / 1994 Ch. 9; proved cleanly in Khale `arXiv:2210.06457v1` eq. (1.4) & Appendix B `[R]`) is needed, while **Khale (2024, Theorem 1.1)** `[R]` supplies the explicit constants $10.5 \log q' + 61.5(\log|t|)^{2/3}(\log\log|t|)^{1/3}$. Since $\log q' \le (\log T)^{1/2}$, for large $T$ every zero with $|\gamma| < U$ satisfies $\beta \le 1 - \eta(T)$ with $\eta(T) := (62 (\log T)^{2/3}(\log\log T)^{1/3})^{-1}$. Dropping $\min(1, (\delta|\gamma|)^{-2}) \le 1$ and integrating by parts (using $N_{q'}(1 - \eta(T), U) = 0$):
  ```math
  \sum_{\chi \bmod q'} \sum_{\substack{|\gamma| < U \\ \frac{1}{2} < \beta \le 1 - \eta(T)}} T^{-2(1-\beta)} = T^{-1} N_{q'}\!\left(\tfrac{1}{2}, U\right) + 2(\log T) \int_{1/2}^{1 - \eta(T)} T^{-2(1-\sigma)} N_{q'}(\sigma, U)\, d\sigma.
  ```
  Put $\gamma_1 := 2 - A(1 - a + \varepsilon_0) = \frac{A}{2}(a - (1 - 2/A)) > 0$ (for $A = 12/5$: $\gamma_1 = \frac{6}{5}(a - 1/6) > 0$). We bound the integral cleanly in two ways:
  1. *Direct full-strip log-free route ($A = 12/5$, Thorner–Zaman 2024 Theorem 2.1 `[R]`):* Set $\varepsilon_1 := \gamma_1/2$. Since $1 - a + \varepsilon_0 < 1$, $(\frac{12}{5} + \varepsilon_1)(1 - a + \varepsilon_0) < 2 - \gamma_1/2$. As $q' = T^{o(1)}$, for large $T$ we have $(q' U)^{\frac{12}{5} + \varepsilon_1}/T^2 \le T^{-\gamma_1/4}$, so both the boundary term at $\sigma = 1/2$ ($\ll T^{-\gamma_1/8}$) and the integral are $\ll_a (\log T) \sup_{\frac{1}{2} \le \sigma \le 1-\eta(T)} T^{-\frac{\gamma_1}{4}(1-\sigma)} = (\log T)\, T^{-\frac{\gamma_1}{4}\eta(T)} = \exp(-c''(a)(\log T)^{1/3}(\log\log T)^{-1/3})$.
  2. *Two-regime $\sigma$-split at $\sigma_0 = \frac{4}{5}$ ($c_0 := 1 - \sigma_0 = \frac{1}{5}$, handling ANY $\varepsilon$-form bound $(q' U)^{A(1-\sigma) + \varepsilon'}$ — both Huxley $A = 12/5$ and the Chen–Gupta–Li `2507.08296v2` `[R]` $A = 7/3$ addendum):*
     - On $\sigma \in [\frac{1}{2}, \frac{4}{5}]$ ($1 - \sigma \ge \frac{1}{5}$): take $\varepsilon' := \gamma_1/20 > 0$. For large $T$, $(q' U)^A / T^2 \le T^{-\frac{3}{4}\gamma_1}$ and $(q' U)^{\varepsilon'} \le T^{\frac{\gamma_1}{20}}$, so uniformly on $[\frac{1}{2}, \frac{4}{5}]$ (and at the boundary $\sigma = 1/2$), $T^{-2(1-\sigma)} N_{q'}(\sigma, U) \ll_{\varepsilon'} T^{-\frac{3}{4}\gamma_1 \cdot \frac{1}{5} + \frac{\gamma_1}{20}} = T^{-\frac{\gamma_1}{10}}$ (`C4`). Here the extra $(q' U)^{\varepsilon'}$ factor is strictly absorbed by the fixed power saving at $1 - \sigma \ge c_0 = \frac{1}{5}$.
     - On $\sigma \in [\frac{4}{5}, 1 - \eta(T)]$: apply **Jutila (1977, *Math. Scand.* **41**, Theorem 1, eq. (1.7))** `[R]` — **log-free**, zero $\varepsilon$-loss outside $(1-\sigma)$: $N_{q'}(\sigma, U) \ll_{\varepsilon''} (q' U)^{(2 + \varepsilon'')(1-\sigma)}$. Here $2 - 2(1 - a + \varepsilon_0) = a + (1 - 2/A) > 2(1 - 2/A) \ge \frac{2}{7} > 0$, so choosing $\varepsilon'' = \frac{1}{10}$ gives $(2 + \varepsilon'')(1 - a + \varepsilon_0) < 2 - \frac{1}{2}(a + 1 - 2/A)$ (`C4`). Hence $(q' U)^{2 + \varepsilon''}/T^2 \le T^{-\frac{1}{4}(a + 1 - 2/A)}$, and the supremum at $\sigma = 1 - \eta(T)$ is $T^{-\frac{1}{4}(a + 1 - 2/A)\eta(T)} = \exp(-c''(a)(\log T)^{1/3}(\log\log T)^{-1/3})$.

  Multiplying by $\varphi(q')\log(q' T)$ absorbs all $\log T$ factors and completes the proof. ∎

#### Lemma 3.3 (Global Averaging of Paper VI Bad Planted Pairs — Unconditional for ALL $H \ge 1$).
Under `(H1)`–`(H4)`, fix $w$, $C_R \ge 0$, $0 \le R \le C_R \log\log X$, and any $M \le X^{1/4}$, $1 \le H \le X$. For each $m \in \mathcal{M}(M)$ ($b = p_0^{2u} m$) and $N \in [X, 2X]$, let $\mathcal{P}_m(N) = \{p \equiv a_0 \pmod{q_0} : N \le bp - j_0 < N + H\}$ and let $\mathcal{B}_m \subset (X/b, 3X/b]$ be the set of primes $p \equiv a_0 \pmod{q_0}$ for which (I2) or (I3) fails. Set $B_{\mathrm{tot}}(N) := \sum_{m \in \mathcal{M}(M)} |\mathcal{B}_m \cap \mathcal{P}_m(N)|$. Then **unconditionally**,
```math
\frac{1}{X} \sum_{X \le N < 2X} B_{\mathrm{tot}}(N) \ll_{w, C_R} H \frac{(\log\log X)^{1+\kappa}}{(\log X)^{1+\kappa}} \sum_{m \in \mathcal{M}(M)} \frac{1}{m}.
```

*Proof.* On the full dyadic interval $(X/b, 3X/b]$ of length $2X/b \gg_w X^{3/4}$, Paper VI's unconditional (I2) Selberg sieve and (I3) Brun–Titchmarsh far-tail estimates (`paper.tex:816-879`) apply directly with $Y = 2X/b \gg X^{3/4}$, giving $|\mathcal{B}_m| \ll_{w, C_R} \frac{X}{b} \frac{(\log\log X)^{1+\kappa}}{(\log X)^{1+\kappa}}$. For each $(m, p)$ with $p \in \mathcal{B}_m$, the condition $N \le bp - j_0 < N + H$ holds for at most $H$ integers $N \in [X, 2X]$. Interchanging the sums over $N$ and $(m, p)$ gives $\sum_{X \le N < 2X} B_{\mathrm{tot}}(N) \le H \sum_{m \in \mathcal{M}(M)} |\mathcal{B}_m|$, and dividing by $X$ yields the claim. ∎

*Proof of Theorem G2.2A (Unconditional Paper VI almost-all windows for $1/6 < a \le 1$).*
Set $\theta := \min(1/4, (a - 1/6)/2) > 0$ and $M := X^\theta$. For each $m \in \mathcal{M}(M)$ ($b = p_0^{2u} m$), put $T_m = X/b$ and $Y_m = H/b$. Then $Y_m \ge X^{a - \theta}/p_0^{2u} \ge T_m^{\vartheta_m}$ with $\vartheta_m \ge \frac{a-\theta}{1-\theta} > a - \theta \ge \frac{a + 1/6}{2} > 1/6$ (`C4`). For each $N \in [X, 2X]$ put $t_N = (N + j_0 - 1)/b$: for every $t \in [t_N, t_N + 1/b)$ we have $(t, t + \delta_m t] \subset (t_N, t_N + Y_m]$ where $\delta_m = (Y_m - 1/b)/(6 T_m)$ satisfies $\delta_m t \ge Y_m/7$. By Lemma 3.2 at the fixed modulus $q' = q_0$ (no Siegel zero for fixed $q_0$ and large $X$),
```math
\frac{1}{X} \sum_{X \le N < 2X} \inf_{t \in [t_N, t_N + 1/b)} \bigl|\widetilde{E}_\psi(t, \delta_m; q_0, a_0)\bigr|^2 \le \frac{b}{X} \int_{T_m}^{3T_m} \bigl|\widetilde{E}_\psi(t, \delta_m; q_0, a_0)\bigr|^2 dt \ll_{q_0, a} Y_m^2 \exp\bigl(-c'(a)(\log X)^{1/3}(\log\log X)^{-1/3}\bigr).
```
Let $\Delta_m^{\mathrm{prime}}(N) := \max\bigl(0,\ \frac{Y_m}{14\varphi(q_0)\log X} - |\mathcal{P}_m(N)| - \Delta_m^{\mathrm{pp}}(N)\bigr)$, where $\Delta_m^{\mathrm{pp}}(N)$ counts prime powers $p^e$ ($e \ge 2$) in $(t_N, t_N + Y_m]$. Taking $L^1$ via Cauchy–Schwarz and summing over $m \in \mathcal{M}(M)$ gives
```math
\frac{1}{X} \sum_{X \le N < 2X} \sum_{m \in \mathcal{M}(M)} \Delta_m^{\mathrm{prime}}(N) \ll_{q_0, a} \frac{H}{\log X} \exp\bigl(-\tfrac{1}{2} c'(a)(\log X)^{1/3}(\log\log X)^{-1/3}\bigr) \sum_{m \in \mathcal{M}(M)} \frac{1}{m}.
```
The prime-power contribution satisfies $\frac{1}{X} \sum_N \sum_m \Delta_m^{\mathrm{pp}}(N) \le \frac{H}{X} \sum_{m \le M} O(\sqrt{X/b}) \ll H \sqrt{M/X} \le H X^{-3/8} = o(H/(\log X)^\kappa)$. Combining with Lemma 3.3 and applying Markov's inequality over $N \in [X, 2X]$, for all but $O(X (\log\log X)^{1+\kappa}/(\log X)^\kappa) = o(X)$ starts $N \in [X, 2X]$, the number of $R$-isolated planted pairs is
```math
\sum_{m \in \mathcal{M}(M)} |\mathcal{P}_m(N)| - B_{\mathrm{tot}}(N) \ge \frac{H}{28 p_0^{2u} \varphi(q_0)\log X} \sum_{m \in \mathcal{M}(M)} \frac{1}{m} \gg_{w, a} \frac{H}{(\log X)^\kappa}.
```
Injectivity of $(m, p) \mapsto bp - j_0$, Paper VI `prop:upper` (unconditional for all $a > 0$), and the two kernel-verified Lean inequalities (`Phase17DiscrepancyBounds.one_sub_discrepancy_le_one_bits`, `one_sub_discrepancy_ge_of_separated_mass`) yield (1)–(3) for almost all $N \in [X, 2X]$. ∎

*Proof of Theorem G2.2A′ (Paper VI almost-all windows under `GRH(q_0)`).*
1. For fixed $\theta \in (0, 1]$ and $X^\theta \le H \le X$, set $\mu := \min(1/4, \theta/2)$ and $M := X^\mu$. Then $Y_m = H/b \gg_w X^{\theta - \mu} \ge X^{\theta/2} \gg \log^2(q_0 X)$ for every $m \in \mathcal{M}(M)$ (`C4`). By Lemma 3.1 (Selberg–GRH) at $q = q_0$ and $T_m = X/b$:
```math
\frac{1}{X} \sum_{X \le N < 2X} \bigl(\Delta_m^{\mathrm{prime}}(N)\bigr)^2 \le \frac{b}{X (\log X)^2} \int_{T_m}^{3T_m} \bigl|\widetilde{E}_\psi(t, \delta_m; q_0, a_0)\bigr|^2 dt \ll_{q_0} \frac{H}{b}.
```
Taking $L^1$ via Cauchy–Schwarz and summing over $m \in \mathcal{M}(M)$ yields
```math
\frac{1}{X} \sum_{X \le N < 2X} \sum_{m \in \mathcal{M}(M)} \Delta_m^{\mathrm{prime}}(N) \ll_{q_0, w} \sqrt{H} \sum_{m \le M} \frac{1}{\sqrt{m}} \ll \sqrt{H M} \le H X^{-(\theta - \mu)/2} = o\left(\frac{H}{(\log X)^\kappa}\right),
```
saving a full power $X^{(\theta-\mu)/2} \ge X^{\min(\theta/4, \theta/2 - 1/8)}$ (`C4`)! Combined with the prime-power bound $O(H X^{-3/8})$ and Lemma 3.3, Markov over $N \in [X, 2X]$ gives (1)–(3) for almost all $N \in [X, 2X]$.
2. For polylogarithmic $H$ with $H/(\log X)^2 \to \infty$, take $m = 1$ ($b = p_0^{2u}$ fixed). Lemma 3.1 gives $\frac{1}{X}\sum_N (\Delta_1^{\mathrm{prime}}(N))^2 \ll_{q_0, w} H$, so by Chebyshev's inequality the number of $N \in [X, 2X]$ with $\Delta_1^{\mathrm{prime}}(N) \ge \frac{H}{28 p_0^{2u}\varphi(q_0)\log X}$ is $\ll_{q_0, w} X(\log X)^2/H = o(X)$. Prime powers give $O(X\log X/\sqrt{X}) = o(X)$ exceptions, and Lemma 3.3 gives $O(X(\log\log X)^{1+\kappa}/(\log X)^\kappa) = o(X)$ exceptions. Hence $\#_w(N, H) \gg_w H/\log X$ for almost all $N \in [X, 2X]$. ∎

*Proof of Theorem G2.2C (Unconditional `GF-22` on EVERY window $7/12 < a \le 1$).*
Fix $7/12 < a \le 1$, set $\varepsilon_0 := \frac{1}{2}(a - 7/12) > 0$, and construct **two** disjoint kill-prime families $\mathcal{P}_1, \mathcal{P}_2$ above $P_0$ as in `GF-22` Step 2 (with $L = \log_b\log N + O_w(1)$ from Theorem G2.4A, or $2\log_b\log N + O_w(1)$ without it), giving $q_\nu = q Q_\nu = \exp(O_w(\log\log N \cdot \log\log\log N))$. By Landau–Page (Davenport Ch. 14), at most one primitive real character $\chi_1 \bmod q_1$ with $q_1 \le \max(q_1', q_2')$ has a zero in $\sigma \ge 1 - c_0/\log(12\max(q_1', q_2'))$, $|t| \le 10$; since $\gcd(q_1', q_2') = q$ and fixed characters mod $q$ have fixed zero-free margins, pick $q' = q Q_\nu$ not divisible by $q_1$.

Set $U = (N + W' + f + 1)/A$, $Y = H/A$, and truncation height $T = U^{1 - a + \varepsilon_0}$. In the explicit formula for $\psi(U+Y; q', a_0) - \psi(U; q', a_0) - Y/\varphi(q')$:
- The truncation error is $O(U\log^2(q' U)/T) = O_w(Y N^{-\varepsilon_0}\log^2 N) = o(Y/\varphi(q'))$, and imprimitive reduction costs $O(\log q'\log N) = o(Y/\varphi(q'))$.
- Since $|(U+Y)^\rho - U^\rho|/|\rho| = |\int_U^{U+Y} t^{\rho-1} dt| \le Y U^{\beta - 1}$, zeros with $\beta \le 1/2$ and $|\gamma| < T$ contribute $\ll \frac{Y}{\varphi(q')} \cdot \varphi(q') T \log(q' T) U^{-1/2} = Y U^{\frac{1}{2} - a + \varepsilon_0}\log(q' U) \ll Y U^{-1/12}\log U = o(Y/\varphi(q'))$ (`C4`).
- For $\beta > 1/2$, combining Landau–Page ($|t| \le 10$) and the uniform Vinogradov–Korobov zero-free region ($10 \le |t| < T$; classical Montgomery 1971 p. 176 / 1994 Ch. 9, explicit constants via **Khale 2024, Theorem 1.1** `[R]`) gives $\beta \le 1 - \eta(U)$ with $\eta(U) = (62(\log U)^{2/3}(\log\log U)^{1/3})^{-1}$. Integrating by parts (with $N_{q'}(1 - \eta(U), T) = 0$):
```math
\frac{Y}{\varphi(q')} \sum_{\chi \bmod q'} \sum_{\substack{|\gamma| < T \\ \frac{1}{2} < \beta \le 1 - \eta(U)}} U^{\beta - 1} = \frac{Y}{\varphi(q')}\left(U^{-1/2} N_{q'}\!\left(\tfrac{1}{2}, T\right) + (\log U) \int_{1/2}^{1 - \eta(U)} U^{-(1-\sigma)} N_{q'}(\sigma, T)\, d\sigma\right).
```
Crucially, the factor $1/\varphi(q')$ **matches the main term $Y/\varphi(q')$ directly**. Put $\gamma_0 := 1 - A(1 - a + \varepsilon_0) = \frac{A}{2}(a - (1 - 1/A)) > 0$ (for $A = 12/5$: $\gamma_0 = \frac{6}{5}(a - 7/12) > 0$). Exactly as in Lemma 3.2:
  1. Using **Thorner–Zaman (2024, *Math. Z.* **306**, Theorem 2.1, eq. (2.1))** `[R]` ($N_{q'}(\sigma, T) \ll_{\varepsilon_1} (q' T)^{(\frac{12}{5} + \varepsilon_1)(1-\sigma)}$, log-free across $0 \le \sigma \le 1$) with $\varepsilon_1 = \gamma_0/2$ gives $(q' T)^{\frac{12}{5} + \varepsilon_1}/U \le U^{-\gamma_0/4}$ for large $U$, bounding the bracket by $\ll_a (\log U) U^{-\frac{\gamma_0}{4}\eta(U)} = \exp(-c'(a)(\log U)^{1/3}(\log\log U)^{-1/3}) \to 0$. (Equivalently, **Thorner–Zaman 2024, Theorem 1.1 & Remark 1.3** `[R]` applies directly once the exceptional modulus $q_1$ is avoided!)
  2. Alternatively, by the **two-regime $\sigma$-split at $\sigma_0 = \frac{4}{5}$ ($c_0 = \frac{1}{5}$)** — which handles ANY $\varepsilon$-form bound $(q' T)^{A(1-\sigma) + \varepsilon'}$ (both Huxley $A = 12/5$ and the Chen–Gupta–Li `2507.08296v2` `[R]` $A = 7/3$ / $T$-aspect $30/13$ addenda) — on $[\frac{1}{2}, \frac{4}{5}]$ taking $\varepsilon' = \gamma_0/20$ yields $U^{-(1-\sigma)} N_{q'}(\sigma, T) \ll U^{-\frac{3}{4}\gamma_0 \cdot \frac{1}{5} + \frac{\gamma_0}{20}} = U^{-\frac{\gamma_0}{10}}$ (`C4`), while on $[\frac{4}{5}, 1 - \eta(U)]$ **Jutila (1977, *Math. Scand.* **41**, Theorem 1, eq. (1.7))** `[R]` ($N_{q'}(\sigma, T) \ll_{\varepsilon''} (q' T)^{(2 + \varepsilon'')(1-\sigma)}$, log-free!) has $1 - 2(1 - a + \varepsilon_0) = a - 1/A > 1 - 2/A \ge 1/7 > 0$ and with $\varepsilon'' = 1/10$ yields $(q' T)^{2 + \varepsilon''}/U \le U^{-\frac{1}{4}(a - 1/A)}$, giving $U^{-\frac{1}{4}(a - 1/A)\eta(U)} = \exp(-c'(a)(\log U)^{1/3}(\log\log U)^{-1/3}) \to 0$ (`C4`).

Thus $\psi(U+Y; q', a_0) - \psi(U; q', a_0) \ge \frac{3Y}{4\varphi(q')}$, prime powers cost $O(\sqrt{N}\log N) = o(Y/\varphi(q'))$, and Step 5′ yields $|\mathcal{U}| \ge Y/(2\varphi(q')\log 2U)$. Steps 6′ and 7′ of `GF-48` (unconditional for all $a > 1/2$, or sharpened via Theorem G2.4A) conclude the proof. ∎

*Proof of Theorems G2.2D and G2.2B (`GF-22` on almost all windows below $1/2$).*
Fix a dyadic scale $X$ and choose $L = L(X)$ and $q' = q Q(X, w)$ **once** for the entire block $N \in [X, 2X]$, choosing $b^L$ larger by a slow factor $\psi(X) := \log\log X$ (which changes $\log q'$ by $o(\log\log X \cdot \log\log\log X)$).
- **Unconditional averaged-tail step (valid for ALL $1 \le H \le X$):** Let $B(N) := \#\{u \in \mathcal{U}(N) : |T_{Au+L}| \ge b^L/2\}$. Each $u \equiv a_0 \pmod{q'}$ in $[X/A, 3X/A]$ belongs to $[U(N), U(N) + Y)$ for at most $H = AY$ integers $N \in [X, 2X]$. Interchanging sums over $N$ and $u$ and applying either `GF-22` Lemma 5.2 on the prefix $[1, 3X/A]$ (first moment $r = 1$, $\alpha = 2$, $b^L \asymp \psi(X)(\log X)^2$, using $|T_{Au+L}| \le C_\Phi \sum_{k \ge 1}\tau(Au+L+k)b^{-k}$) or Theorem G2.4A's Galois-conjugate second-moment Shiu bound on the prefix $[1, 3X/A]$ (second moment $r = 2$, $\alpha = 1$, $b^L \asymp \psi(X)\log X$, using $|T_{Au+L}|^2 \le \frac{K_\Phi}{b-1}\sum_{\sigma \in G}\sum_{k \ge 1}|c_{\chi^\sigma}(Au+L+k)|^2 b^{-k}$):
  ```math
  \frac{1}{X} \sum_{X \le N < 2X} B(N) \le \frac{H}{X} \sum_{\substack{u \le 3X/A \\ u \equiv a_0 \ (q')}} \frac{(2 |T_{Au+L}|)^r}{b^{r L}} \ll \frac{H}{X} \cdot \frac{X/A}{\varphi(q')} \cdot \frac{\log X}{\psi(X)^r (\log X)^2} = \frac{Y}{\psi(X)^r \varphi(q') \log X} = o\left(\frac{Y}{\varphi(q')\log X}\right).
  ```
  By Markov over $N \in [X, 2X]$, $B(N) \ge \frac{Y}{56\varphi(q')\log 2U}$ holds for at most $O(X/\psi(X)^r) = o(X)$ starts $N$.
- **Prime-power removal (unconditional):** $\frac{1}{X}\sum_N \sum_{U(N) \le p^e < U(N)+Y,\, e \ge 2} \log p \le \frac{H}{X} O(\sqrt{X/A}\,\log X) = O(Y\sqrt{A/X}\,\log X)$, so by Markov prime powers contribute $\ge \frac{Y}{28\varphi(q')}$ for at most $O_w(\varphi(q')\sqrt{X}\log X) = O(X^{1/2 + o(1)}) = o(X)$ starts $N$ (independent of $H$).
- **Prime supply on almost all $[U(N), U(N) + Y)$:** Partition $[X/A, 3X/A]$ by the pairwise disjoint intervals $[U(N), U(N) + 1/A)$ of length $1/A$ and set $\delta := (Y - 2/A)/(6T) \in (0, 1/6]$ with $T = X/A$. For every $t \in [U(N), U(N) + 1/A) \subset [T, 3T]$ we have $t(1+\delta) \le U(N) + \frac{1}{A} + \frac{1}{2}(Y - 2/A) < U(N) + Y$ and $\delta t \ge \frac{1}{6}(Y - 2/A) \ge Y/7$ (for large $X$), so $\psi(U(N)+Y; q', a_0) - \psi(U(N); q', a_0) < \frac{Y}{14\varphi(q')}$ implies $|\widetilde{E}_\psi(t, \delta; q', a_0)| > \frac{Y}{14\varphi(q')}$ on the entire interval $[U(N), U(N) + 1/A)$:
  - For **Theorem G2.2D** ($1/6 < a \le 1$, unconditional): integrating over $[T, 3T]$ and applying **Lemma 3.2** (with two-family Landau–Page avoidance for $q'$, Thorner–Zaman 2024 Thm. 2.1 / Huxley 1975 + Jutila 1977 Thm. 1, and uniform Vinogradov–Korobov) bounds the exceptional set by $O(X[\varphi(q')\exp(-c'(a)(\log X)^{1/3}(\log\log X)^{-1/3}) + \varphi(q')^2\log^2(q' X)/Y]) = o(X)$, giving $|\mathcal{U}(N)| \ge Y/(28\varphi(q')\log 2U)$ for all but $o(X)$ starts $N \in [X, 2X]$.
  - For **Theorem G2.2B** (Dirichlet GRH): integrating over $[T, 3T]$ and applying **Lemma 3.1** (Selberg–GRH) bounds the exceptional set by $O(X \cdot \varphi(q')^2 \log^2(q' X) / Y)$, which is $o(X)$ whenever $H \ge \exp(C_1 \log\log X \cdot \log\log\log X)$ with $C_1 > 2\alpha d/\log b$ ($2d/\log b$ with Theorem G2.4A; $4d/\log b$ without it). Subtracting the $B(N)$ bad tails leaves at least $\frac{Y}{56\varphi(q')\log 2U} \ge H\exp(-C_w \log\log X \cdot \log\log\log X)$ good starts for almost all $N \in [X, 2X]$. ∎

---

### 3.3 Proof of Theorem G2.3 (Exact Leading Window Discrepancy Constants)

*Proof of Theorem G2.3.*
Apply `NormalityChecker.CoefficientTransfer` and `NormalityChecker.RadixWidthLaw` finite lemmas to the real number $y := \{b^N L_c(b)\}$ on length $H$ (using $\{b^n y\} = \{b^{N+n} L_c(b)\}$, so $D_H(y; b) = D_{N,H}(L_c(b); b)$ and `SharpTranslation.sharp_translation_isGreatest` gives the window translation identity verbatim). Write $c(n) = b^{V_b(n)} U_b(n)$ with $b \nmid U_b(n)$, $u(n) = \lfloor\log_b U_b(n)\rfloor + 1$, $t(n) = n - V_b(n)$, and $\tilde{t}(n) = t(n) - u(n)$. Put $\rho_{N, H} = S(N, H)/H \asymp_a (\log N)^{-\kappa}$ and $\lambda_{N, H} = \log_b(1/\rho_{N, H}) = \kappa\ell_N + O_a(1)$.

**Step 1 (Local upper bound via window form of Theorem 2.2).**
Apply the window form of `notes/phase20/coefficient-transfer.md` Theorem 2.2 on $[N, N+H)$ with $\varepsilon = \rho_{N, H}$ and $L = \lceil \lambda_{N, H} \rceil + 2$. Because $V_b(n) \le \log_b \tau(n) = O(\log N/\log\log N)$, every arrival $t(n) \in (N, N+H]$ comes from $n \in (N, N + H + O(\log N)]$, so $P(N, H) = S(N, H) + O(\log N)$, the right boundary shadow is $\Lambda_{N, H} = O(\log N)$, and $\widehat{P}_{N, H}(N + H + L) = S(N, H)(1 + o(1))$. Thus
```math
1 - D_{N, H}(L_c(b); b) \le 2\rho_{N, H} + \frac{W_U(N, H) + S(N, H)\lambda_{N, H} + O(S(N, H))}{H}.
```

**Step 2 (Local width moments `(W3)` purely via Shiu's theorem on $(N, N+H]$ — valid for ALL $0 < a \le 1$).**
- If $b = 2^k$: $U_b(n) \le 2^{k-1}\mathrm{odd}(c(n))$, so by Shiu (`thm:shiu`) on $(N, N+H]$, $W_U(N, H) \ll_a H/(\log N)^\kappa = O(S(N, H)) = o(S(N, H)\lambda_{N, H})$, giving $\omega_b = 0$.
- If $b \ne 2^k$: for any $|t| \le 1$ and $0 < z < 1$, both $g_t(n) = \mathbf{1}_{c(n)>0} c(n)^t$ (since $g_t(p^e) \le (e+1)^{|t|} \le 2^e$) and $\mathbf{1}_{c(n)>0} z^{\omega_{S, 1}(n)}$ (bounded by $1$) lie directly in Shiu's class. Applying `thm:shiu` on $(N, N+H]$ gives $\sum_{N < n \le N+H} g_t(n) \ll_{a, t} H(\log N)^{\delta 2^t - 1}$ and $\sum_{N < n \le N+H} \mathbf{1}_{c(n)>0} z^{\omega_{S,1}(n)} \ll_{a, z} H(\log N)^{\delta z - 1}$. By Chernoff optimization (as in `radix-lambert.md` Lemma 2.2), for every $\varepsilon > 0$ there is $c(\varepsilon) > 0$ with
  ```math
  \#\{N < n \le N+H : c(n) > 0,\ |\log c(n) - \delta(\log 2)LL| > \varepsilon LL\} \ll_{a, \varepsilon} H (\log N)^{-\kappa - c(\varepsilon)}.
  ```
  Integrating the upper tail $\int_{(\delta\log 2 + \varepsilon)LL}^\infty e^{-t_0 u} \sum g_{t_0}\,du = O_{a, \varepsilon}(H (\log N)^{-\kappa - c(\varepsilon)})$ bounds the full local first moment purely locally:
  ```math
  \sum_{N < n \le N+H,\, c(n)>0} \log c(n) \le (\delta\log 2 + o(1)) S(N, H) LL.
  ```
  To control $V_b(n)$ locally without any $\sqrt{N}$ square-factor error, pick an odd prime $q \mid b$ and define the multiplicative function $h_q(n) := 2^{v_q(c(n))} \mathbf{1}_{c(n)>0}$. At every prime $p$, $c(p) \in \{0, 2\}$ is not divisible by odd $q$, so $h_q(p) = \mathbf{1}_{p \in S}$; at prime powers $p^e$, $2^{v_q(c(p^e))} \le e + 1 \le 2^e$ (`C5` verified through $e \le 500$). Hence $h_q$ lies in Shiu's class with the exact same prime values as $\mathbf{1}_{c(n)>0}$, so `thm:shiu` gives $\sum_{N < n \le N+H} h_q(n) \ll_a H/(\log N)^\kappa$, and Markov gives $\#\{N < n \le N+H : c(n) > 0,\ V_b(n) > \varepsilon \lambda_{N, H}\} = o(S(N, H))$. Thus $u(n)/\lambda_{N, H} \to \omega_b = \delta\log 2/\kappa$ in $L^1$ on $\{n \in (N, N+H] : c(n) > 0\}$, proving `(W3)` locally.

**Step 3 (Local isolation `(E1)`–`(E5)` and circle-separation lower bound).**
Set $B = \max(0, 2\delta - 1)$, $H_V = \lceil(B + 2)\ell_N\rceil$, $R_N = \lceil(2+\omega_b)\lambda_{N, H} + (B + 2)\ell_N\rceil$, and $H_{\mathrm{iso}} = R_N + H_V$.
- `(E1)` & `(E3)`: Every $n'$ with $t(n') \in [N - R_N, N + H + R_N]$ lies in $[N - R_N, N + H + O(\log N)]$, on which Shiu bounds $\sum c(n') \ll_a H(\log N)^B$; Markov gives $\#\{V_b(n') > H_V\} \ll_a H/(\log N)^2$, spoiling $O_a(H\log\log N/(\log N)^2) = o(S(N, H))$ indices.
- `(E2)` (local pair sieve): For each $1 \le |h| \le H_{\mathrm{iso}} < z_0 = (\log N)^2$, `lem:selberg` on $(N, N+H]$ with $z = H^{1/4}$ gives $\#\{N < n \le N+H : c(n)c(n+h) > 0\} \ll_a H(\log\log N)^{2\kappa}/(\log N)^{2\kappa} + H^{1/2}\log^2 H$; summing over $|h| \le H_{\mathrm{iso}}$ yields $o(S(N, H))$.
- `(E4)`: By the arrival identity on $[N, N + H + R_N]$ + Shiu, $\sum_{N \le s < N + H + R_N} |A(s)| \ll_a H(\log N)^B$, so `RadixWidthLaw.card_large_tail_le` gives $\#\{|A(t(n))| > 1/2\} \ll_a H/(\log N)^{\kappa + 2} = o(S(N, H))$ (`C5`).
- Marking via `RadixWidthLaw.card_far_in_gap_ge` and `CoefficientTransfer.one_sub_discrepancy_ge_of_bulk_and_far` yields the matching lower bound $(1 + \omega_b - o(1))\rho_{N, H}\lambda_{N, H}$ whenever $\omega_b \le 1$ (i.e. $b = 2^k$ or $\delta \le \delta^* = 1/(1+\log 2)$); for even composite $b = 2^s b'$ and $\delta^* < \delta \le \delta^*_b$, the 2-adic run-exclusion Lemma 1.2 of `GF-21` (`notes/phase22/radix-thresholds-and-class-groups.md`) is purely local on individual good coefficients $U(n)$ and transfers verbatim! This proves Part 1.

**Step 4 (Explicit `GF-12` constants in Part 2).**
When $S$ is a union of reduced classes modulo $q_0$ of density $\delta = r/\varphi(q_0)$, the Dirichlet series $F(s) = \sum_{n \ge 1} \mathbf{1}_{c(n) > 0} n^{-s}$ satisfies $F(s) = \prod_{\chi \bmod q_0} L(s, \chi)^{a_\chi} \cdot G_0(s)$ with $a_\chi = \varphi(q_0)^{-1}\sum_{u \in S}\bar\chi(u)$ ($a_{\chi_0} = \delta$) and $G_0$ holomorphic and nonvanishing on $\Re(s) > 1/2$.
- *(a) Unconditionally on all windows:* In the classical zero-free region $\sigma \ge 1 - c_0/\log(|t|+2)$ of all $L(s, \chi)$ ($\chi \bmod q_0$), $F(s)$ is holomorphic on the region minus the branch slit $(1 - c_0/\log 2, 1]$. The Selberg–Delange Hankel contour integral (Tenenbaum, Ch. II.5) gives $S(X) = \int_2^X \frac{C_f}{(\log t)^\kappa}(1 + O(1/\log t))\,dt + O(X\exp(-c_0'\sqrt{\log X}))$. Subtracting at $N + H$ and $N$ yields $S(N, H) \sim C_f H/(\log N)^\kappa$ uniformly for $N\exp(-c_1\sqrt{\log N}) \le H \le N$ ($0 < c_1 < c_0'$).
- *(b) Under `GRH(q_0)` on all windows:* No $L(s, \chi)$ ($\chi \bmod q_0$) vanishes in $\Re(s) > 1/2$, so $F(s)$ has **zero off-axis branch points** in $\{\Re(s) > 1/2\} \setminus (1/2, 1]$. Because $\Re(a_\chi)$ can be negative for general unions of residue classes $S$ (though every $a_\chi \ge 0$ for $\chi_{-4}$ and `ex:quarter`), bounding $|F(s)|$ requires **both** upper and lower bounds for $|L(s, \chi)|$. Shifting Perron's integral for $S(N + H) - S(N)$ (truncated at $T = \sqrt{N}$) to the vertical line **$\sigma_1 = \frac{1}{2} + \frac{c}{\log\log N}$** (for any fixed $c > 0$, e.g. $c = 1$) — where `GRH(q_0)` yields the uniform **two-sided** bound $|\log L(\sigma + it, \chi)| \ll_{q_0, c} \frac{\log(|t| + 3)}{\log\log(|t| + 3)}$ on $\sigma \ge \sigma_1$ (Montgomery–Vaughan Ch. 13 / Titchmarsh Ch. 14) — gives $|F(\sigma_1 + it)| \ll_{q_0, c} \exp(C \log N / \log\log N)$ for $|t| \le \sqrt{N}$ and $N^{\sigma_1} = \sqrt{N}\exp(c \log N / \log\log N)$, yielding
  ```math
  S(N, H) = \frac{C_f H}{(\log N)^\kappa}\left(1 + O\left(\frac{1}{\log N}\right)\right) + O\left(\sqrt{N}\exp\left(C_1 \frac{\log N}{\log\log N}\right)\right),
  ```
  so $S(N, H) \sim C_f H/(\log N)^\kappa$ uniformly for $\sqrt{N}\exp(C_2 \log N / \log\log N) \le H \le N$ (and hence all fixed $a > 1/2$).
- *(c) Unconditionally on almost all windows at every fixed $0 < a \le 1$ (using Matomäki–Radziwiłł II, `arXiv:2007.04290`, Corollary 1 `[R]`):* Because $c$ is multiplicative, $\mathcal{N} := \{n \in \mathbb{N} : c(n) > 0\}$ is a multiplicative subset of $\mathbb{N}$. Since $S$ contains every prime $p \equiv a_0 \pmod{q_0}$, Mertens' theorem in arithmetic progressions gives $\sum_{w < p \le z,\, p \in \mathcal{N}} 1/p \ge \varphi(q_0)^{-1}\sum_{w < p \le z} 1/p - O_{q_0}(1/\log w)$ for all $2 \le w \le z$, verifying condition (1.2) of `arXiv:2007.04290` with $\alpha = \frac{1}{2\varphi(q_0)} > 0$. Here $\delta(\mathcal{N}; X) = \prod_{p \le X,\, p \notin \mathcal{N}}(1 - 1/p) \asymp (\log X)^{-\kappa}$, so for any $H \in [X^a, X]$ we have $h_0 := H\delta(\mathcal{N}; X) \in [X^{a/2}, X]$ (for large $X$). Applying `arXiv:2007.04290` Corollary 1 with $f \equiv 1$ and slowly decaying accuracy parameter $\delta_0(X) := (\log\log X)^{-1/(2\kappa(\alpha))} \to 0$ gives an exceptional set of size $\ll X h_0^{-\delta_0(X)^{\kappa(\alpha)}} \le X \exp(-\frac{a}{2}\log X \cdot (\log\log X)^{-1/2}) = o(X)$ uniformly in $H \in [X^a, X]$, outside which $S(N, H) = (1 + o(1))(H/X)\sum_{X < n \le 2X}\mathbf{1}_{c(n)>0} \sim C_f H/(\log N)^\kappa$ (by the unconditional long-interval asymptotic on $[X, 2X]$). Substituting into Part 1 completes Part 2. ∎

*(Remark on unconditional branch cuts: Shifting Perron's contour for $F(s)$ past zeros of $\zeta(s) L(s, \chi)$ without GRH creates fractional-power branch cuts at every zero in the critical strip, which is why Part 2's unconditional explicit constant stops at the zero-free range $N\exp(-c_1\sqrt{\log N})$, whereas Part 1 gives the exact self-normalized constant unconditionally on all polynomial windows $a > 0.53$.)*

---

### 3.4 Proofs of Theorems G2.4A and G2.4B (Second-Moment Shiu Reduction & CRT Covering Barrier)

*Proof of Theorem G2.4A.*
**Step 1 (Galois-conjugate trace-duality bound for every $h \ge 2$).**
Let $K := \mathbb{Q}(\zeta_h)$ ($m := \varphi(h) = [K : \mathbb{Q}]$) and $G := \operatorname{Gal}(K/\mathbb{Q})$. Note that a single-embedding bound $|\Phi(z)| \le C_\Phi |z|$ is **false** whenever $\varphi(h) \ge 4$ (because $\mathbb{Z}[\zeta_h]$ is dense in $\mathbb{C}$: for $h = 5$ and $\Phi_0(a_0 + a_1\zeta_5 + a_2\zeta_5^2 + a_3\zeta_5^3) = a_0$, the elements $z_k = (1 + \zeta_5^2)^k$ have $|z_k| = (\frac{\sqrt{5}-1}{2})^k \to 0$ exponentially while $|\Phi_0(z_k)| = F_{k+1} \in \{8, 89, 10946, 165580141\}$ at $k = 5, 10, 20, 40$, certified in exact rationals in `C6`). Instead, since $\Phi : \mathbb{Z}[\zeta_h] \to \mathbb{Z}$ is additive, it extends uniquely to a $\mathbb{Q}$-linear functional $\Phi : K \to \mathbb{Q}$ on the $\mathbb{Z}$-basis $\{1, \zeta_h, \dots, \zeta_h^{m-1}\}$. By separability of $K/\mathbb{Q}$, the trace pairing $(x, y) \mapsto \operatorname{Tr}_{K/\mathbb{Q}}(xy)$ is nondegenerate (equivalently, the Vandermonde matrix $V = (\sigma(\zeta_h)^j)_{\sigma \in G,\, 0 \le j < m}$ satisfies $\det(V)^2 = \operatorname{disc}(\mathbb{Q}(\zeta_h)/\mathbb{Q}) \ne 0$, so every coordinate $a_j$ is a $K$-linear combination of the Galois conjugates $\{\sigma(z)\}_{\sigma \in G}$). Hence there exists a unique element $\beta_\Phi \in K$ such that
```math
\Phi(z) = \operatorname{Tr}_{K/\mathbb{Q}}(\beta_\Phi z) = \sum_{\sigma \in G} \sigma(\beta_\Phi)\,\sigma(z) \qquad \forall z \in \mathbb{Z}[\zeta_h].
```
For every $n \ge 1$ and $\sigma \in G$, $\sigma(c_\chi(n)) = \sum_{d \mid n} \sigma(\chi(d)) = c_{\chi^\sigma}(n)$, where $\chi^\sigma := \sigma \circ \chi \bmod q$ is again a **nonprincipal** character of order $h$. By triangle inequality and Cauchy–Schwarz (noting $\overline{\sigma(z)} = \sigma(\bar{z})$ since $G$ is abelian, so $\sum_{\sigma \in G} |\sigma(\beta_\Phi)|^2 = \operatorname{Tr}_{K/\mathbb{Q}}(\beta_\Phi\overline{\beta_\Phi}) =: K_\Phi \in \mathbb{Q}_{>0}$):
```math
|c_\Phi(n)| = |\Phi(c_\chi(n))| \le C'_\Phi \sum_{\sigma \in G} |c_{\chi^\sigma}(n)|, \qquad |c_\Phi(n)|^2 \le K_\Phi \sum_{\sigma \in G} |c_{\chi^\sigma}(n)|^2,
```
where $C'_\Phi := \max_{\sigma \in G} |\sigma(\beta_\Phi)|$. (At $h = 5$ with $\Phi_0(z) = a_0$, solving the exact rational trace-matrix system in `C6` gives $\beta_{\Phi_0} = \frac{1 - \zeta_5}{5}$, $K_{\Phi_0} = \frac{2}{5}$, and verifies $|\Phi_r(z_k)|^2 \le K_{\Phi_r}\operatorname{Tr}(z_k\overline{z_k})$ in pure `Fraction`s for all $0 \le r \le 3$ and $1 \le k \le 40$.)

**Step 2 (Universal second-moment identity and Shiu bound across conjugates).**
For **every** $\sigma \in G$, since $\chi^\sigma \bmod q$ is nonprincipal, $\sum_{(r, q) = 1} \chi^\sigma(r) = \sum_{(r, q) = 1} \overline{\chi^\sigma}(r) = 0$, so
```math
\frac{1}{\varphi(q)} \sum_{\gcd(r, q) = 1} |1 + \chi^\sigma(r)|^2 = \frac{1}{\varphi(q)} \sum_{\gcd(r, q) = 1} \bigl(2 + \chi^\sigma(r) + \overline{\chi^\sigma}(r)\bigr) = 2.
```
For any $u \in \mathcal{U}$, Cauchy–Schwarz over $k \ge 1$ and the Galois-conjugate inequality above give
```math
|T_{Au+L}|^2 \le \left(\sum_{k \ge 1} |c_\Phi(Au + L + k)| b^{-k}\right)^2 \le \frac{1}{b - 1} \sum_{k \ge 1} |c_\Phi(Au + L + k)|^2 b^{-k} \le \frac{K_\Phi}{b - 1} \sum_{\sigma \in G} \sum_{k \ge 1} |c_{\chi^\sigma}(Au + L + k)|^2 b^{-k}.
```
Choose $P_0$ with $K_0 := P_0 - L - W' - f \ge \lceil 4s\log_b(d+1) + 8\log_b\log N \rceil$ (increasing $P_0$ only by a constant factor, leaving $\log q' \sim (d/\log b)\log\log N \cdot \log\log\log N$ unchanged). For **each** $\sigma \in G$:
- For $1 \le k < K_0$: no kill prime $p_j \in \mathcal{P}_\nu$ divides $A a_0 + L + k$, so factoring $m = Au + L + k = \tilde{g} m_1$ where $\tilde{g}$ is the $(Aq)$-smooth part and $\gcd(m_1, Aq') = 1$ gives $|c_{\chi^\sigma}(m)|^2 = |c_{\chi^\sigma}(\tilde{g})|^2 |c_{\chi^\sigma}(m_1)|^2 \le \tau(\tilde{g})^2 |c_{\chi^\sigma}(m_1)|^2$. Summing over $\tilde{g} \le H^{1/4}$ (tail $\tilde{g} > H^{1/4}$ is $O(H^{1-\eta})$) and applying Shiu's theorem (`thm:shiu`) to the multiplicative function $|c_{\chi^\sigma}(m_1)|^2$ (note $|c_{\chi^\sigma}(p^e)|^2 \le (e+1)^2 \le 4^e$ and $\sum_{p \le N} |c_{\chi^\sigma}(p)|^2 / p = 2\log\log N + O_q(1)$) on the coprime progression modulo $q' \cdot (Aq/\gcd(\tilde{g}, Aq)) = N^{o(1)} < (H/\tilde{g})^{1/2}$ yields
  ```math
  \sum_{\substack{U \le u < U + Y \\ u \equiv a_0 \ (q')}} |c_{\chi^\sigma}(Au + L + k)|^2 \ll_{q, w, a} \frac{Y}{\varphi(q')} \cdot \frac{(\log N)^2}{\log N} = \frac{Y}{\varphi(q')} \log N.
  ```
- For $k \ge K_0$: use $|c_{\chi^\sigma}(m)|^2 \le \tau(m)^2$ and the same $(Aq')$-smooth factorization + Shiu on $\tau(m_1)^2$ (mean $(\log N)^3$) with $\tau(g_k)^2 \le \tau(A)^2\tau(q)^2 (d+1)^{2s}$: since $(d+1)^{2s} b^{-k/2} \le (\log N)^{-4}$ for $k \ge K_0$, the sum over $k \ge K_0$ is $O_{q, w, a}(Y/(\varphi(q')\log N))$.

Summing over all $\varphi(h)$ conjugates $\sigma \in G$ multiplies the implied constant only by $\varphi(h) K_\Phi = O_{h, \Phi}(1)$, giving $\sum_{u \equiv a_0 \ (q')} |T_{Au+L}|^2 \ll_{q, \Phi, w, a} \frac{Y}{\varphi(q')}\log N$. By Chebyshev's inequality,
```math
\#\left\{u \in \mathcal{U} : |T_{Au+L}| \ge \frac{b^L}{2}\right\} \le \frac{4}{b^{2L}} \sum_u |T_{Au+L}|^2 \ll_{q, \Phi, w, a} \frac{Y}{\varphi(q')} \frac{\log N}{b^{2L}}.
```
Choosing $b^L \ge K_2 \log N$ (with $K_2 = K_2(q, \Phi, w, a)$ sufficiently large), i.e. **$L = \frac{1}{\log b}\log\log N + O_{q, \Phi, w, a}(1)$**, makes the bad set at most $\frac{Y}{4\varphi(q')\log 2U}$, halving $L$ and cutting $\log q'$ from $\frac{2d}{\log b}\log\log N\cdot\log\log\log N$ to **$\frac{d}{\log b}\log\log N\cdot\log\log\log N$**.

**Step 3 (General $t$-th moment, strict log-convexity at $t = 2$, and exact proof of $\alpha_*(\chi) < 1$ for every $h \ge 2$).**
For general $t \ge 1$, Hölder's inequality on $|T_{Au+L}| \le C'_\Phi \sum_{\sigma \in G}\sum_{k \ge 1} |c_{\chi^\sigma}(Au+L+k)| b^{-k}$ + Shiu on each $|c_{\chi^\sigma}|^t$ gives $b^{tL} \gg (\log N)^{\kappa_t(\chi)}$, i.e. $b^L \gg (\log N)^{\kappa_t(\chi)/t}$ where $\kappa_t(\chi) = \frac{1}{h}\sum_{j=0}^{h-1} |1 + e^{2\pi i j/h}|^t$.
- *Asymptotic global minimizer ($h \to \infty$):* As $h \to \infty$, $\kappa_t(\chi) \to \kappa_t(\infty) = \mathbb{E}[|1 + e^{i\theta}|^t] = \frac{2^t}{\sqrt{\pi}}\frac{\Gamma((t+1)/2)}{\Gamma(t/2+1)}$. By Hölder's inequality $t \mapsto \log \kappa_t(\infty)$ is convex on $(0, \infty)$, and $t \mapsto -\log t$ is strictly convex on $(0, \infty)$, so $t \mapsto \log(\kappa_t(\infty)/t)$ is **strictly convex** on $(0, \infty)$. Its derivative at $t = 2$ is
  ```math
  \log 2 + \tfrac{1}{2}\psi(\tfrac{3}{2}) - \tfrac{1}{2}\psi(2) - \tfrac{1}{2} = \log 2 + \tfrac{1 - 2\log 2}{2} - \tfrac{1}{2} = 0,
  ```
  so $t = 2$ ($\alpha = 1$) is the **unique global minimizer** on $(0, \infty)$.
- *Strict inequality $\alpha_*(\chi) < 1$ for every finite $h \ge 2$:* Let $f(\theta) := |1 + e^{i\theta}|^2 \log|1 + e^{i\theta}| = (2 + 2\cos\theta)\log|1 + e^{i\theta}|$ (with $f(\pi) = 0$). Since $f \in C^1(\mathbb{R}/2\pi\mathbb{Z})$ and $\log|1 + e^{i\theta}| = \sum_{m=1}^\infty \frac{(-1)^{m-1}}{m}\cos(m\theta)$ has Fourier coefficients $g_0 = 0$, $g_m = \frac{(-1)^{|m|-1}}{2|m|}$ ($m \ne 0$), multiplying by $2 + e^{i\theta} + e^{-i\theta}$ gives $\widehat{f}(0) = 1$, $\widehat{f}(\pm 1) = \frac{3}{4}$, and for $|n| \ge 2$:
  ```math
  \widehat{f}(n) = 2 g_n + g_{n-1} + g_{n+1} = \frac{(-1)^n}{2}\left(-\frac{2}{|n|} + \frac{1}{|n|-1} + \frac{1}{|n|+1}\right) = \frac{(-1)^n}{|n|(n^2 - 1)}.
  ```
  Because $\sum_{n \in \mathbb{Z}} |\widehat{f}(n)| < \infty$ and $f$ is continuous, $f(\theta) = \sum_{n \in \mathbb{Z}} \widehat{f}(n) e^{in\theta}$ holds pointwise everywhere. Averaging over $\theta = 2\pi j/h$ ($0 \le j < h$) kills every $h \nmid n$, yielding for **every integer $h \ge 2$**:
  ```math
  \kappa'_2(h) - 1 = \frac{1}{h}\sum_{j=0}^{h-1} f\!\left(\frac{2\pi j}{h}\right) - 1 = 2\sum_{k=1}^{\infty} \widehat{f}(kh) = \sum_{k=1}^{\infty} \frac{2(-1)^{kh}}{kh(k^2 h^2 - 1)}.
  ```
  If $h \ge 2$ is even, every term is strictly positive, so $\kappa'_2(h) - 1 > \frac{2}{h(h^2-1)} > 0$ (hence optimal $t_* < 2$); if $h \ge 3$ is odd, the series strictly alternates with strictly decreasing magnitudes $a_k = \frac{2}{kh(k^2 h^2 - 1)}$, so $\kappa'_2(h) - 1 < -a_1 + a_2 < 0$ (hence optimal $t_* > 2$; checked for $2 \le h \le 60$ in `C6`). In every case $\left.\frac{d}{dt}\right|_{t=2}(\kappa_t(h)/t) = \frac{1}{2}(\kappa'_2(h) - 1) \ne 0$, proving **$\alpha_*(\chi) < 1$ strictly for every $h \ge 2$** (and `C6` certifies in exact integers that $g_3(21/10) < 1$ at $h = 3$ and $g_2(3/2) < 95/100$ at $h = 2$). ∎

*Proof of Theorem G2.4B.*
**Part 1 (Single CRT congruence class).** Let $Q = \operatorname{lcm}_{1 \le j \le L} p_j^{e_j + 1}$ enforce $v_{p_j}(m_0 + j) \equiv d_{p_j} - 1 \pmod{d_{p_j}}$ for every $j \in \{1, \dots, L\}$, where every $p_j \in \mathcal{P}'$ has $d_{p_j} \ge d_{\min} \ge 3$ and hence $p_j^{d_{p_j} - 1} \mid m_0 + j$ with $d_{p_j} - 1 \ge 2$.
1. For any prime $p \in \mathcal{P}'$ and any integer $m_0$, the set of offsets $I_p := \{j \in \{1, \dots, L\} : p^{d_p - 1} \mid m_0 + j\}$ lies in a single residue class modulo $p^{d_p - 1}$ inside an interval of length $L$, so $|I_p| \le \lfloor L/p^{d_p - 1} \rfloor + 1$.
2. If $p > \sqrt{L}$, then $p^{d_p - 1} \ge p^2 > L$, so $|I_p| \le 1$: **each prime $p > \sqrt{L}$ can kill at most ONE offset in $\{1, \dots, L\}$**.
3. All small primes $p \in \mathcal{P}'$ with $p \le \sqrt{L}$ combined kill at most
   ```math
   S_{\mathrm{sm}}(L) := \sum_{\substack{p \in \mathcal{P}' \\ p \le \sqrt{L}}} \left(\left\lfloor \frac{L}{p^{d_p - 1}} \right\rfloor + 1\right) \le L \sum_{p \in \mathcal{P}'} \frac{1}{p^2} + \pi(\sqrt{L}) = \bigl(P_{\mathcal{P}'}(2) + o(1)\bigr) L.
   ```
   By exact rational summation over $p \le 10{,}000$ plus the telescoping tail $\sum_{n > 10000} n^{-2} < 1/10000$ (`C6`), $P(2) \in [0.452238, 0.452338] < 1/2$, and for cubic mod 7 $P_{\mathcal{P}'}(2) \in [0.422597, 0.422697]$.
4. Hence at least $m(L) := L - S_{\mathrm{sm}}(L) \ge (1 - P_{\mathcal{P}'}(2) - o(1))L$ uncovered offsets (strictly $> \frac{1}{2} L$ for all $L \ge L_0(\chi)$, e.g. $L \ge 20$ for cubic mod $7$, while $m(10) = 5 = L/2$) MUST be killed by pairwise **distinct** primes $p_1 < \dots < p_{m(L)}$ in $\mathcal{P}' \cap (\sqrt{L}, \infty)$, each dividing $Q$ to exponent at least $d_{\min} \ge 3$. By PNT (or Chebyshev's elementary lower bound $\sum_{i=1}^m \log p_i \ge (1 - o(1)) m\log m$):
   ```math
   \log Q \ge d_{\min} \sum_{i=1}^{m(L)} \log p_i \ge d_{\min} \bigl(1 - P_{\mathcal{P}'}(2) - o(1)\bigr) L \log L.
   ```
   (Even for $L = 20, 50, 100, 1000$ on cubic mod 7, `C6` certifies explicitly $m \ge 11, 28, 57, 576$ and $\log_2 Q_{\min} \ge 155, 524, 1248, 19246$.)

**Part 2 (Lemma 3.4: Union bound over ALL zero blocks $\mathcal{Z}_\chi(L)$).**
Consider any integer $n \in \mathcal{Z}_\chi(L) \cap (N, N + H]$ (taking $N = 0, H = X \to \infty$ at fixed $L \ge L_0(\chi)$ for natural density, or $H \ge N^a$ with $a > 1/2$ and $L \ll \log\log N$ for long moving windows). For every $j \in \{1, \dots, L\}$, $c_\chi(n + j) = 0$ forces $p^{d_p - 1} \mid (n + j)$ (hence $p^2 \mid n + j$) for some $p \in \mathcal{P}'$. By Step 3 above, all small primes $p \in \mathcal{P}' \cap [2, \sqrt{L}]$ combined cover at most $S_{\mathrm{sm}}(L)$ offsets, so there exist a subset $J = \{j_1 < \dots < j_m\} \subset \{1, \dots, L\}$ of cardinality $m := m(L)$ and an ordered $m$-tuple of **pairwise distinct** primes $(p_1, \dots, p_m) \in (\mathcal{P}' \cap (\sqrt{L}, \infty))^m$ such that $p_i^2 \mid (n + j_i)$ for all $1 \le i \le m$.

Set a large-prime cutoff $Z := H^{1/(4m)}$ and split into two exhaustive cases:
- *Subcase A (some offset $j \in \{1, \dots, L\}$ satisfies $p^2 \mid (n + j)$ for a prime $p > Z$):* Necessarily $p \le \sqrt{N + H + L}$, so for each $j$ the count of such $n \in (N, N + H]$ is at most
  ```math
  \sum_{Z < p \le \sqrt{N + H + L}} \left(\frac{H}{p^2} + 1\right) \le \frac{2 H}{Z} + \pi(\sqrt{N + H + L}) \le \frac{2 H}{Z} + 2\sqrt{N + H + L}.
  ```
  Summing over $1 \le j \le L$ gives at most $2 L H Z^{-1} + 2 L \sqrt{N + H + L}$.
- *Subcase B (all $m$ distinct primes satisfy $\sqrt{L} < p_i \le Z$):* For each fixed subset $J = \{j_1 < \dots < j_m\}$ ($\binom{L}{m}$ choices) and each ordered $m$-tuple of pairwise distinct primes $(p_1, \dots, p_m) \in (\mathcal{P}' \cap (\sqrt{L}, Z])^m$, the congruences $n \equiv -j_i \pmod{p_i^2}$ determine a unique residue class modulo $D = \prod_{i=1}^m p_i^2$, contributing at most $H/D + 1$ elements of $(N, N + H]$. Summing the $+1$ terms over all $\binom{L}{m}$ subsets and at most $Z^m$ tuples gives at most $2^L Z^m = 2^L H^{1/4}$, while summing the main terms $H/D$ gives
  ```math
  H \binom{L}{m} \sum_{\substack{p_1, \dots, p_m \in \mathcal{P}' \cap (\sqrt{L}, Z] \\ \text{distinct}}} \frac{1}{p_1^2 \cdots p_m^2} \le H \binom{L}{m} \left(\sum_{\substack{p \in \mathcal{P}' \\ p > \sqrt{L}}} \frac{1}{p^2}\right)^m.
  ```

By partial summation and Chebyshev/PNT, $\sum_{p > \sqrt{L}} p^{-2} \le \frac{2 + o(1)}{\sqrt{L}\log L}$, while $\binom{L}{m} \le 2^L$, so
```math
\log\!\left[\binom{L}{m}\left(\sum_{\substack{p \in \mathcal{P}' \\ p > \sqrt{L}}} \frac{1}{p^2}\right)^m\right] \le L\log 2 - m\left(\tfrac{1}{2}\log L + \log\log L - O(1)\right) = -\frac{1 - P_{\mathcal{P}'}(2) - o(1)}{2}\, L\log L.
```
- Taking $N = 0$, $H = X \to \infty$ at any fixed $L \ge L_0(\chi)$, the error $(2LX Z^{-1} + 2L\sqrt{X+L} + 2^L X^{1/4})/X = O_L(X^{-1/(4m)}) \to 0$, yielding the upper natural density bound $\overline{d}(\mathcal{Z}_\chi(L)) \le \exp(-\frac{1 - P_{\mathcal{P}'}(2) - o(1)}{2} L\log L)$.
- For any fixed $c > 0$ and $L \ge c\log_b\log N$ (with $L \ll \log\log N$, and note $\mathcal{Z}_\chi(L') \subseteq \mathcal{Z}_\chi(L)$ for $L' \ge L$): on every long window $(N, N + H]$ with $H \ge N^a$ ($a > 1/2$, including prefixes $[1, N]$), $Z = H^{1/(4m)} \ge \exp(\Omega(\log N / \log\log N))$, so all three error terms $2LHZ^{-1}$, $2L\sqrt{3N}$, and $2^L H^{1/4}$ are $o(H\exp(-C\log\log N\cdot\log\log\log N))$. Finally, applying this prefix bound on $[X, 3X]$ and averaging over $N \in [X, 2X]$ by Markov's inequality yields $|\mathcal{Z}_\chi(L) \cap (N, N + H]| \le H\exp(-\frac{1 - P_{\mathcal{P}'}(2) - o(1)}{2} L\log L)$ for **almost all** $N \in [X, 2X]$ at **any** window length $H \ge 1$.

Thus for any fixed $c > 0$ and $L \ge c\log_b\log N$, **no** method relying on zero blocks in $\mathcal{Z}_\chi(L)$ — whether a single CRT class (exponent $d_{\min}(1 - P_{\mathcal{P}'}(2))$) or an arbitrary union of CRT classes / squarefull or Selberg sieve (exponent $\frac{1 - P_{\mathcal{P}'}(2)}{2}$) — can reach $H/(\log N)^C$ or $c' H$. By contrast, for even-order characters ($d_{\min} = 2$), $d_p - 1 = 1$ makes $\sum_{p \in \mathcal{Q}} 1/p = \infty$ diverge, which is precisely why Paper VI's squarefree Selberg sieve succeeds at polynomial-log density $(\log N)^{-\kappa}$. ∎

---

### 3.5 Audit of Unconditional Short-Interval Prime Inputs in Arithmetic Progressions (G2.5)

| Input / Theorem | Exponent $\nu$ | Scope ($q_0$ & quantifier) | Two-sided or minorant? | Reading label & Paper VI / Mira Cult applicability |
| --- | --- | --- | --- | --- |
| **Perelli–Pintz–Salerno (1985)**, *Invent. Math.* **79**, 1–9 | $\nu > 7/12 = 0.5833\ldots$ | **All** $q_0 \le X^{1/40}$ (averaged), **all** windows | Two-sided asymptotic | `[R]` (printed source verified in Paper VI). Applies to Paper VI (`thm:words`); NOT used in Theorem G2.2C. |
| **Perelli–Pintz–Salerno (1984)**, *Ann. Pisa* **11**, 529–539 | $\nu > 7/12$ (level $\rho < 3\nu - 7/4$) | Averaged over $q \le X^\rho$, **all** windows | Two-sided Bombieri–Vinogradov | `[R]` (audited in P13). Required by Mira Cult Claim 0002. |
| **Thorner–Zaman (2024)**, *Math. Z.* **306**, Paper No. 54 (`arXiv:2108.10878v2`) | $\nu > 7/12$ all; $\nu > 1/6$ almost all (Thm. 2.1: log-free $A = 12/5$) | Single modulus $q \ge 2$ (incl. $q' = X^{o(1)}$ without $\beta_1$) | Two-sided asymptotic & log-free zero density | `[R]` (published TeX & DOI verified directly). Combines Huxley (1975) + Jutila (1977, Thm. 1); directly supplies **Lemma 3.2** and **Theorems G2.2A, G2.2C, G2.2D**. |
| **Jutila (1977)**, *Math. Scand.* **41**, 45–62, **Theorem 1** eq. (1.7) | Log-free $N(\sigma, T, q) \ll_\varepsilon (qT)^{(2+\varepsilon)(1-\sigma)}$ ($\frac{4}{5} \le \sigma \le 1$) | Single modulus $q$ (and hybrid $N^*$ in eq. (1.8)), near $\sigma = 1$ | Log-free zero density | `[R]` (printed journal scan read directly). Eliminates all $(qT)^\varepsilon$ / log-power loss near $\sigma = 1$ for BOTH $A = 12/5$ and $A = 7/3$ ($\sigma$-split at $\frac{4}{5}$). |
| **Guth–Maynard (2024/2026)**, `arXiv:2405.20552v2` (*Ann. of Math.* **203**(2) `[S]`) | $\nu > 17/30 = 0.5667\ldots$ ($A = 30/13$) | **$q_0 = 1$ ($\zeta(s)$) ONLY**, all windows ($2/15$ almost all) | Two-sided asymptotic | `[R]` (arXiv v2 TeX read; journal metadata `[S]`). **Does NOT directly apply** to Paper VI ($q_0 \ge 3$) or Mira Cult without character/hybrid extension. |
| **Chen–Gupta–Li (2025/2026)**, `arXiv:2507.08296v2` (Jul 2026) | Uniform $A = 7/3$ ($\nu > 4/7$ all, $1/7$ almost all); Thm. 2 $T$-aspect $30/13$ for $q = U^{o(1)}$ ($17/30$ all, $2/15$ almost all) | Single modulus $q$ ($\sum_{\chi \bmod q} N(\sigma, T, \chi) \le (qT)^{o(1)}(q^{\frac{7}{3}(1-\sigma)}T^{2(1-\sigma)} + (qT)^{\frac{30}{13}(1-\sigma)})$) | Two-sided (unrefereed preprint) | `[R]` (arXiv v2 TeX read). Pairing with **Jutila 1977 Thm. 1** `[R]` on $[\frac{4}{5}, 1]$ closes the near-$\sigma = 1$ $\varepsilon$-gap; segregated as unrefereed preprint and NOT used in main theorems; does NOT supply $Q$-summed BV level for Mira Cult. |
| **Baker–Harman–Pintz (1997)**, Thm. 3(I) (via Kumchev 2002) | $\nu > 0.55 = 11/20$ | $q_0 \le (\log X)^A$, **all** windows | Lower bound | `[S]`. Superseded by Kumchev 2002 for Paper VI. |
| **Kumchev (2002)**, *Q. J. Math.* **53**, 479–501 | $\nu > 0.53$ | $q_0 \le Y X^{-0.53+\eta}$, **all** windows | Signed Harman minorant $\lambda$ | `[R]` (author's posted text per Paper VI). **Sharpest published unconditional exponent for Paper VI $(\mathrm{P}_\nu)$**; does NOT transfer to Mira Cult (`GF-48` §3.4). |
| **Baker–Harman–Pintz (2001)**, *Proc. LMS* **83**, 532–562 | $\nu = 0.525$ | **$q_0 = 1$ ONLY**, all windows | Harman sieve + Watt (1995) | `[S]`. **Does NOT hold for arithmetic progressions $q_0 \ge 3$** (lacks character-twisted Watt fourth moment, as Kumchev 2002 §1 explicitly notes). |
| **Huxley (1972/1975)**, *Invent. Math.* **15** & *Acta Arith.* **26**, 435–444 | $A = 12/5$ ($\nu > 7/12$ all, $\nu > 1/6$ almost all) | Fixed $q_0$ and single modulus $q$ | Zero-density estimate | `[S]` (cited via **Thorner–Zaman 2024 Thm. 2.1** `[R]` and Chen–Gupta–Li eq. (1.5) `[R]`; combined with Jutila 1977 `[R]` near $\sigma = 1$ in Lemma 3.2 & G2.2A/C/D). |
| **Jia (1996)**, *Acta Arith.* **76**, 21–84 | $\nu > 1/20 = 0.05$ | **$q_0 = 1$ ONLY**, almost all windows | Harman sieve | `[S]`. Stated for $q_0 = 1$ only; NOT applied to Paper VI ($q_0 \ge 3$). |

---

## 4. Track G3: External Literature & Provenance Audit

> **Methodological caveat.** No web or bibliographic search proves priority or novelty. All provenance judgments below are provisional pending independent human specialist review; cross-model review is not independent human peer review. **Zero external contact and zero endorsement claims have occurred.**

### 4.1 Mesoscopic Local Limit Theorems for Shifted Divisor Functions & Sparse Multiplicative Supports
- **Classical probabilistic foundations:** Erdős–Kac (1940, *Amer. J. Math.* **62**, 738–742) `[S]` (Gaussian CLT for $\omega(n)$); Halberstam (1955/1956, *J. LMS*) `[S]` (additive functions on shifted primes $p + a$); Kubilius (1964, *Probabilistic Methods in the Theory of Numbers*, AMS) `[S]`; Tenenbaum (*Introduction to Analytic and Probabilistic Number Theory*, 3rd ed., CUP 2015, Chs. II.5, III.3–III.4) `[S]` (Selberg–Delange, Halász, Turán–Kubilius).
- **Sparse multiplicative supports in almost all short intervals (Hooley & Matomäki–Radziwiłł II):**
  - **C. Hooley (1971, *Acta Math.* **127**, 279–297; 1973, *J. Number Theory* **5**, 215–217; 1974, *J. Reine Angew. Math.* **267**, 207–218; 1994, *J. Reine Angew. Math.* **452**, 79–109)** `[S]`: using the shifted convolution problem for $r_2(n)$ (coefficients of $\zeta_{\mathbb{Q}(i)}(s)$), Hooley (1994) proved the order of magnitude $\sum_{x < s_i \le x + h_0\sqrt{\log x}} 1 \asymp h_0$ for integers representable as sums of two squares ($c = 1 * \chi_{-4}$, $\kappa = 1/2$) in almost all short intervals whenever $h_0 \to \infty$ (and Hooley 1971 proved the gap moment $\sum_{s_n \le x} (s_{n+1} - s_n)^\gamma \asymp x(\log x)^{(\gamma-1)/2}$ for $\gamma \in [1, 5/3)$).
  - **K. Matomäki & M. Radziwiłł, *Multiplicative functions in short intervals II* (`arXiv:2007.04290`, Jul 2020, preprint)** `[R]`: whereas Matomäki–Radziwiłł (2016, *Ann. of Math.* **183**, 1015–1056) `[A/S]` has error $o(H)$ (which is trivial for lacunary supports of density $(\log X)^{-\kappa}$), **MR II** resolves the sparse case directly! Specifically, for any multiplicative subset $\mathcal{N} \subset \mathbb{N}$ satisfying the prime lower-density hypothesis (1.2) ($\sum_{w < p \le z,\, p \in \mathcal{N}} 1/p > \alpha \sum_{w < p \le z} 1/p - O(1/\log w)$) — which holds unconditionally for every Paper VI `(H1)`–`(H4)` support $\mathbf{1}_{c>0}$ with $\alpha = \frac{1}{2\varphi(q_0)}$ — **Corollary 1** and **Theorem 1** of MR II establish the **full asymptotic** $\sum_{x < n \le x + h_0\delta(\mathcal{N}; X)^{-1},\, n \in \mathcal{N}} 1 = (1 + o(1)) h_0 \cdot \frac{1}{X\delta(\mathcal{N}; X)}\sum_{X < n \le 2X,\, n \in \mathcal{N}} 1$ for almost all $x \in [X, 2X]$ (with power-saving exceptional set $\ll X h_0^{-\delta^{\kappa(\alpha)}}$) for **every** $h_0 \to \infty$ (i.e. every $H/(\log X)^\kappa \to \infty$, far below $X^{1/6}$!), strengthening Hooley (1994) to a full asymptotic for sums of two squares and extending it to general number-field norm forms (`Theorem 2` of MR II).
  - **Consequence for positioning Track G:** Because Hooley (1994) and MR II (`arXiv:2007.04290`) already supply almost-all short-interval **support** counts $S(N, H)$ down to $H/(\log X)^\kappa \to \infty$ (feeding directly into **Theorem G2.3(1)** and yielding **Theorem G2.3(2c)**'s explicit `GF-12` window constant at every fixed $a > 0$ on almost all windows), **Theorems G2.2A and G2.2A′ must be positioned specifically as word-count and $R$-isolated planting theorems** for arbitrary binary words $w$ in $L_c(2)$ (which require locating isolated planted prime shifts $n = bp - j_0$ and do not follow from $S(N, H)$ alone).
- **Modern local limit and short-interval correlation literature:** Granville–Soundararajan (2007, *Sieving and the Erdős–Kac theorem*, NATO Sci. Ser. II **237**) `[S]` (moment method for shifted/sieved sets); Harper (2009, *Q. J. Math.*; 2013) `[S]` (Stein's method & local/large-deviation estimates for additive functions); Matomäki–Radziwiłł (2016, *Ann. of Math.* **183**, 1015–1056) `[A/S]`; Matomäki–Radziwiłł–Tao (2015/2019) `[S]` and Tao–Teräväinen (2019/2023) `[S]` (joint local limit theorems for $(\Omega(n), \Omega(n+1))$ and Chowla/Elliott correlations).
- **External application to $E(2)$:** **Mira Cult (`Mira-Cult/math`, Claim 0002, commit `149831943806a656c9efaa14cacbd9c915b2a2ba`, 23 Nov 2026)** `[R]` (audited in `notes/phase13/erdos-borwein.md` and `reviews/erdos-local-limit.md`; paper credits GPT-6.2 Astra with drafting under Mira Cult's guidance). Develops a multi-bank force-weighted conditional local-limit theorem for shifted $\tau(bp + j)$ on short intervals $H \ge N^a$ ($a > 7/12$, unconditionally; audited to $a > 1/2$ under Dirichlet GRH in `GF-48` §3), yielding positive lower word density for $E(2)$. Residual verification burden on the uniform exact-atom induction remains explicitly recorded; zero external contact, zero endorsement.

### 4.2 Short-Interval Prime Distribution in Arithmetic Progressions
- **Classical & GRH benchmarks:** Cramér (1920) `[S]`; Selberg (1943, *Arch. Math. Naturvid.* **47**, 87–105) `[S]` (almost-all short intervals $H/(\log X)^2 \to \infty$ under RH); Davenport (*Multiplicative Number Theory*, 2nd/3rd ed., Chs. 14–20) `[R/S]`; Montgomery (1971, *Topics in Multiplicative Number Theory*, LNM 227; 1994, CBMS 84, Ch. 9) `[S]`; Gallagher (1970, *Invent. Math.* **11**, 329–339) `[S]` (log-free large-sieve density estimate near $\sigma = 1$); **Jutila (1977, *Math. Scand.* **41**, 45–62, Theorem 1, eq. (1.7))** `[R]` (printed scan verified: log-free $N(\sigma, T, q) \ll_\varepsilon (qT)^{(2+\varepsilon)(1-\sigma)}$ for $\frac{4}{5} \le \sigma \le 1$, eliminating $\varepsilon$-loss near $\sigma = 1$); Huxley (1972, *Invent. Math.* **15**, 164–170; 1973/1975, *Acta Arith.* **24, 26, 27**) `[S]` ($A = 12/5$); Montgomery–Vaughan (1973, *Mathematika* **20**, 119–134; 2007, *MNT I*, Chs. 11–13) `[R/S]`; Saffari–Vaughan (1977) `[S]`; Perelli–Pintz–Salerno (1984, *Ann. Pisa* **11**, 529–539; 1985, *Invent. Math.* **79**, 1–9) `[R]`; Heath-Brown (1982, 1988) `[S]`; Jia (1996, *Acta Arith.* **76**, 21–84) `[S]`; Baker–Harman–Pintz (1997, CUP; 2001, *Proc. LMS* **83**, 532–562) `[S]`; Kumchev (2002, *Q. J. Math.* **53**, 479–501) `[R]`; Harman (2007, *Prime-Detecting Sieves*, PUP) `[S]`.
- **2024–2026 breakthroughs:** **Thorner–Zaman (2024, *Math. Z.* **306**, Paper No. 54, `arXiv:2108.10878v2`)** `[R]` (log-free $N_q(\sigma, T) \ll_\varepsilon (qT)^{(\frac{12}{5}+\varepsilon)(1-\sigma)}$ across $0 \le \sigma \le 1$ and uniform short-interval PNT in APs down to $\theta = 7/12$ without $\beta_1$, directly underwriting Lemma 3.2 and Theorems G2.2A, G2.2C, G2.2D) and **Thorner–Zaman (2024, *Forum Math.* **36**, 1059–1080, `arXiv:2208.11123v4`)** `[R]` (explicit Bombieri–Gallagher log-free density estimate); **Khale (`arXiv:2210.06457v1` `[R]`; *Q. J. Math.* **75**(1), 299–332, 2024 `[S]`, Theorem 1.1)** (first explicit Vinogradov–Korobov zero-free region in $(q, t)$ for $L(s, \chi)$, plus Appendix B proof of classical non-explicit eq. (1.4)); **Guth–Maynard (`arXiv:2405.20552v2` `[R]`; *Ann. of Math.* **203**(2), 623–675, 2026 `[S]`)** ($N(\sigma, T) \le T^{\frac{30}{13}(1-\sigma)+o(1)}$ for $\zeta(s)$, short intervals $x^{17/30+o(1)}$); **Chen–Gupta–Li (`arXiv:2507.08296v2`, Jul 2026, unrefereed preprint)** `[R]` (Theorem 2: $\sum_{\chi \bmod q} N(\sigma, T, \chi) \le (qT)^{o(1)}(q^{\frac{7}{3}(1-\sigma)}T^{2(1-\sigma)} + (qT)^{\frac{30}{13}(1-\sigma)})$, uniform $A = 7/3$); Le Duc Hieu (`arXiv:2509.04883v2`, Sep 2025) `[A]` ($k$-APs of primes in $[x, x+x^\theta]$, $\theta > 17/30$); Turnage-Butterbaugh (`arXiv:2607.04632`, Jul 2026) `[A]` (survey); Cossaboom (`arXiv:2609.27715`, Sep 2026) `[A]` ($\mathrm{GL}_2$ automorphic zero density $5/2$).

### 4.3 Generalized Lambert Digit Classifications (Including Mira Cult & Captain Sude Records)
- **Classical irrationality & theta-square baseline:** Erdős (1948, *J. Indian Math. Soc.*) `[R]`; P. B. Borwein (1991, *JNT* **37**; 1992, *MPCPS* **112**) `[A/S]`; Vandehey (2012, `arXiv:1206.0340`) `[S]`; Luca–Tachiya (2014) `[S]`; Hamieh–Murty (2016) `[R]`; Bailey–Crandall (2002, *Exp. Math.*) `[R]`; Bailey–Borwein–Crandall–Pomerance (2004, *JTNB* **16**, §9, Theorem 9.4: $\#_1(\theta_3(1/2)^2, M) \sim C_0 M/\sqrt{\log M}$) `[R]`; Crandall (2012, *Integers* **12**, A23) `[R]`.
- **2026 contemporaries (strictly pinned, zero external contact, zero endorsement):**
  - John M. Campbell (22 May 2026, `arXiv:2605.24160`) `[R]`: `11` infinitely often in $E(2)$.
  - **Captain Sude** (7–13 Sept 2026, 3 pinned Lean 4 repositories) `[R]`: `erdos-borwein-disjunctivity` (`bd98789a`, conditional Lean); `erdos-borwein-disjunctivity-elementary` (`d51e93e9`, unconditional Lean disjunctivity of $E(2)$ with count $\ge N\exp(-70000(\log\log N)^3)$); `generalized-Lambert-disjunctivity-and-nonnormality` (`fe33be21`, nonlinear power-Lambert $\sum (b^{m^r}-1)^{-1}$ for $r \ge 2$ only; excludes linear $r = 1$).
  - **Mira Cult** (Oct–Nov 2026, `Mira-Cult/math` Claim 0002 at `1498319438` and gist S06 `41b5a780f7`) `[R]`: positive lower word density in windows $N^a \le H \le N$ ($a > 7/12$) for $E(2)$ ($k = 1$).
  - Costa Lambrinoudis (2026) `[S]`: AI-assisted Lean proof that $E(2)$ is not a quadratic irrational.
- **Repository placement:** `CC-46`/`CC-48` (Paper VI), `GF-05`/`GF-12`/`GF-21` (leading discrepancy constants for sparse $L_\chi, \Theta_Q$), `GF-22` (disjunctivity for all nonprincipal $\Phi \circ (1*\chi)$), `GF-31`/`GF-36`/`GF-40`/`GF-42`/`GF-44` (dense digit-mass & kernel-verified NAF geometric transfer for $E(2^k), E_+(2^k), L_\pm(2^k)$, completely disjoint from $E(2)$ and $r \ge 2$), and `GF-48` + Phase 26 Track G (moving-window extensions, almost-all windows below $1/2$, leading window constants, and the CRT covering barrier).

### 4.4 Constructive Badly Approximable Normal Numbers
Cross-checked against Phase 25 Track H2 Topic 9 (`notes/phase25/historical-provenance-lambert.md` §Topic 9) and Track F2 (`GF-46`):
- **Non-constructive existence (classical):** Kaufman (1980, *Mathematika* **27**, 262–267: Rajchman measures with polynomial Fourier decay on $F_N$ for $\dim_H(F_N) > 2/3$, hence badly approximable absolutely normal numbers exist; 1981, *Acta Arith.* **39**, 265–267) `[A/S]`; Queffélec–Ramaré (2003, *L'Enseign. Math.* **49**, 335–356: lowers threshold to $\dim_H > 1/2$, covering $F_2$) `[A/S]`; Hochman–Shmerkin (2015, *Invent. Math.* **202**, 427–479: arbitrary finite alphabet $|S| \ge 2$, non-constructive) `[A/S]`; Jordan–Sahlsten (2016) `[S]`.
- **Computable normal / Liouville / CF-normal constructions (NOT badly approximable):** Becher–Heiber–Slaman (2013, *Inform. Comput.* **232**, 1–9: polynomial-time absolutely normal; 2015, *Math. Comp.* **84**, 2939–2952: computable absolutely normal Liouville number) `[A/S]`; Becher–Bugeaud–Slaman (2016, *PAMS* **144**, 1509–1521) `[A/S]`; Scheerer (2015, `arXiv:1511.03582`; 2017: computable absolutely normal and CF-normal, unbounded partial quotients) `[A/S]`; Aistleitner–Becher–Scheerer–Slaman (2017, *Acta Arith.* **180**, 333–346: computable absolutely normal with discrepancy $O(N^{-1/2})$) `[A/S]`.
- **Phase 25–26 relevance (`GF-46`):** `GF-46` supplies explicit computable badly approximable polynomial-absolutely-normal numbers in $F_M$ at $M = 100$ (purely analytic), $M = 42$ (elementary Kloosterman + finite cert), and $M = 14$ (Weil + finite cert). Priority remains provisional pending exhaustive MathSciNet/zbMATH specialist review; lowering the computable cap to $M = 2$ (effectivizing Queffélec–Ramaré) remains open.

### 4.5 Toeplitz Determinants & Orbit Measures (Szegő–Kolmogorov–Krein, Simon *OPUC*)
- **Primary treatises & theorems:** Szegő (1915, 1920, 1952: First and Strong Szegő Limit Theorems for Toeplitz determinants $D_m(\mu) = \det(\widehat{\mu}(j-k))_{0 \le j,k < m}$) `[S]`; Kolmogorov (1941) & Krein (1945): **Szegő–Kolmogorov–Krein theorem**, $\inf_{P(0)=0} \int_{\mathbb{T}} |1 + P(z)|^2 d\mu = \exp(\int_{-\pi}^\pi \log w(\theta)\frac{d\theta}{2\pi})$ where $d\mu = w\frac{d\theta}{2\pi} + d\mu_s$ `[S]`; Grenander–Szegő (1958, *Toeplitz Forms and Their Applications*) `[S]`; **Barry Simon (2005)**, *Orthogonal Polynomials on the Unit Circle*, Parts 1 & 2 (AMS Colloquium Publications Vol. 54, Part 1 Ch. 2 Verblunsky coefficients $\alpha_n$ & Szegő's theorem; Part 2 Chs. 6 & 10 CMV matrices and spectral entropy) `[S]`.
- **Phase 26 connection to radix orbit measures:** For any weak* limit measure $\mu$ of the radix-$b$ orbit measures $\mu_N = N^{-1}\sum_{n < N} \delta_{\{b^n x\}}$ on $\mathbb{T}$, the Toeplitz determinant satisfies the Verblunsky–Szegő identity $D_m(\mu) = \prod_{j=0}^{m-1}(1 - |\alpha_j|^2)^{m-j}$ (Simon, Part 1, Theorem 1.5.11 `[S]`). Full normality ($\mu = \lambda$) corresponds uniquely to $D_m(\mu) = 1$ ($\alpha_j \equiv 0$), whereas if a weak* limit measure is a Dirac mass $\mu = \delta_c$ (which forces $x \in K_b$, though membership $x \in K_b$ does not by itself force every weak* limit measure to be a single Dirac mass), it satisfies $\operatorname{rank} T_m(\mu) = 1$, $D_m(\mu) = 0$ for all $m \ge 2$, and Szegő entropy $-\infty$; intermediate measures $\mu = (1-\gamma)\lambda + \gamma\delta_0$ (realized in `GF-26`/`GF-45`) have strictly positive Szegő ratio $\lim D_{m+1}/D_m = 1 - \gamma$ because the singular atom $\gamma\delta_0$ drops out of the Szegő–Kolmogorov–Krein prediction error! This connects Toeplitz positivity directly to finite Fourier moment obstructions (`CC-49`, `GF-28`) and limit-measure entropy diagnostics (Objective 3).

### 4.6 Padé & Hankel Determinant Methods for Logarithms
- **Historical progression for $\mu(\ln 2)$:** Alladi–Robinson (1980, *J. Reine Angew. Math.* **318**, 137–155: Legendre-polynomial Padé approximants, $\mu(\ln 2) \le 4.622$) `[S]`; Beukers (1979, *Bull. LMS* **11**, 268–272; 1981, LNM **888**, 90–99: hypergeometric integrals for $\zeta(2), \zeta(3), \ln 2$) `[S]`; Rukhadze (1987, *Vestnik Moskov. Univ. Ser. I Mat. Mekh.* **42**, no. 6, 25–29; English transl. *Mosc. Univ. Math. Bull.* **42**, 30–35: Legendre-type polynomial integral $\int_0^1 y^{7t}(1-y)^{7t}(1+y)^{-6t-1}dy$, yielding $\mu(\ln 2) < 3.8913998\ldots$, verified via Marcovecchio `arXiv:2512.12890` p. 2 `[R]` and Waldschmidt `arXiv:math/0312440` `[R]`; also rounded to `3.893` in some citations) `[S]`; Hata (1990, *J. Reine Angew. Math.* **407**, 99–125; 1993, *Acta Arith.* **63**, 335–349: Legendre-type polynomial & $C^2$-saddle-point refinements for $\ln 2$, $\pi$, and other constants) `[S]`; Rhin–Viola (1996, *Acta Arith.* **77**, 23–56; 2001, *Acta Arith.* **97**, 269–293: **method lineage** — permutation-group arithmetic cancellation on Beukers-type multiple integrals developed for $\zeta(2)$ and $\zeta(3)$) `[S]`; Marcovecchio (2009, *Acta Arith.* **139**, 147–184 `[S]`, and 2014, *Int. J. Number Theory* **10**(7), 1829–1855, `arXiv:2512.12890` `[R]`: adapts the Rhin–Viola permutation-group method + multiple Legendre polynomials to $\ln 2$, establishing the record $\mu(\ln 2) \le 3.574553902525\ldots$); Bugeaud (*Distribution Modulo One and Diophantine Approximation*, CUP 2012) `[S]` (Hankel determinants and Padé denominators).
- **Phase 26 connection (`BC-05` $\ln 2$, `CC-02`, `CC-50`, `GF-35`, `GF-40`, `GF-47`):** Padé/Hankel rational approximants $p_n/q_n$ to $\ln 2$ achieve $\mu(\ln 2) \le 3.5746$ (yielding shadowing-length bounds via `CC-50`), yet they cannot directly establish $D^+(\ln 2; 2) < 1$ because their denominators $q_n$ contain the smooth primorial cancellation $\operatorname{lcm}(1, \dots, n)/d_n$ (exponential in $n$) rather than the pure dyadic-plus-small-period BBP structure required by `GF-35`/`GF-47`.

---

## 5. External Inputs and Exact Hypothesis Verification

| Input | Exact Statement Used | Where Used | Label | Hypotheses Verified |
| --- | --- | --- | --- | --- |
| **Dirichlet GRH (`GRH(q_0)`, `Dirichlet GRH`)** | All zeros of $L(s, \chi)$ in $0 < \Re s < 1$ have $\Re s = 1/2$ (machine-verified externally in `lsernau/grh-lean@72fead10`, not peer-reviewed) | Theorems G2.1A, G2.1B(2), G2.2A′, G2.2B, G2.3(2b), Lemma 3.1 | **Conditional / External-GRH** | Named per result: `GRH(q_0)` only for Paper VI (`G2.1A`, `G2.2A′`, `G2.3`); `Dirichlet GRH` for growing $q' = q Q(N, w)$ (`G2.1B`, `G2.2B`). |
| Truncated explicit formula & zero counting (X1)–(X2) | Davenport Chs. 15–19; Montgomery–Vaughan I Ch. 12 | Lemmas 3.1–3.2, Theorem G2.2C | External input (classical) | Primitive $\chi^* \bmod q^*$, $2 \le U \le T$. |
| **Thorner–Zaman (2024)**, *Math. Z.* **306**, Paper No. 54 (`arXiv:2108.10878v2`, Thm. 2.1, eq. (2.1)) `[R]` | Log-free $N_q(\sigma, T) = \sum_{\chi \bmod q} N(\sigma, T, \chi) \ll_\varepsilon (q T)^{(\frac{12}{5} + \varepsilon)(1-\sigma)}$ for $0 \le \sigma \le 1$, $q \ge 2$, $T \ge 1$ (combining Huxley 1975 `[S]` + Jutila 1977 `[R]`) | Lemma 3.2, Theorems G2.2A, G2.2C, G2.2D | External input (published, primary-read `[R]`, unconditional) | Used at $q = q_0$ fixed and $q = q' = X^{o(1)}$, $\sigma \in [\frac{1}{2}, 1 - \eta]$; zero $\varepsilon$-loss outside $(1-\sigma)$! |
| **Jutila (1977)**, *Math. Scand.* **41**, 45–62, **Theorem 1**, eq. (1.7) `[R]` | Log-free $N(\sigma, T, q) = \sum_{\chi \bmod q} N(\sigma, T, \chi) \ll_\varepsilon (q T)^{(2 + \varepsilon)(1-\sigma)}$ for $\frac{4}{5} \le \sigma \le 1$, $T \ge 1$ | Lemma 3.2, Theorem G2.2C, G2.2A/C/D $\sigma$-split at $\frac{4}{5}$ (incl. $4/7$ & $1/7$ addenda) | External input (published, primary-read `[R]`, unconditional) | Used on $[\frac{4}{5}, 1 - \eta]$; eliminates all $(qT)^\varepsilon$ / log-power loss near $\sigma = 1$ for both $A = 12/5$ and $A = 7/3$. |
| **Uniform Vinogradov–Korobov zero-free region** (Montgomery 1971 p. 176 / 1994 Ch. 9 `[S]`; **Khale**, `arXiv:2210.06457v1` `[R]`, *Q. J. Math.* **75**(1) `[S]`, Thm. 1.1 & eq. (1.4)) | Classical non-explicit $\sigma \ge 1 - c'/(\log q + (\log|t|)^{2/3}(\log\log|t|)^{1/3})$ suffices; explicit constants $10.5\log q + 61.5(\log|t|)^{2/3}(\log\log|t|)^{1/3}$ ($|t| \ge 10$, $q \ge 3$) via Khale Thm. 1.1 | Lemma 3.2, Theorems G2.2A, G2.2C, G2.2D | External input (published, primary-read `[R]`, unconditional) | Used for $q' \ge 3$ with $\log q' = O(\log\log N \cdot \log\log\log N) \le (\log N)^{1/2}$ and $10 \le |t| < U$; explicit constants not essential. |
| **Landau–Page** (Davenport Ch. 14) | At most one primitive real $\chi_1 \bmod q_1 \le Q_{\max}$ has a zero in $\sigma \ge 1 - c_0/\log(12 Q_{\max})$, $|t| \le 10$ | Lemma 3.2, Theorems G2.2C, G2.2D | External input (classical, unconditional) | Two disjoint kill families $\mathcal{P}_1, \mathcal{P}_2$ avoid $q_1$ since $\gcd(q_1', q_2') = q$ is fixed. |
| **Shiu (1980)**, Thm. 1 | Short-interval upper bound for multiplicative $g \ge 0$ in progressions ($k < y^{1-\alpha}$, $x^\beta < y \le x$) | Theorems G2.3, G2.4A | External input (classical, unconditional) | Verified $g_t$, $z^{\omega_{S,1}}$, $h_q = 2^{v_q(c)}\mathbf{1}_{c>0}$ (`C5`), $|c_{\chi^\sigma}|^2$ (for all $\sigma \in G$), $\tau^2$ all satisfy $g(p^e) \le A_1^e$ and $g(n) \ll_\varepsilon n^\varepsilon$; $q' = N^{o(1)} < H^{1/2}$ for $H \ge N^a$. |
| **Selberg–Delange** (Tenenbaum Ch. II.5) & **GRH two-sided $\log L$ bound** (Littlewood 1924 / Montgomery–Vaughan Ch. 13) | Hankel contour for $F(s) = \sum \mathbf{1}_{c>0} n^{-s}$ (unconditional zero-free region; under `GRH(q_0)`, $|\log L(\sigma+it, \chi)| \ll_{q_0, c} \log(|t|+3)/\log\log(|t|+3)$ on $\sigma \ge \frac{1}{2} + c/\log\log N$) | Theorem G2.3(2a–2b) | External input (classical) | Used when $S$ is a union of reduced classes mod $q_0$; contour $\sigma_1 = \frac{1}{2} + c/\log\log N$ covers both $\Re(a_\chi) > 0$ and $\Re(a_\chi) < 0$. |
| **Matomäki–Radziwiłł II** (`arXiv:2007.04290`, Jul 2020, Cor. 1) `[R]` & **Hooley (1994)** `[S]` | Almost-all short-interval asymptotic for sparse multiplicative supports $\mathcal{N}$ satisfying (1.2), down to $H/(\log X)^\kappa \to \infty$ (Hooley 1994: order of magnitude for $\chi_{-4}$) | Theorem G2.3(1), G2.3(2c) & §4.1 | External preprint `[R]` (MR II); published `[S]` (Hooley 1994) | Condition (1.2) verified for `(H1)`–`(H4)` with $\alpha = \frac{1}{2\varphi(q_0)}$ via Mertens in APs; Theorem G2.3(2c) strictly separated as preprint-dependent. |
| **Chen–Gupta–Li** (`arXiv:2507.08296v2`, Jul 2026, Thm. 2) `[R]` | $\sum_{\chi \bmod q} N(\sigma, T, \chi) \le (qT)^{o(1)}(q^{\frac{7}{3}(1-\sigma)}T^{2(1-\sigma)} + (qT)^{\frac{30}{13}(1-\sigma)})$ (uniform $A = 7/3$; $T$-aspect $30/13$ when $q = U^{o(1)}$) | Addenda remarks only (G2.2, G2.5) | External unrefereed preprint (`[R]`, NOT used in main theorems) | Paired with Jutila 1977 Thm. 1 `[R]` on $[\frac{4}{5}, 1]$ in the $\sigma$-split; strictly segregated from main unconditional theorems pending peer review. |
| **Repository Lean declarations** | `Phase17DiscrepancyBounds.one_sub_discrepancy_le_one_bits`, `one_sub_discrepancy_ge_of_separated_mass`, `SharpTranslation.sharp_translation_isGreatest`, `CoefficientTransfer.one_sub_discrepancy_ge_of_bulk_and_far`, `RadixWidthLaw.*` | Theorems G2.1A, G2.2A, G2.2A′, G2.3 | Kernel-verified (repository) | All hold unconditionally for every real $y = \{b^N L\}$ and every $H \ge 1$. |
| **Repository paper inputs** | Paper VI (`prop:planting`, `prop:upper`, `lem:selberg`, `lem:small`, `lem:isolated`); `GF-48` (Theorem A, Corollary A.2, Lemma E.2); `GF-12` / `GF-21` (Theorem 1, Theorem B1) | §3.1–§3.4 | Repository inputs (labels preserved) | Every modified hypothesis re-verified line by line. |

---

## 6. Evidence Labels and Ledger

- **Lean-supported paper proof (unconditional, new, unreviewed; published primary-verified inputs):** Theorem G2.2A (Paper VI almost-all-window word counts & $R$-isolated planting, $1/6 < a \le 1$); Theorem G2.3(1) (self-normalized exact window leading constant) and Theorem G2.3(2a) (unconditional all-window explicit `GF-12` constant on $N\exp(-c_1\sqrt{\log N}) \le H \le N$). Finite discrepancy/width cores are existing repository Lean declarations.
- **Paper proof (unconditional, new, unreviewed; published primary-verified inputs):** Theorem G2.1B(1) ($H = \sqrt{N}(\log N)^C$ method barrier for `GF-22`'s CRT construction); Lemma 3.2; Lemma 3.3; Theorem G2.2C (`GF-22` all windows $7/12 < a \le 1$); Theorem G2.2D (`GF-22` almost-all windows $1/6 < a \le 1$); Theorem G2.4A (universal Galois-conjugate second-moment Shiu halving of `GF-22` CRT exponent, strict log-convexity at $t = 2$, and Fourier proof of $\alpha_*(\chi) < 1$); Theorem G2.4B(1)–(2) & Lemma 3.4 (single-CRT-class and arbitrary-union zero-block covering barriers for odd-order characters).
- **Preprint-input paper proof (unconditional, zero GRH; depends on unrefereed arXiv preprint):** Theorem G2.3(2c) (almost-all-window explicit `GF-12` constant for every fixed $a > 0$, using Matomäki–Radziwiłł II `arXiv:2007.04290` Corollary 1 `[R]`); and the `4/7`/`1/7` (resp. `17/30`/`2/15`) addenda to G2.2A/C/D using Chen–Gupta–Li `arXiv:2507.08296v2` `[R]` paired with Jutila 1977 `[R]`.
- **Conditional / External-GRH (written deductions from `GRH(q_0)` or `Dirichlet GRH` — machine-verified externally in `lsernau/grh-lean@72fead10`, not human peer-reviewed, NOT kernel-verified in this repository):** Lemma 3.1; Theorem G2.1A (Paper VI at $H = \sqrt{N}(\log N)^C$, $C > 2$, and $C = 2$ endpoint); Theorem G2.1B(2) (`GF-22` at $\sqrt{N}\exp(C_0\log\log N\cdot\log\log\log N)$); Theorem G2.2A′ (Paper VI almost-all-window word counts & planting for $H = X^\theta$ and $(\log X)^{2+\varepsilon}$); Theorem G2.2B (`GF-22` almost-all windows $\exp(C_1\log\log X\cdot\log\log\log X)$); Theorem G2.3(2b) (all-window explicit `GF-12` constant down to $\sqrt{N}\exp(C_2\log N/\log\log N)$).
- **Finite certificate (`[exact]`):** `18,955` pure `int`/`Fraction` substantive mathematical checks in [`scripts/phase26_grh_windows.py`](../../scripts/phase26_grh_windows.py) (zero floating-point locals across all frames): exact outward rational enclosures for $\ln b$, $\delta^*_b$, $d/\ln b$; exact geometric tail identity; 360-point $C > 2$ and 59-point $C \in (-1, 2]$ far-tail budgets; 1,500-point G2.2A/A′ grids and 800-point two-regime $\sigma$-split checks at $\sigma_0 = 4/5$ and $1 - \eta$ (for both $A = 12/5$ and $A = 7/3$, all-window and almost-all); $h_q$ valuation bound; exact $h = 5$ Galois-conjugate trace-duality bound ($K_{\Phi_0} = 2/5$, $\det M = 125$, all $4$ coordinates across $1 \le k \le 40$) and counterexample certification; exact integer proofs of $g_3(21/10) < 1$ and $g_2(3/2) < 0.95$; Fourier sign proof of $\kappa'_2(h) \ne 1$ for $2 \le h \le 60$; certified $P(2) \in [0.452238, 0.452338] < 1/2$, $P_{\mathcal{P}'}(2) \in [0.422597, 0.422697]$, single-CRT vs. union-bound exponent bounds, and concrete covering-congruence $\log_2 Q_{\min}$ lower bounds.
- **Consistency checks (`[consistency]`):** `127` pure `int`/`Fraction`/string bookkeeping & sanity checks honestly separated from `[exact]` certificates (`C1` file/declaration partitions & hex SHA format checks, `C2` part 3 illustrative $C_2 = 10$ check, `C3` scaling sanity checks, `C4` Khale `61.5 + 0.5 = 62`, `C6` part 1 $\mathbb{Q}[x]/(x^h - 1)$ coefficient bookkeeping).
- **Finite illustrations (`[finite]`, NOT asymptotic evidence):** `C7` (`19` isolated numeric checks: $\alpha_*(h)$ grid search for $h \in \{2, 3, 4, 5, 6, 7, 12\}$ and illustrative `L_+(2)` CRT digit-count reduction at $\log_{10} N \in \{10, 10^2, 10^3, 10^4, 10^6\}$).
- **Open:** §9.

---

## 7. Reproduction Instructions

Run on Windows (or Linux) with Python 3 (standard library only; no WSL):

```sh
python -B scripts/phase26_grh_windows.py
```

Expected output (verified exit code `0`, runtime $\approx 0.3\text{ s}$):
```text
ALL 19101 CHECKS PASSED (18955 exact, 127 consistency, 19 finite)
```

No existing repository file, Lean module, registry entry, or benchmark file was edited or depends on this script.

---

## 8. Exact Finite Tests and Consistency Checks (`scripts/phase26_grh_windows.py`)

Checks are strictly partitioned into **`[exact]`** (substantive `int`/`Fraction` mathematical certificates, runtime-verified zero float locals), **`[consistency]`** (bookkeeping, format, and illustrative-parameter sanity checks), and **`[finite]`** (isolated floating-point illustrations, never asymptotic evidence):

1. **`C1 [consistency]` (G1 primary-source verification accounting):** Bookkeeping partitions (`495 + 306 + 2 = 803` for `grh/`, `573 + 219 + 2 = 794` for `grh-compact/`), rational compression ratios from transcribed line counts (`99.5097% > 99.50%` compact; `98.0691% > 98.06%` readable), declaration accounting (`216,571 - 216,568 = 3` and `204,583 - 204,580 = 3`; `165,163 + 51,408 = 216,571`; `165,163 + 39,420 = 204,583`; `39,482 + 10,750 = 50,232`), and hexadecimal **format** checks for all pinned SHA strings (the SHA *values* themselves were verified directly against GitHub API).
2. **`C2 [exact + consistency]` (Theorem G2.1A budgets):** `[exact]` verifies $\sum_{j=J+1}^{J+M} j 2^{-j} = (J+2)2^{-J} - (J+M+2)2^{-(J+M)}$ across $816$ exact `Fraction` pairs; checks prime-supply and Lemma-E.2 far-tail margins across `360` values $C \in (2, 20]$ (both the necessary `< 0` bound and the `< -1` margin) plus `59` values $C \in (-1, 2]$ confirming the far tail is never the bottleneck; checks Rankin's $2\delta - 2\log 2 < \delta$ across $\delta \in (0, 1)$. `[consistency]` checks the illustrative $C_2 = 10$ squared threshold $K^2 > 32 C_2^2 \varphi(q_0)^2 p_0^{2u}$ at $C = 2$.
3. **`C3 [exact + consistency]` (Theorems G2.1B & G2.2B `GF-22` thresholds):** `[exact]` computes certified outward rational enclosures of $d/\log b$ for $(d, b) \in \{2, 3, 4, 5\} \times \{2, 3, 5, 10\}$ (e.g., cubic $L_\pm(2)$: $3/\log 2 \in [4.328085, 4.328085]$ vs. Phase 25's $6/\log 2 \in [8.656170, 8.656170]$). `[consistency]` checks Step 5′ vs. Step 6′ $(\log N)^3$ dominance and $2 C_0 = C_1$ algebraic scaling.
4. **`C4 [exact + consistency]` (Theorems G2.2A–D zero-density, two-regime $\sigma$-split & almost-all grids):** `[exact]` verifies $A \mapsto (1 - 1/A, 1 - 2/A)$ across Ingham (`8/3`), Montgomery (`5/2`), Huxley + Jutila (`12/5`), Chen–Gupta–Li (`7/3`), Guth–Maynard (`30/13`), and Density Hypothesis (`2`); checks strict ordering chains; checks every parameter inequality across `500` grid points each for G2.2A ($A = 12/5, 7/3$) and G2.2A′; and verifies the **two-regime $\sigma$-split at $\sigma_0 = 4/5$ ($c_0 = 1/5$) and $\sigma = 1 - \eta$** (bulk absorption of $(q'T)^{\varepsilon'}$ by $U^{-\frac{3}{4}\gamma c_0}$ AND Jutila's log-free $(2 + \varepsilon'')(1-\sigma)$ near $\sigma = 1$, plus Thorner–Zaman's full-strip log-free bound for $A = 12/5$) across `200` grid points each for both $A = 12/5$ and $A = 7/3$ in both all-window and almost-all regimes. `[consistency]` checks Khale's `61.5 + 0.5 = 62` bookkeeping.
5. **`C5 [exact]` (Theorem G2.3 window leading constants):** Exact outward rational enclosures of $\delta^* = 1/(1+\log 2) \in (0.5906, 0.5907)$ and `GF-21` even-composite jumps $\delta^*_6 \in (0.7017, 0.7018)$, $\delta^*_{10} \in (0.6736, 0.6737)$, $\delta^*_{12} \in (0.7654, 0.7655)$ (noting that `docs/registry/GF.toml:381` has a prose transcription slip for $\beta_b$ while `notes/phase22/radix-thresholds-and-class-groups.md:8` has the exact $\beta_b = \log b/\log b'$); verifies the Shiu prime-power bound $2^{v_q(c(p^e))} \le e + 1 \le 2^e$ specifically for $h_q$ ($q \in \{3, 5, 7, 11, 13\}$, $1 \le e \le 500$).
6. **`C6 [exact + consistency]` (Theorems G2.4A & G2.4B):**
   - `[consistency]` verifies the $\mathbb{Q}[x]/(x^h - 1)$ coefficient bookkeeping of $\sum_{j=0}^{h-1}(2 + x^j + x^{h-j}) - 2\sum x^r = 2h$ for $2 \le h \le 60$.
   - `[exact]` **Galois-conjugate trace-duality test at $h = 5$ ($\varphi(5) = 4$):** computes exact $\det(\operatorname{Tr}(\zeta_5^{i+j})) = 125 = 5^3$, solves for all four dual elements $\beta_{\Phi_r} \in \mathbb{Q}(\zeta_5)$ (certifying $\beta_{\Phi_0} = \frac{1 - \zeta_5}{5}$ and $K_{\Phi_0} = \operatorname{Tr}(\beta_{\Phi_0}\overline{\beta_{\Phi_0}}) = \frac{2}{5}$), and verifies in exact `int`/`Fraction` arithmetic across $z_k = (1 + \zeta_5^2)^k$ ($1 \le k \le 40$) BOTH the exact trace identity $\Phi_r(z_k) = \operatorname{Tr}(\beta_{\Phi_r} z_k)$ and the Galois-conjugate Cauchy–Schwarz bound $|\Phi_r(z_k)|^2 \le K_{\Phi_r}\operatorname{Tr}(z_k\overline{z_k})$ for all $r \in \{0, 1, 2, 3\}$, while simultaneously certifying the failure of naive $|\Phi_0(z_k)| \le |z_k|$ ($|\Phi_0(z_k)| = 8, 89, 10946, 165580141$ at $k = 5, 10, 20, 40$, with $|z_{40}|^2 < (39/100)^{40} < 10^{-16}$ vs. $|\Phi_0(z_{40})|^2 > 10^{16}$).
   - `[exact]` integer proofs of $g_3(21/10) < 1$ and $g_2(3/2) < 0.95$, plus exact Fourier-series sign checks certifying $\kappa'_2(h) \ne 1$ for $2 \le h \le 60$.
   - `[exact]` certified outward rational enclosures $P(2) \in [0.452238, 0.452338] < 1/2$ and $P_{\mathcal{P}'}(2) \in [0.422597, 0.422697]$ (cubic mod 7), single-CRT exponent $3(1 - P_{\mathcal{P}'}(2)) > 1.731909$, union-bound exponent $(1 - P_{\mathcal{P}'}(2))/2 > 0.288651$ (universal $(1 - P(2))/2 > 0.273831$), and concrete covering-congruence lower bounds (noting explicitly $m(10) = 5 = L/2$ at $L = 10$ and $m(L) > L/2$ for $L \ge 20$):

   | $L$ | small primes $p \le \sqrt{L}$ in $\mathcal{P}'$ | max covered by small $p$ | min distinct large $p > \sqrt{L}$ | $\log_2 Q_{\min} \ge$ |
   | --- | --- | --- | --- | --- |
   | 10 | 2 | 5 | 5 | 55 |
   | 20 | 2 | 9 | 11 | 155 |
   | 50 | 3 | 22 | 28 | 524 |
   | 100 | 3 | 43 | 57 | 1,248 |
   | 200 | 4 | 85 | 115 | 2,925 |
   | 500 | 6 | 212 | 288 | 8,639 |
   | 1000 | 8 | 424 | 576 | 19,246 |

7. **`C7 [finite]` (Isolated numerical illustrations — NOT asymptotic evidence):** Optimal Shiu moment $\alpha_*(h) = \inf_{t \ge 1} \kappa_t(h)/t$ ($0.942085$ at $h=2$, $0.997932$ at $h=3$, $0.999311$ at $h=4$, $0.999916$ at $h=5$, $0.999947$ at $h=6$, $0.999989$ at $h=7$, $0.999999$ at $h=12$, with $t_* < 2$ for even $h$ and $t_* > 2$ for odd $h$ matching Step 3 of Theorem G2.4A); illustrative `L_+(2)` CRT $\log_{10} q'$ drop from Phase 25 ($L_{\mathrm{old}}$) to Theorem G2.4A ($L_{\mathrm{new}}$):

   | $\log_{10} N$ | $L_{\mathrm{old}}$ | $\log_{10} q'_{\mathrm{old}}$ | $L_{\mathrm{new}}$ | $\log_{10} q'_{\mathrm{new}}$ | ratio |
   | --- | --- | --- | --- | --- | --- |
   | $10$ | 25 | 221.0 | 20 | 184.1 | 0.833 |
   | $10^2$ | 30 | 270.1 | 22 | 206.3 | 0.764 |
   | $10^3$ | 37 | 339.7 | 25 | 238.1 | 0.701 |
   | $10^4$ | 43 | 404.2 | 29 | 280.2 | 0.693 |
   | $10^6$ | 57 | 556.4 | 35 | 342.7 | 0.616 |

---

## 9. Open Questions

1. **Full order $H/(\log N)^\kappa$ on $H = \sqrt{N}(\log N)^C$ under `GRH(q_0)`:** Theorem G2.1A achieves $H(\log\log N)^\delta/\log N$ on $H = \sqrt{N}(\log N)^C$ ($C > 2$) for Paper VI. Can a non-planted-prime method (or a pair-correlation / Montgomery conjecture refinement of Littlewood's Lindelöf bound) establish the full support asymptotic $S(N, H) \sim C_f H/(\log N)^\kappa$—and hence the exact `GF-12` window constant—at $H = \sqrt{N}(\log N)^C$?
2. **Unconditional polynomial-window explicit constant $C_\chi$ on EVERY window for $L_\chi$:** Theorem G2.3(1) proves the exact self-normalized window constant unconditionally on all windows $a > 0.53$, and Theorem G2.3(2c) gives the explicit `GF-12` constant on **almost all** windows for every fixed $a > 0$ (via Matomäki–Radziwiłł II `arXiv:2007.04290`), whereas Part 2(a)'s **every-window** explicit $C_\chi$ stops unconditionally at $N\exp(-c_1\sqrt{\log N})$ because of fractional-power branch cuts in $F(s) = \sqrt{\zeta(s)L(s,\chi)}G(s)$. Can half-dimensional sieve asymptotics (Iwaniec / Plaksin / Harman) establish $S(N, H) \sim C_\chi H/\sqrt{\log N}$ unconditionally on **every** polynomial window $H = N^a$ ($a < 1$)?
3. **Unconditional almost-all-window word counts for Paper VI below $1/6$:** Can a Harman-sieve almost-all prime lower bound in a fixed arithmetic progression (extending Jia 1996's $1/20$ from $q_0 = 1$ to $q_0 \ge 3$) push Theorem G2.2A's word-count / $R$-isolated planting exponent below $1/6$ unconditionally?
4. **Breaking the zero-block $\exp(-c\log\log N\cdot\log\log\log N)$ barrier for cubic $L_\pm(b)$:** Theorem G2.4B(1)–(2) now rules out **every** method that relies on detecting long zero blocks $\mathcal{Z}_\chi(L) = \{c_\chi(n+1) = \dots = c_\chi(n+L) = 0\}$ of length $L \ge c\log_b\log N$ (both single CRT congruence systems and arbitrary unions of CRT classes / squarefull inclusion–exclusion sieves counting all zero blocks simultaneously). Can either (a) a Mira-Cult-style multi-bank local-limit theorem incorporating the mod-6 phase $\varepsilon_\pm(t(n))$, or (b) a **zero-block-free** (or short-block $L = o(\log\log N)$) construction exploiting atypically small or cancelling signed tail coefficients $c_\Phi(n+j)$, reach $H/(\log N)^C$ or positive lower word density for $L_\pm(2)$?
5. **Hybrid Bombieri–Vinogradov analogue of Guth–Maynard / Chen–Gupta–Li:** Does a $Q$-averaged (hybrid) extension of `arXiv:2507.08296v2` yield a short-interval Bombieri–Vinogradov theorem with positive level of distribution below $\vartheta = 7/12$, which would lower Mira Cult's unconditional exponent for $E(2)$?
6. **Lean 4 formalization of the explicit-formula bridge in progressions:** While `AndrewVSutherland/schoenfeld-rh-lean` formalizes RH $\iff$ Schoenfeld's bound for $q = 1$, formalizing `DirichletLZerosOnLine` $\implies$ Theorem A for $\psi(x; q, u)$ inside Lean 4 would make the conditional analytic bridge itself mechanically checkable (still strictly separated from unconditional theorems).
7. **Registry erratum check (for future owner-authorized update):** `docs/registry/GF.toml:381` (`GF-21`) prints $\beta_b = (1 - 1/v_2(b))\log b + \log 2$ in prose, whereas the proved formula in `notes/phase22/radix-thresholds-and-class-groups.md:8` is $\beta_b = \log b / \log b'$; this note does not modify `GF.toml`.

---

## 10. Standing Objectives Advanced

- **Objective 1 (establish normality):** none.
- **Objective 2 (establish nonnormality & disjunctivity):**
  - **Unconditional** moving-window disjunctivity for `GF-22` (every nonprincipal $\Phi \circ (1*\chi)$, every base $b \ge 2$) upgraded from $N\exp(-c_3\sqrt{\log N})$ to **every window $a > 7/12$** (Theorem G2.2C) and **almost all windows $a > 1/6$** (Theorem G2.2D), with the $t = 2$ CRT exponent cut in half universally via the Galois-conjugate second-moment Shiu reduction (Theorem G2.4A).
  - **Unconditional** almost-all-window word counts, $R$-isolated planting, and disjunctivity for Paper VI below $1/2$, down to **$a > 1/6$** (Theorem G2.2A).
  - **Conditional / External-GRH** window disjunctivity pushed to **$H = \sqrt{N}(\log N)^C$ ($C > 2$; $C = 2$ endpoint)** for Paper VI (Theorem G2.1A), to **$\sqrt{N}\exp(C_0\log\log N\cdot\log\log\log N)$** ($C_0 > d/\log b$, threshold of the $t = 2$ CRT method) for `GF-22` (Theorem G2.1B), and on almost all windows down to **$H = (\log X)^{2+\varepsilon}$** for Paper VI (Theorem G2.2A′) and **sub-polynomial $X^{o(1)}$** for `GF-22` (Theorem G2.2B).
- **Objective 3 (quantify digit distributions):**
  - Exact self-normalized leading window discrepancy constant matching `GF-12` across all radices $b = 2^k$ and all sub-threshold $b \ne 2^k$ ($\delta \le \delta^*_b$), unconditionally on all windows $a > 0.53$, almost all windows $a > 1/6$ (Theorem G2.2A), and almost all windows $a > 0$ (Hooley 1994 for $\chi_{-4}$; MR II `arXiv:2007.04290` for all `(H1)`–`(H4)`); explicit `GF-12` constants unconditionally on all windows $N\exp(-c_1\sqrt{\log N}) \le H \le N$, unconditionally on almost all windows for every fixed $a > 0$ via MR II (`arXiv:2007.04290` preprint), and under `GRH(q_0)` on all windows $\sqrt{N}\exp(C_2\log N/\log\log N) \le H \le N$ (Theorem G2.3).
  - Full-order almost-all window discrepancy gap $1 - D_{N,H}(L) \asymp (\log\log X)/(\log X)^\kappa$ unconditionally for $a > 1/6$ and under `GRH(q_0)` for every $\theta > 0$.
- **Objective 4 (rigorous mathematical limitations):**
  - Single-CRT-class ($\log Q \ge d_{\min}(1 - P_{\mathcal{P}'}(2) - o(1))L\log L$) AND arbitrary-union ($\overline{d}(\mathcal{Z}_\chi(L)) \le \exp(-\frac{1 - P_{\mathcal{P}'}(2) - o(1)}{2} L\log L)$) zero-block covering barriers for odd-order characters via $P(2) < 1/2$ (Theorem G2.4B & Lemma 3.4), proving why no method relying on zero blocks of length $L \ge c\log_b\log N$ (neither a single CRT congruence system, nor an arbitrary union of CRT classes, nor a Paper-VI-style squarefull/Selberg sieve) can reach $H/(\log N)^C$ or positive density for cubic $L_\pm(b)$.
  - Method barrier showing $H = \sqrt{N}(\log N)^C$ fails for `GF-22`'s CRT construction for every fixed $C > 0$ (Theorem G2.1B(1)), and exact $C = 2$ / $M = N^\theta$ limitations for Paper VI planting (Theorem G2.1A).
  - Exact scope boundary of `lsernau/grh-lean@72fead10` (Dirichlet $L$-functions only; no ERH/Hecke/automorphic $L$-functions) and exact $q_0 = 1$ boundary of BHP `0.525` and Guth–Maynard `17/30`.
- **Benchmarks:** Zero status changes on `BC-01`…`BC-50` or `BF-*`.

---

## References

- K. Alladi, M. L. Robinson, Legendre polynomials and irrationality, *J. Reine Angew. Math.* **318** (1980), 137–155 `[S]`.
- L. Alpöge, *Remark* (announcement of Lean 4 formalization of RH and Dirichlet GRH with Claude, 20 November 2026), `https://alpo.ge/remark.pdf` `[R]`.
- D. H. Bailey, J. M. Borwein, R. E. Crandall, C. Pomerance, On the binary expansions of algebraic numbers, *J. Théor. Nombres Bordeaux* **16** (2004), 487–518 `[R]`.
- R. C. Baker, G. Harman, J. Pintz, The exceptional set for Goldbach's problem in short intervals, CUP (1997), 1–54 `[S]`; The difference between consecutive primes, II, *Proc. LMS* **83** (2001), 532–562 `[S]`.
- V. Becher, P. A. Heiber, T. A. Slaman, *Inform. Comput.* **232** (2013), 1–9; *Math. Comp.* **84** (2015), 2939–2952 `[A/S]`.
- F. Beukers, *Bull. LMS* **11** (1979), 268–272; LNM **888** (1981), 90–99 `[S]`.
- P. B. Borwein, *J. Number Theory* **37** (1991), 253–259; *Math. Proc. Camb. Phil. Soc.* **112** (1992), 141–146 `[A/S]`.
- J. M. Campbell, On the binary digits of the Erdős–Borwein constant, `arXiv:2605.24160` (2026) `[R]`.
- Captain Sude, pinned Lean 4 repositories (`bd98789a`, `d51e93e9`, `fe33be21`, Sept 2026) `[R]`.
- B. Chen, V. Gupta, Y. C. Li, Large value estimates for Dirichlet polynomials with characters and zero density of Dirichlet $L$-functions, `arXiv:2507.08296v2` (Jul 2026, unrefereed preprint) `[R]`.
- C. Cossaboom, Zero density estimates for $\mathrm{GL}_2$ automorphic $L$-functions, `arXiv:2609.27715` (Sep 2026) `[A]`.
- H. Davenport, *Multiplicative Number Theory*, 2nd/3rd ed., Springer GTM 74 `[R/S]`.
- P. Erdős, On arithmetical properties of Lambert series, *J. Indian Math. Soc.* **12** (1948), 63–66 `[R]`.
- P. X. Gallagher, A large sieve density estimate near $\sigma = 1$, *Invent. Math.* **11** (1970), 329–339 `[S]`.
- L. Guth, J. Maynard, New large value estimates for Dirichlet polynomials, `arXiv:2405.20552v2` `[R]` (*Ann. of Math.* **203** (2026), no. 2, 623–675 `[S]`).
- M. Hata, *J. Reine Angew. Math.* **407** (1990), 99–125; *Acta Arith.* **63** (1993), 335–349 `[S]`.
- M. Hochman, P. Shmerkin, Equidistribution from fractal measures, *Invent. Math.* **202** (2015), 427–479 `[A/S]`.
- C. Hooley, On the intervals between numbers that are sums of two squares, *Acta Math.* **127** (1971), 279–297; II, *J. Number Theory* **5** (1973), 215–217; III, *J. Reine Angew. Math.* **267** (1974), 207–218; IV, *J. Reine Angew. Math.* **452** (1994), 79–109 `[S]`.
- M. N. Huxley, *Invent. Math.* **15** (1972), 164–170; *Acta Arith.* **24** (1973), 329–346; **26** (1975), 435–444; **27** (1975), 159–169 `[S]`.
- C. H. Jia, Almost all short intervals containing prime numbers, *Acta Arith.* **76** (1996), 21–84 `[S]`.
- M. Jutila, On Linnik's constant, *Math. Scand.* **41** (1977), 45–62 (Theorem 1, eq. (1.7)) `[R]`; Zero-density estimates for $L$-functions, *Acta Arith.* **32** (1977), 55–62 `[S]`.
- R. Kaufman, *Mathematika* **27** (1980), 262–267; *Acta Arith.* **39** (1981), 265–267 `[A/S]`.
- T. Khale, An explicit Vinogradov–Korobov zero-free region for Dirichlet $L$-functions, `arXiv:2210.06457v1` `[R]` (*Q. J. Math.* **75** (2024), no. 1, 299–332 `[S]`).
- A. Kumchev, The difference between consecutive primes in an arithmetic progression, *Q. J. Math.* **53** (2002), 479–501 `[R]`.
- Le Duc Hieu, Arithmetic progressions of primes in short intervals beyond the $17/30$ barrier, `arXiv:2509.04883v2` (2025) `[A]`.
- Lean FRO & Mathlib Initiative, *Lean verification of the Riemann Hypothesis* (21 November 2026), `https://leanprover-community.github.io/blog/posts/riemann-hypothesis/` `[R]`.
- R. Marcovecchio, The Rhin–Viola method for $\log 2$, *Acta Arith.* **139** (2009), 147–184 `[S]`; Multiple Legendre polynomials in Diophantine approximation, *Int. J. Number Theory* **10** (2014), no. 7, 1829–1855 (`arXiv:2512.12890v1`) `[R]`.
- K. Matomäki, M. Radziwiłł, Multiplicative functions in short intervals, *Ann. of Math.* **183** (2016), 1015–1056 `[A/S]`; Multiplicative functions in short intervals II, `arXiv:2007.04290` (Jul 2020, preprint) `[R]`.
- Mira Cult, `Mira-Cult/math` Claim 0002 (commit `149831943806a656c9efaa14cacbd9c915b2a2ba`, 23 Nov 2026) and gist S06 (`41b5a780f7`, Oct 2026) `[R]`.
- H. L. Montgomery, *Topics in Multiplicative Number Theory*, LNM 227 (1971); *Ten Lectures on the Interface Between Analytic Number Theory and Harmonic Analysis*, CBMS 84 (1994); H. L. Montgomery, R. C. Vaughan, *MNT I*, CUP (2007) `[R/S]`.
- A. Perelli, J. Pintz, S. Salerno, *Ann. Sc. Norm. Super. Pisa* **11** (1984), 529–539; *Invent. Math.* **79** (1985), 1–9 `[R]`.
- M. Queffélec, O. Ramaré, *L'Enseign. Math.* **49** (2003), 335–356 `[A/S]`.
- G. Rhin, C. Viola, *Acta Arith.* **77** (1996), 23–56; **97** (2001), 269–293 `[S]`.
- M. Rubinstein (University of Waterloo), *Alpöge/Claude proof of the Generalized Riemann Hypothesis* and verification logs (`math.uwaterloo.ca/~mrubinst/alpoge_claude_grh/`, `mrubinst.github.io/grh-lean-verification/`, `grh-lean-compact-check/`, Nov 2026) `[R]`.
- E. A. Rukhadze, Lower estimate for rational approximations of $\ln 2$, *Vestnik Moskov. Univ. Ser. I Mat. Mekh.* **42** (1987), no. 6, 25–29 (English transl. *Mosc. Univ. Math. Bull.* **42** (1987), 30–35) `[S]`.
- A.-M. Scheerer, `arXiv:1511.03582` (2015) `[A/S]`; C. Aistleitner, V. Becher, A.-M. Scheerer, T. A. Slaman, *Acta Arith.* **180** (2017), 333–346 `[A/S]`.
- A. Selberg, On the normal density of primes in small intervals, and the difference between consecutive primes, *Arch. Math. Naturvid.* **47** (1943), 87–105 `[S]`.
- L. Sernau (with Anthropic / Claude), `lsernau/grh-lean` at commit `72fead102f663d5c7a407964a13dc0cf9d977207` (25 November 2026) `[R]`.
- P. Shiu, A Brun–Titchmarsh theorem for multiplicative functions, *J. Reine Angew. Math.* **313** (1980), 161–170 `[R]`.
- B. Simon, *Orthogonal Polynomials on the Unit Circle*, Parts 1 & 2, AMS Colloquium Publications Vol. 54 (2005) `[S]`.
- A. V. Sutherland (MIT), Verification files for the Lean proof of RH / shorter GRH proof (`math.mit.edu/~drew/grh/`, `math.mit.edu/~drew/shortgrh/`, updated 27 Nov 2026) `[R]`.
- G. Tenenbaum, *Introduction to Analytic and Probabilistic Number Theory*, 3rd ed., CUP (2015) `[S]`.
- J. Thorner, A. Zaman, Refinements to the prime number theorem for arithmetic progressions, *Math. Z.* **306** (2024), no. 3, Paper No. 54 (`arXiv:2108.10878v2`, DOI `10.1007/s00209-023-03414-3`) `[R]`; An explicit version of Bombieri's log-free density estimate and Sárközy's theorem for shifted primes, *Forum Math.* **36** (2024), no. 4, 1059–1080 (`arXiv:2208.11123v4`, DOI `10.1515/forum-2023-0091`) `[R]`.
- C. L. Turnage-Butterbaugh, A decades-long breakthrough in zero-density estimates and primes in short intervals, `arXiv:2607.04632` (Jul 2026) `[A]`.
- M. Waldschmidt, Diophantine analysis, `arXiv:math/0312440` (2003) `[R]`.
