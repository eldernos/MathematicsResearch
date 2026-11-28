# Arithmetic Hankel Determinants for $\ln 2$: Prime-Centered Poles, Rank-Sensitive Local Denominators, Uvarov–Christoffel Reduction, Reset Limitations and Extensions

Phase 26, Track B (`B1`–`B7`). Continues Phase 25 Track G ([`classical-constants-frontier.md`](../phase25/classical-constants-frontier.md), `GF-47`), Phase 24 Track E ([`classical-constants-and-joint-numerators.md`](../phase24/classical-constants-and-joint-numerators.md), `GF-40`), Phase 23 Track E ([`classical-correlations-and-log2.md`](../phase23/classical-correlations-and-log2.md), `GF-35`), Phase 22 Track E ([`classical-targets-and-recon.md`](../phase22/classical-targets-and-recon.md), `GF-28`), and the kernel-verified BBP/factorial entries [`CC-03`](../../docs/results.md#cc-03), [`CC-08`](../../docs/results.md#cc-08), [`CC-09`](../../docs/results.md#cc-09), [`CC-11`](../../docs/results.md#cc-11). Companion exact verification script: [`scripts/phase26_hankel_ln2.py`](../../scripts/phase26_hankel_ln2.py).

---

## 0. Definitions, notation, evidence labels and scope

**BBP rational states of $\ln 2$.** Set $s_0 = 0$ and for $n \ge 1$,

```math
s_n = \sum_{j=1}^{n} \frac{2^{n-j}}{j} = \frac{A_n}{Q_n} \quad (\gcd(A_n, Q_n) = 1,\ Q_n \ge 1),
```

matching `NormalityChecker.logPrefix` (`CC-03`, `CC-10`) and `GF-47` §0. They obey $s_{n+1} = 2 s_n + \frac{1}{n+1}$ and $2^n \ln 2 = s_n + T_n$, where

```math
T_n = \sum_{k=1}^{\infty} \frac{1}{(n + k) 2^k} = \int_0^1 \frac{t^n}{2 - t}\,dt \in \left(\frac{1}{n + 2},\ \frac{1}{n + 1}\right) \subset \left(\frac{1}{2(n + 1)},\ \frac{1}{n + 1}\right).
```

Write $x_n = \{s_n\} \in \mathbb{Q}/\mathbb{Z}$ and $\|u\| = \operatorname{dist}(u, \mathbb{Z})$. For $x \in \mathbb{Q} \setminus \{0\}$ and a prime $q$, $v_q(x) \in \mathbb{Z}$ is the $q$-adic valuation, $e_q(x) = \max(0, -v_q(x))$ is the $q$-pole order (the exponent of $q$ in the reduced denominator $\operatorname{den}(x)$), and $\mathbb{Z}_{(q)} = \{x \in \mathbb{Q} : v_q(x) \ge 0\}$ is the discrete valuation ring of $q$-integral rationals. For $N \ge 1$, $L_N = \operatorname{lcm}(1, 2, \dots, N)$ and $\psi(x) = \sum_{q^j \le x} \log q = \log L_{\lfloor x \rfloor}$ is the second Chebyshev function. Throughout, $\log$ denotes the natural logarithm.

**Prime-centered Hankel matrix.** Given a prime $p$, an integer dimension $1 \le r \le p$, starting index $M = p - r + 1 \ge 1$, and integers $m_n \in \mathbb{Z}$ ($M \le n \le M + 2r - 2 = p + r - 1$), define the $r \times r$ Hankel matrix $H$ (indexed $0 \le i, j < r$) by

```math
H_{i,j} = s_{M + i + j} - m_{M + i + j}.
```

Write $\Delta m_n = m_n - 2 m_{n-1}$ and $\Delta^2 m_n = m_n - 4 m_{n-1} + 4 m_{n-2}$. When $m_{M+k} = 2^k m_M$ for all $0 \le k \le 2r - 2$ (a **clean window**), we write $H_c$ for $H$ and $\varepsilon = 2^M \ln 2 - m_M$.

**Moment and Cauchy matrices.** For $M \ge 0$ and $r \ge 1$, define the $r \times r$ symmetric matrices ($0 \le i, j < r$)

```math
K(M, r)_{i,j} = T_{M + i + j} = \int_0^1 \frac{t^{M + i + j}}{2 - t}\,dt, \qquad C(M, r)_{i,j} = \int_0^1 t^{M + i + j}\,dt = \frac{1}{M + 1 + i + j},
```

and $v = (1, 2, 4, \dots, 2^{r-1})^T \in \mathbb{Z}^r$. Write $C'(M, r) = C(M - 1, r)$ ($M \ge 1$), so $C'(M, r)_{i,j} = \frac{1}{M + i + j}$. For a real symmetric matrix relation, $A \prec B$ (resp. $A \preceq B$) denotes Loewner strict (resp. weak) positive-definite order ($B - A$ positive definite / semidefinite).

**GF-47 drop set.** For an odd prime $q$, $D(q) = \{1 \le m < q : q \mid A_m\}$ (`GF-47` Lemma 3.3).

**Overloaded symbols.** $M = p - r + 1$ is the Hankel window start throughout §§1–6 (and $M = k_0(p) - r + 1$ in §7); in §5, $M_i = \prod_{n_i/2 < q \le n_i} q$ denotes the `GF-47` Theorem 3.6 top-band reset modulus. $L$ denotes the unit lower-triangular difference matrix in §§2–4 and binary run length in §§4–5; $L_N = \operatorname{lcm}(1, \dots, N)$ always carries a subscript.

**Evidence labels** ([`docs/research-objectives.md`](../../docs/research-objectives.md)):
- *Paper proof*: complete written proof in this note.
- *Finite certificate*: exact `int`/`Fraction` computation verified by `scripts/phase26_hankel_ln2.py` (`[exact]`, or outward-certified rational enclosure `[encl]`).
- *External input*: published theorem cited without re-proof (enumerated in §8).
- *Finite measurement* / *Numerical evaluation* (`[finite]` / `[float]`): isolated numerical comparisons; bears on no asymptotic limit.
- *Open*.

Independent cross-model audit ([`reviews/track-b-review.md`](reviews/track-b-review.md)) was used to audit and revise this note; cross-model review is **not** independent human peer review and authorizes no benchmark status change.

**Scope statement.** **Nothing in this note proves normality, simple normality, simple nonnormality, $D^+ < 1$, $D^- > 0$, or (non)membership in $K_b$ for $\ln 2$, $\pi$, $e$, $\zeta(3)$, or any constant in the permanent 50-constant roster `BC-01`…`BC-50`. No benchmark status changes.** The results are unconditional arithmetic-analytic structural theorems, an exact Hankel–Padé equivalence, a self-contained dyadic irrationality measure $\mu_2(\ln 2) \le 6.178813\ldots$ (weaker than Alladi–Robinson 1980 and Marcovecchio 2009, sharper than `CC-05`'s Lean transition constant), a rigorous reset-countermodel limitation theorem, and exact BBP/factorial extensions (Objectives 3 and 4).

---

## Summary of conclusions

| Item | Headline Result | Evidence |
| --- | --- | --- |
| **B1** | **Prime-centered Hankel pole & nonvanishing** (Thm 1.1): for every prime $p$ (odd, and also $p = 2$), $1 \le r \le p$, $M = p - r + 1$, and arbitrary $m_{i,j} \in \mathbb{Z}_{(p)}$, $p H \bmod p$ is lower-right anti-triangular with unit anti-diagonal $1$, giving $\det(p H) \equiv (-1)^{r(r-1)/2} \pmod p$, **$v_p(\det H) = -r$**, and **$\det H \ne 0$** unconditionally. Clarified as an amplified denominator pole, not a positive numerator gain. Lean-ready Track H lemma specs provided (§1.3). | Paper proof; finite certificate (`284` exact matrices) |
| **B2** | **Recurrence-reduced row & double-difference clearing** (Thm 2.1, Lemma 2.2, Cor. 2.3): bottom-to-top $\mathrm{row}_i \leftarrow \mathrm{row}_i - 2\mathrm{row}_{i-1}$ clears prior primes into row $0$ and yields $\operatorname{den}(\det H) \mid D_{\mathrm{row}}(p, r) = L_p \prod_{i=1}^{r-1} \operatorname{lcm}(M+i, \dots, M+i+r-1)$. Double differencing $H^{(2)} = L H L^T$ refines $L_p$ to $\operatorname{lcm}(Q_M, \operatorname{lcm}(M+1, \dots, p))$. At $r = c\sqrt{p/\log p}$, $\log D_{\mathrm{row}} = (1 + c^2/2 + o(1)) p = O(p)$ (vs naive $\Theta(rp)$); at the full linear endpoint $r = p$ ($\alpha = 1$), $\log D_{\mathrm{row}}(p, p) + \log \det C(1, p) = (\frac{3}{2} - 2\ln 2 + o(1)) p^2 \approx +0.11371\, p^2 > 0$ (for $\alpha \in (0, 1)$, finite measurements at $p = 1999$ remain positive overall, though the $r^2$-normalized excess dips to $-0.0796$ at $\alpha = 0.02$). | Paper proof (+ PNT for asymptotics at sublinear $r$ and $\alpha = 1$); finite certificate (`924` LCM pairs, `51` matrices); finite measurement / heuristic for $\alpha \in (0, 1)$ |
| **B3** | **Rank-sensitive local denominator lemma & exact B3–Cauchy cancellation** (Thms 3.1, 3.2, 3.3, 3.4): SNF / saturated-lattice bound $v_q(\det A) \ge -\sum_{k=0}^{e-1} s_k$. For BBP windows: non-entering primes have rank $\le 1$ ($v_q \ge -e_q(s_M)$); single-insertion simple primes at $t = mq - M$ have **exact** rank $s(t) = \min(t, 2r - 1 - t) + \mathbf{1}_{\rho_{\mathrm{maj}} \ne 0}$ (dropping by $1$ at first entry $m = 1$ when $t \ge r$, or at `GF-47` drop events $q \mid A_m$ or $q \mid A_{m-1}$). For ALL primes $q$ (incl. $q = 2$, higher powers $q^e$), block-rank decomposition proves $D_{\mathrm{B3}}(p, r) \mid D_{\mathrm{row}}(p, r)$, the **exact finite integer identity** $\prod_q q^{\sum_j \mathrm{rk}(M,r,q^j)} = \bigl(r \binom{p}{r} \det C(M-1, r)\bigr)^{-1}$, and **$D_{\mathrm{B3}}(p, r) \det C(M, r) \le \frac{L_p}{r \binom{p+r}{r}}$**, cancelling ALL $O(p^2)$ terms identically and collapsing $\log(D_{\mathrm{B3}} \det C)$ to $\Phi_{\mathrm{B3}}(\alpha) p = (1 + \alpha\log\alpha - (1+\alpha)\log(1+\alpha)) p < 0$ for $\alpha > 0.542211\ldots$. | Paper proof (zero PNT for exact divisibility; PNT for $\Phi_{\mathrm{B3}}$); finite certificate (`1,716` rank windows, `6,272` Cauchy-block triples, `100` global identities) |
| **B4** | **Positive-moment representation & Exact Uvarov–Christoffel Reduction** (Props 4.1–4.2, Thms 4.3–4.5): $H_c = \varepsilon v v^T - K$, $\frac{1}{2} C \prec K \prec C$, exact $v^T C^{-1} v = \sum_{k=0}^{r-1} (2k+M+1) P_k^{(0,M)}(3)^2$, elementary Hadamard–Jacobi upper bounds on $\det K / \det C$, and the **exact algebraic identity** $\det K / \det C = r\binom{p+r}{r} I_{M, r-1}$, $v^T K^{-1} v = P_{r-1}^{(0,M)}(3)/I_{M, r-1}$, $\det H_c = (-1)^r r\binom{p+r}{r}\det C \cdot (I_{M,r-1} - \varepsilon P_{r-1}^{(0,M)}(3))$, yielding **$D_{\mathrm{B3}}(p, r)\det K \le L_p I_{M, r-1}$**. Proves unconditionally $|2^M \ln 2 - m_M| \ge 2^{-(5.178813 + o(1)) M}$ ($\mu_2^{\mathrm{Hankel}} = 6.178813\ldots$, threshold $\alpha_* = 0.442847\ldots$, $\ge 0.3806 \log_2 N$ binary transitions vs `CC-05`'s $0.1966 \log_2 N$, vs Alladi–Robinson $4.622101$ and Marcovecchio $3.574554$). | Paper proof (+ PNT); finite certificate (`153` exact $\mathbb{Q}[X]$ Uvarov–Christoffel cases, `97` rational enclosures) |
| **B5** | **Adversarial countermodel survival & activation-vs-exclusion reset barrier** (Thm 5.1): every reset-free prime-centered window inside `GF-47` Theorem 3.6's countermodel blocks $[n_i, \lfloor \frac{3}{2} n_i \rfloor)$ preserves B1, B2, B3, and B4 **verbatim** while $\|\tilde{x}_n\| \to 0$ and $D^+ = 1$. Any reset-free block of ratio $\rho$ caps $\alpha < \frac{\rho-1}{\rho+1}$, so `GF-47`'s $\rho = 1.5$ ($\alpha < 0.20$), top-band $\rho = 1.7213$, and full-denominator $\rho_{\mathrm{info}} = 2.4427$ all sit below the **activation** threshold $\rho_*^{\mathrm{Hankel}} = 2.5897$ (where the Hankel bound first becomes positive). Crucially, actually **excluding** a clean block requires $\rho - 1 > \mu_2^{\mathrm{Hankel}} - 1 \approx 5.1788$, i.e. $\rho > \rho_{\mathrm{excl}}^{\mathrm{Hankel}} \approx 6.1788$: the true gap is **$1.44$ vs $5.18$ bits/index** (e.g. $|\tilde{\varepsilon}| \approx 2^{-166}$ vs threshold $2^{-1243}$ on $[240, 360)$), not a near miss $2.4427$ vs $2.5897$. Crossing a reset breaks B2/B3/B4 via reset poles $M_i M_{i-1}$. Even with zero resets, single-block lower bounds $|\varepsilon| \ge 2^{-c M}$ cannot exclude $D^+ = 1$. | Paper proof; finite certificate on exact `GF-47` blocks $[240, 360)$ and $[360, 540)$ (`18` interior + `1` crossing window + `4` $|\tilde{\varepsilon}|$ enclosures) |
| **B6** | **Complete 8-row Amplification-Cost Ledger** (§6): full side-by-side comparison of B1+B2, B1+B3, and B1+B3+B4 identifying the two exact barriers (asymmetric shift penalty $L_{M+r-1}$ vs $L_r$, and single-block linear-run barrier). | Paper proof (synthesis of §§1–5) |
| **B7** | **Extensions to $\pi$, $e$, and $\zeta(3)$** (Thms 7.1, 7.2, 7.3): $\pi$ (base 16 BBP) gives $v_p = -r$ across all four odd classes mod $8$ ($r \le r_{\max} \approx p/8$), B3 non-entering rank $\le 1$, single-insertion rank law $s(t)$ for $q \ge 7$ (or $\beta \ne 0$), and positive-definite $K^{(\pi)}$ ($P_\pi(t) > 0$), while heuristic quadratic comparison and the symmetric $M = 0$ linear-balance benchmark ($6 - 2\log(4+\sqrt{15}) = +1.8731 > 0$) point against denominator balance. $e$ (factorial $e_K$) gives $v_p = -m r$ across all bands $1 \le m < p$ (no drop events on the anti-diagonal), but fails B3 collapse for $t < r$, fails small-prime clearing, fails PD ($R_1 R_3 < R_2^2$), and degenerates under geometric shifts $m_{n+1} = 2 m_n$ on `GF-47` Cor. 4.4 states. $\zeta(3)$ (Broadhurst base $2^{12}$) gives cubic pole $v_p = -3r$ ($p \ge 13$, $r \le \lfloor(p+12)/24\rfloor$) and B3 cubic non-entering bound, but fails positivity ($Q_{\zeta(3)}(1/2) < 0$; $K^{(\zeta(3))}(M, r)$ indefinite for fixed $M$ and $r \ge r_0(M)$), while the symmetric $M = 0$ linear-balance benchmark gives $+62.30 > 0$. | Paper proof & finite certificate (`30` $\pi$ + `124` $\pi$-rank windows, `53` $e$, `15` $\zeta(3)$ matrices, exact non-PD / sign-change & $>52$-digit Broadhurst certificates); *Heuristic / $M = 0$ benchmark* for $\pi, \zeta(3)$ denominator balances |

---

## 1. B1: Prime-Centered Hankel Determinant ($v_p(\det H) = -r$)

### 1.1 Exact $p$-adic pole and unconditional nonvanishing

**Theorem 1.1 (Prime-centered Hankel pole; Paper proof; Finite certificate).** Let $p$ be a prime (odd, or $p = 2$), let $1 \le r \le p$, and set $M = p - r + 1$. Let $(m_{i,j})_{0 \le i,j < r}$ be ANY matrix of $p$-integral rationals $m_{i,j} \in \mathbb{Z}_{(p)}$ (in particular, any Hankel array $m_{i,j} = m_{M+i+j}$ with arbitrary integers $m_n \in \mathbb{Z}$), and define

```math
H_{i,j} = s_{M + i + j} - m_{i,j} \qquad (0 \le i, j < r).
```

Then:
1. $p H \in M_r(\mathbb{Z}_{(p)})$, and entrywise modulo $p \mathbb{Z}_{(p)}$:
   ```math
   p H_{i,j} \equiv \begin{cases} 0 & \text{if } i + j < r - 1, \\ 2^{i + j - (r - 1)} & \text{if } i + j \ge r - 1. \end{cases} \pmod{p \mathbb{Z}_{(p)}}
   ```
   In particular, on the main anti-diagonal $i + j = r - 1$, $p H_{i, r-1-i} \equiv 1 \pmod{p \mathbb{Z}_{(p)}}$.
2. $\det(p H) \equiv (-1)^{r(r-1)/2} \pmod{p \mathbb{Z}_{(p)}}$.
3. Consequently, **$v_p(\det H) = -r$** and **$\det H \ne 0$** unconditionally.

*Proof.* Verify the index range first: since $1 \le r \le p$ and $0 \le i, j \le r - 1$, every index $n = M + i + j$ satisfies

```math
1 \le p - r + 1 = M \le n \le M + 2r - 2 = p + r - 1 \le 2p - 1 < 2p.
```

Moreover, $n = p$ if and only if $i + j = r - 1$.

- *Case $i + j < r - 1$ (so $1 \le n < p$):* every summand $\frac{2^{n-k}}{k}$ ($1 \le k \le n$) in $s_n$ has $1 \le k < p$, so $p \nmid k$ and $2^{n-k} \in \mathbb{Z}$, hence $s_n \in \mathbb{Z}_{(p)}$. Since $m_{i,j} \in \mathbb{Z}_{(p)}$, $H_{i,j} \in \mathbb{Z}_{(p)}$ and $p H_{i,j} \in p \mathbb{Z}_{(p)}$.
- *Case $i + j \ge r - 1$ (so $p \le n \le 2p - 1$):* the unique integer $k \in \{1, \dots, n\}$ divisible by $p$ is $k = p$. Separating $k = p$ gives
  ```math
  p H_{i,j} = 2^{n - p} + p \left( \sum_{\substack{1 \le k \le n \\ k \ne p}} \frac{2^{n-k}}{k} - m_{i,j} \right).
  ```
  Every remaining term has $p \nmid k$ and $n - k \ge 0$, so the parenthesized expression lies in $\mathbb{Z}_{(p)}$, giving $p H_{i,j} \equiv 2^{n - p} = 2^{i + j - (r - 1)} \pmod{p \mathbb{Z}_{(p)}}$. (For odd $p$, every lower-right entry is a unit mod $p$; for $p = 2$, $r \in \{1, 2\}$, $2^0 = 1$ on the anti-diagonal and $2^1 \equiv 0 \pmod 2$ at $(1, 1)$ when $r = 2$, so the congruence holds for $p = 2$ as well.)

This proves (1). Let $A = p H \in M_r(\mathbb{Z}_{(p)})$ and let $\bar{A} \in M_r(\mathbb{F}_p)$ be its reduction modulo $p$. Permuting the columns of $\bar{A}$ by the anti-diagonal reversal $\sigma(j) = r - 1 - j$ (which is a product of $\lfloor r/2 \rfloor$ disjoint transpositions, so $\operatorname{sgn}(\sigma) = (-1)^{\lfloor r/2 \rfloor} = (-1)^{r(r-1)/2}$) produces a lower-triangular matrix whose diagonal entries are $\bar{A}_{i, r-1-i} = 1$. Hence $\det(\bar{A}) = (-1)^{r(r-1)/2} \cdot 1^r = (-1)^{r(r-1)/2} \ne 0$ in $\mathbb{F}_p$. Lifting back to $\mathbb{Z}_{(p)}$ gives (2) and $v_p(\det A) = 0$. Since $\det A = \det(p H) = p^r \det H$, we conclude $v_p(\det H) = -r$ and $\det H \ne 0$. $\square$

### 1.2 Critical conceptual warning: amplified pole $\ne$ numerator divisibility gain

Writing $\det H = N / D$ in lowest terms ($\gcd(N, D) = 1$, $D > 0$), Theorem 1.1 proves that $p^r \parallel D$ and $p \nmid N$ (so $N \ne 0$). Two points must never be conflated:
1. **$v_p(\det H) = -r$ is an amplified denominator pole, NOT a positive numerator divisibility gain.** It forces $D$ to carry the factor $p^r$; it does **not** supply a prime power dividing $N$ that would lift $|N|$ above $1$, nor does it give any real-size lower bound by itself.
2. **What Theorem 1.1 buys is unconditional nonvanishing with zero exceptional indices.** In any rational lower bound $|\det H| \ge 1 / D_0$ (for a clearing integer $D_0$ with $D_0 \det H \in \mathbb{Z}$), Theorem 1.1 guarantees $D_0 \det H \ne 0$ for *every* prime $p$, *every* $1 \le r \le p$, and *every* choice of integers $m_n$ — eliminating the consecutive-index nonvanishing step required in Padé arguments — while showing that $v_p(D_0) \ge r$ is sharp and cannot be reduced at $p$.

### 1.3 Lean-ready lemma specifications for Track H

Using the repository's existing definition `NormalityChecker.logPrefix : ℕ → ℚ` (`NormalityChecker/LogTwo.lean`), the B1–B2 foundation decomposes into five short, Mathlib-native declarations (one definition, two helper lemmas, and two main theorems) requiring no Smith Normal Form:

```lean
namespace NormalityChecker.HankelLogTwo

/-- Prime-centered r × r BBP Hankel matrix for ln 2 with arbitrary integer shifts. -/
def bbpHankel (p r : ℕ) (m : Fin r → Fin r → ℤ) : Matrix (Fin r) (Fin r) ℚ :=
  fun i j => logPrefix (p - r + 1 + i.val + j.val) - (m i j : ℚ)

/-- Helper: logPrefix n is p-integral for n < p, and p * logPrefix n - 2^(n-p) is p-integral for p ≤ n < 2p. -/
lemma logPrefix_pIntegral_lt {p n : ℕ} (hp : p.Prime) (hn : n < p) :
    ¬ p ∣ (logPrefix n).den

lemma logPrefix_mul_prime_sub_pow {p n : ℕ} (hp : p.Prime) (hlo : p ≤ n) (hhi : n < 2 * p) :
    ¬ p ∣ ((p : ℚ) * logPrefix n - (2 : ℚ) ^ (n - p)).den

/-- Anti-triangular determinant congruence over ZMod p: det(p H) ≡ (-1)^(r(r-1)/2) (mod p). -/
theorem bbpHankel_det_padicVal {p r : ℕ} (hp : p.Prime) (hr1 : 1 ≤ r) (hrp : r ≤ p)
    (m : Fin r → Fin r → ℤ) :
    (bbpHankel p r m).det ≠ 0 ∧ padicValRat p (bbpHankel p r m).det = -(r : ℤ)

/-- Unimodular row reduction L * H has rows i ≥ 1 equal to 1/(M+i+j) - (m_{i,j} - 2 m_{i-1,j}). -/
theorem bbpHankel_den_dvd_rowClearing {p r : ℕ} (hp : p.Prime) (hr1 : 1 ≤ r) (hrp : r ≤ p)
    (m : ℕ → ℤ) :
    ((bbpHankel p r (fun i j => m (p - r + 1 + i.val + j.val))).det).den ∣
      (Finset.Icc 1 p).lcm id *
        ∏ i ∈ Finset.Ico 1 r, (Finset.Icc (p - r + 1 + i) (p + i)).lcm id

end NormalityChecker.HankelLogTwo
```

*Formalization route:* In `bbpHankel_det_padicVal`, map `p • bbpHankel p r m` entrywise through the localization ring homomorphism `Localization.AtPrime (Ideal.span {(p : ℤ)}) →+* ZMod p` (or simply clear the coprime common denominator $D_\perp = \operatorname{lcm}_{i,j} \operatorname{den}(p H_{i,j})$, which satisfies $p \nmid D_\perp$, and reduce the integer matrix $D_\perp (p H)$ modulo $p$ via a **one-sided column permutation** — `Matrix.det_permute'` with `Fin.revPerm`, whose sign is $(-1)^{\lfloor r/2 \rfloor} = (-1)^{r(r-1)/2}$, turning the lower-right anti-triangular mod-$p$ matrix into a lower-triangular matrix with $1$'s on the diagonal; note that a two-sided `Matrix.det_reindex_self` would reindex both rows and columns and leave an anti-triangular matrix anti-triangular). That avoids `Localization` boilerplate completely and stays under ~120 lines of Lean 4.

---

## 2. B2: Recurrence-Reduced Denominator Costs (Row and Double Differences)

### 2.1 Row reduction and double row/column differencing

Let $L \in \mathrm{SL}_r(\mathbb{Z})$ be the unit lower-triangular matrix with $L_{i,i} = 1$, $L_{i, i-1} = -2$ for $1 \le i < r$, and all other entries $0$. Left multiplication $H^{(1)} = L H$ performs the bottom-to-top row operations $\mathrm{row}_i \leftarrow \mathrm{row}_i - 2\,\mathrm{row}_{i-1}$ ($i = r - 1, \dots, 1$), and $H^{(2)} = L H L^T$ additionally performs the right-to-left column operations $\mathrm{col}_j \leftarrow \mathrm{col}_j - 2\,\mathrm{col}_{j-1}$ ($j = r - 1, \dots, 1$). Since $\det L = 1$, $\det H = \det H^{(1)} = \det H^{(2)}$.

**Theorem 2.1 (Row and double-difference clearing; Paper proof; Finite certificate).** For any prime $p$, $1 \le r \le p$, $M = p - r + 1$, and arbitrary integers $(m_n)_{M \le n \le p + r - 1}$:

1. *(Row reduction)* $H^{(1)} = L H$ has entries
   ```math
   H^{(1)}_{0,j} = s_{M + j} - m_{M + j} \quad (0 \le j < r), \qquad H^{(1)}_{i,j} = \frac{1}{M + i + j} - \Delta m_{M + i + j} \quad (1 \le i < r,\ 0 \le j < r).
   ```
   Consequently,
   ```math
   \operatorname{den}(\det H) \;\Big|\; D_{\mathrm{row}}(p, r) := L_p \cdot \prod_{i=1}^{r-1} \operatorname{lcm}(M + i,\ M + i + 1,\ \dots,\ M + i + r - 1).
   ```
2. *(Double differencing)* $H^{(2)} = L H L^T$ has the block form
   ```math
   H^{(2)} = \begin{pmatrix} s_M - m_M & u^T \\ u & B \end{pmatrix},
   ```
   where $u_j = \frac{1}{M + j} - \Delta m_{M + j}$ ($1 \le j < r$) and $B_{i,j} = \frac{1}{M + i + j} - \frac{2}{M + i + j - 1} - \Delta^2 m_{M + i + j}$ ($1 \le i, j < r$). Row-by-row clearing of $H^{(2)}$ gives the **exact same** row LCMs $L_p$ and $D_i = \operatorname{lcm}(M+i, \dots, M+i+r-1)$ as $H^{(1)}$. However, expanding $\det H^{(2)} = (s_M - m_M) \det B + \det\begin{pmatrix} 0 & u^T \\ u & B \end{pmatrix}$ isolates $s_M$ in the single $(0,0)$ entry and yields the strictly refined divisibility
   ```math
   \operatorname{den}(\det H) \;\Big|\; D_{\mathrm{double}}(p, r) := \operatorname{lcm}\bigl(Q_M,\ \operatorname{lcm}(M + 1, \dots, p)\bigr) \cdot \prod_{i=1}^{r-1} \operatorname{lcm}(M + i, \dots, M + i + r - 1) \;\Big|\; D_{\mathrm{row}}(p, r).
   ```

*Proof.* (1) For $i \ge 1$, $s_{M+i+j} - 2 s_{M+i-1+j} = \frac{1}{M+i+j}$ by the BBP recurrence, so $H^{(1)}_{i,j} = \frac{1}{M+i+j} - \Delta m_{M+i+j}$. Every entry in row $0$ has $M + j \le p$ and denominator dividing $L_p$; every entry in row $i \ge 1$ has denominator dividing $D_i = \operatorname{lcm}(M+i, \dots, M+i+r-1)$. Multiplying row $0$ by $L_p$ and row $i \ge 1$ by $D_i$ produces an integer matrix with determinant $D_{\mathrm{row}}(p, r) \det H \in \mathbb{Z}$.

(2) Applying $\mathrm{col}_j \leftarrow \mathrm{col}_j - 2\mathrm{col}_{j-1}$ to $H^{(1)}$ leaves $(0,0)$ unchanged, turns $(0, j)$ ($j \ge 1$) into $(s_{M+j} - 2 s_{M+j-1}) - \Delta m_{M+j} = \frac{1}{M+j} - \Delta m_{M+j} = u_j$, leaves $(i, 0) = u_i$, and turns $(i, j)$ ($i, j \ge 1$) into $\frac{1}{M+i+j} - \frac{2}{M+i+j-1} - \Delta^2 m_{M+i+j}$. In row $i \ge 1$ of $H^{(2)}$, the integers appearing in denominators are $\{M+i\} \cup \bigcup_{j=1}^{r-1}\{M+i+j-1, M+i+j\} = \{M+i, \dots, M+i+r-1\}$, whose LCM is still $D_i$; in row $0$ of $H^{(2)}$, the LCM of $Q_M$ and $M+1, \dots, p$ divides $L_p$. In the multilinearity split $\det H^{(2)} = (s_M - m_M)\det B + \det\begin{pmatrix} 0 & u^T \\ u & B \end{pmatrix}$, the first term has denominator dividing $Q_M \prod_{i=1}^{r-1} D_i$ and the second has denominator dividing $\operatorname{lcm}(M+1, \dots, p) \prod_{i=1}^{r-1} D_i$; their sum has denominator dividing $D_{\mathrm{double}}(p, r)$. $\square$

*What double differencing saves:* $D_{\mathrm{double}}$ improves on $D_{\mathrm{row}}$ precisely at primes $q \le p$ satisfying $\max\!\bigl(v_q(Q_M),\ \max_{M < n \le p} v_q(n)\bigr) < \lfloor \log_q p \rfloor$ (with the empty max taken as $0$ when $M = p$; e.g., when $q$ drops in $s_M$ and no multiple of $q^{\lfloor \log_q p \rfloor}$ lies in $(M, p]$, occurring in $17/51$ exact test matrices in `scripts/phase26_hankel_ln2.py`). Since $\log(L_M/Q_M) \le 116 M^{2/3}$ (`CC-03`), double differencing changes $\log D_{\mathrm{row}}$ only by $O(p^{2/3})$ and leaves the leading asymptotics unchanged.

### 2.2 Exact two-sided interval-LCM lemma and asymptotic logarithmic cost of B2

**Lemma 2.2 (Exact two-sided interval-LCM divisibility; Paper proof; Finite certificate).** For every integer $a \ge 1$ and $r \ge 1$, put $I = \{a, a + 1, \dots, a + r - 1\}$ and $P_I = \prod_{m \in I} m$. Then

```math
P_I \;\Big|\; (r - 1)!\, \operatorname{lcm}(I) \qquad \text{and} \qquad r!\, \operatorname{lcm}(I) \;\Big|\; L_r \, P_I,
```

whence $\frac{P_I}{(r-1)!} \le \operatorname{lcm}(I) \le \frac{L_r}{r!} P_I$.

*Proof.* Fix any prime $q$. For the first divisibility, choose $m_0 \in I$ maximizing $v_q(m_0)$, so $v_q(m_0) = v_q(\operatorname{lcm}(I))$. For every $m \in I \setminus \{m_0\}$, $v_q(m) \le v_q(|m - m_0|)$ (since $q^{v_q(m)}$ divides both $m$ and $m_0$). Writing $k_1 = m_0 - a$ and $k_2 = a + r - 1 - m_0$ (so $k_1 + k_2 = r - 1$),

```math
v_q(P_I) - v_q(\operatorname{lcm}(I)) = \sum_{m \in I \setminus \{m_0\}} v_q(m) \le \sum_{m \in I \setminus \{m_0\}} v_q(|m - m_0|) = v_q(k_1!\, k_2!) \le v_q((r - 1)!),
```

because $\binom{r-1}{k_1} \in \mathbb{Z}$. For the second divisibility, write $c(q^e) = \#\{m \in I : q^e \mid m\}$. Then $v_q(P_I) - v_q(\operatorname{lcm}(I)) = \sum_{e \ge 1,\, c(q^e) \ge 1} (c(q^e) - 1)$. Whenever $q^e \le r$, any interval of length $r$ contains at least $\lfloor r / q^e \rfloor \ge 1$ multiples of $q^e$, so $v_q(P_I) - v_q(\operatorname{lcm}(I)) \ge \sum_{e \ge 1,\, q^e \le r} (\lfloor r / q^e \rfloor - 1) = v_q(r!) - \lfloor \log_q r \rfloor = v_q(r!) - v_q(L_r)$. $\square$

**Corollary 2.3 (Exact logarithmic denominator cost of B2; Paper proof + PNT external).**
1. *(Sublinear regime $1 \le r = o(p)$)* By Lemma 2.2, Stirling's formula, and PNT ($\psi(x) = (1 + o(1)) x$),
   ```math
   \log D_{\mathrm{row}}(p, r) = \psi(p) + r(r - 1) \log\!\left(\frac{p}{r}\right) + \kappa_D(p, r) r^2 + O\!\left(r \log r + \frac{r^3}{p}\right), \qquad 1 - o(1) \le \kappa_D(p, r) \le 2 + o(1).
   ```
   In particular, setting $r = \bigl(c + o(1)\bigr) \sqrt{p / \log p}$ (for any fixed $c > 0$) yields
   ```math
   \log D_{\mathrm{row}}(p, r) = \left(1 + \frac{c^2}{2} + o(1)\right) p = O(p)
   ```
   (with slow subleading $o(1)$ correction $\approx c^2\bigl(\frac{\log\log p}{2\log p} + \frac{\kappa_D}{\log p}\bigr) \approx 0.25\text{–}0.34$ at $c = 1$, $p \approx 2000$), whereas naive row-by-row clearing $D_{\mathrm{naive}}(p, r) = L_{p + r - 1}^r$ has $\log D_{\mathrm{naive}}(p, r) = r \psi(p + r - 1) \sim c\, p^{3/2} / \sqrt{\log p} = \Theta(rp)$.
2. *(Full linear endpoint $r = p$, $\alpha = 1$, $M = 1$)* For every $1 \le i \le p - 1$, every prime power $q^e \le p$ divides some element of $[i+1, i+p]$ (length $p$) and every prime power $q^e \in (p, i+p]$ belongs to $[i+1, i+p]$ itself, so $\operatorname{lcm}(i+1, \dots, i+p) = L_{i+p}$. Hence
   ```math
   \log D_{\mathrm{row}}(p, p) = \psi(p) + \sum_{i=1}^{p-1} \psi(i + p) = \left(\frac{3}{2} + o(1)\right) p^2.
   ```
   Comparing with $-\log \det C(1, p) = (2 \ln 2 + o(1)) p^2 \approx 1.38629\, p^2$ (§4.2), B2 leaves a strictly positive quadratic excess $(\frac{3}{2} - 2\ln 2 + o(1)) p^2 \approx +0.11371\, p^2 > 0$ at $\alpha = 1$, so $D_{\mathrm{row}}(p, p) \det C(1, p) \to +\infty$.

*Remark (Behavior for intermediate $\alpha \in (0, 1)$; Finite measurement / Heuristic).* For $\alpha \in (0, 1)$, Lemma 2.2 alone gives only $1 - o(1) \le \kappa_D(p, r) \le 2 + o(1)$, which does not decide the sign of $\kappa_D - \frac{3}{2}$ in the small-$\alpha$ limit against $-\log \det C((1-\alpha)p, \alpha p)$. Heuristically, averaging $\sum_{n \le x} \Lambda(n)\{x/n\} \sim (1 - \gamma) x$ predicts $\kappa_D \to 1 + \gamma \approx 1.5772 > \frac{3}{2}$ (quadratic excess $\gamma - \frac{1}{2} \approx +0.0772$ per $r^2$). Finite measurements at $p = 1999$ (`scripts/phase26_hankel_ln2.py`, `[finite]`) agree closely across $0.10 \le \alpha \le 0.80$, where $(\log D_{\mathrm{row}} + \log\det C - \psi(p))/r^2 \in [0.0667, 0.0751]$ (and $+0.1124$ at $\alpha = 1.00$), whereas at small $\alpha = 0.02$ ($r = 40$) subleading terms push that $r^2$-normalized ratio to $-0.0796$ and only the $\psi(p)$ term keeps $\log(D_{\mathrm{row}} \det C) = +1867.09 > 0$. We do not prove a general $\alpha \in (0, 1)$ lower bound for B2 because B3 (Theorem 3.4) strictly supersedes B2.

---

## 3. B3: Rank-Sensitive Prime-Local Denominator Lemma and Exact B3–Cauchy Cancellation

### 3.1 General prime-local rank and elementary-divisor bounds

**Theorem 3.1 (Rank-sensitive $q$-adic determinant bound; Paper proof).** Let $q$ be a prime and let $A \in M_r(\mathbb{Q})$.

1. *(Simple pole, $e = 1$)* Suppose $B := q A \in M_r(\mathbb{Z}_{(q)})$ and let $s = \operatorname{rank}_{\mathbb{F}_q}(B \bmod q)$. Then $v_q(\det A) \ge -s$.
2. *(General prime power $q^e$, $e \ge 1$)* Suppose $B := q^e A \in M_r(\mathbb{Z}_{(q)})$. Let $B = U \operatorname{diag}(d_1, \dots, d_r) V$ be its Smith Normal Form over the PID $\mathbb{Z}_{(q)}$ ($U, V \in \mathrm{GL}_r(\mathbb{Z}_{(q)})$, $0 \le v_1 \le \dots \le v_r \le \infty$ where $v_i = v_q(d_i)$). For each $0 \le k \le e - 1$, define the level-$k$ $\mathbb{F}_q$-rank
   ```math
   s_k := \#\{1 \le i \le r : v_i \le k\} = \dim_{\mathbb{F}_q} \frac{(B \mathbb{Z}_{(q)}^r \cap q^k \mathbb{Z}_{(q)}^r) + q^{k+1} \mathbb{Z}_{(q)}^r}{q^{k+1} \mathbb{Z}_{(q)}^r}.
   ```
   Then
   ```math
   v_q(\det A) \ge -\sum_{k=0}^{e-1} s_k.
   ```
3. *(Saturated-lattice layer bound)* Suppose for a given $j \in \{1, \dots, e\}$ (setting $k = e - j \in \{0, \dots, e-1\}$) we decompose $A = A_{\ge j} + A_{< j}$ with $q^{j-1} A_{< j} \in M_r(\mathbb{Z}_{(q)})$. Then $s_{e - j} \le \operatorname{rank}_{\mathbb{Q}}(A_{\ge j})$. In particular, if $A = A_0 + \sum_{a=1}^m q^{-e_a} R_a$ with $A_0, R_a \in M_r(\mathbb{Z}_{(q)})$, $e = \max_a e_a$, and $\rho_a = \operatorname{rank}_{\mathbb{Q}}(R_a)$, then
   ```math
   v_q(\det A) \ge -\sum_{k=0}^{e-1} \dim_{\mathbb{Q}}\!\left(\sum_{a : e_a \ge e - k} \operatorname{im}_{\mathbb{Q}}(R_a)\right) \ge -\sum_{a=1}^{m} e_a \rho_a.
   ```

*Proof.* (1) is the $e = 1$ case of (2) since $s_0 = \operatorname{rank}_{\mathbb{F}_q}(B \bmod q)$. (Note also an SNF-free elementary proof of (1) for Lean: row-echelon reduction over $\mathbb{F}_q$ lifts to unimodular $\mathbb{Z}_{(q)}$-row operations that make $r - s$ rows divisible by $q$, so $q^{r-s} \mid \det B = q^r \det A$.)

(2) Changing basis by $U, V \in \mathrm{GL}_r(\mathbb{Z}_{(q)})$ reduces $B \mathbb{Z}_{(q)}^r$ to $\bigoplus_{i=1}^r q^{v_i} \mathbb{Z}_{(q)}$, so $(B \mathbb{Z}_{(q)}^r \cap q^k \mathbb{Z}_{(q)}^r) + q^{k+1} \mathbb{Z}_{(q)}^r = \bigoplus_{i=1}^r q^{\min(\max(v_i, k), k+1)} \mathbb{Z}_{(q)}$. The quotient modulo $q^{k+1}\mathbb{Z}_{(q)}^r$ has one $\mathbb{F}_q$-summand precisely for each $i$ with $v_i \le k$, confirming the two definitions of $s_k$ coincide. Then

```math
v_q(\det B) = \sum_{i=1}^{r} v_i \ge \sum_{i=1}^{r} \min(v_i, e) = \sum_{k=0}^{e-1} \#\{i : v_i > k\} = \sum_{k=0}^{e-1} (r - s_k) = e r - \sum_{k=0}^{e-1} s_k.
```

Subtracting $e r$ from $v_q(\det B) = e r + v_q(\det A)$ gives $v_q(\det A) \ge -\sum_{k=0}^{e-1} s_k$.

(3) Set $k = e - j$, $V_k = \operatorname{im}_{\mathbb{Q}}(A_{\ge j}) \subseteq \mathbb{Q}^r$, and $L_k = V_k \cap \mathbb{Z}_{(q)}^r$. Because $\mathbb{Z}_{(q)}$ is a PID and $L_k$ is saturated in $\mathbb{Z}_{(q)}^r$, $L_k$ is free of rank $d_k = \dim_{\mathbb{Q}} V_k = \operatorname{rank}_{\mathbb{Q}}(A_{\ge j})$ and $L_k \cap q \mathbb{Z}_{(q)}^r = q L_k$. Now $B = q^e A_{\ge j} + q^{k+1}(q^{j-1} A_{<j})$ with $q^{j-1} A_{<j} \in M_r(\mathbb{Z}_{(q)})$. If $x \in \mathbb{Z}_{(q)}^r$ satisfies $B x \in q^k \mathbb{Z}_{(q)}^r$, then $y_1 := q^e A_{\ge j} x = B x - q^{k+1}(q^{j-1} A_{<j} x)$ lies in both $V_k$ and $q^k \mathbb{Z}_{(q)}^r$, hence $q^{-k} y_1 \in V_k \cap \mathbb{Z}_{(q)}^r = L_k$, so $y_1 \in q^k L_k$. Therefore $B \mathbb{Z}_{(q)}^r \cap q^k \mathbb{Z}_{(q)}^r \subseteq q^k L_k + q^{k+1} \mathbb{Z}_{(q)}^r$, and dividing by $q^k$ mod $q$ embeds the space defining $s_k$ into $(L_k + q \mathbb{Z}_{(q)}^r)/q\mathbb{Z}_{(q)}^r \cong L_k / q L_k \cong \mathbb{F}_q^{d_k}$, giving $s_k \le d_k$. The additive consequence follows by taking $A_{\ge e-k} = \sum_{a : e_a \ge e-k} q^{-e_a} R_a$ and noting each term $a$ enters exactly $e_a$ levels $k \in \{e - e_a, \dots, e - 1\}$. $\square$

### 3.2 Exact local rank formulas for BBP Hankel windows

Iterating $s_{n+1} = 2 s_n + \frac{1}{n+1}$ yields the exact global decomposition of $H = (s_{M+i+j} - m_{M+i+j})_{0 \le i, j < r}$:

```math
H = s_M \cdot v v^T + \sum_{t=1}^{2r-2} \frac{1}{M + t} E^{(t)} - (m_{M + i + j}), \qquad E^{(t)}_{i,j} = \mathbf{1}_{i+j \ge t}\, 2^{i+j-t}.
```

Define also the upper-left $t \times t$ triangle $F^{(t)}_{i,j} = \mathbf{1}_{i+j < t}\, 2^{i+j}$, so that $E^{(t)} = 2^{-t} v v^T - 2^{-t} F^{(t)}$.

**Theorem 3.2 (Exact single-prime ranks for BBP Hankel windows; Paper proof; Finite certificate).** Fix $M \ge 1$, $r \ge 1$, arbitrary $m_n \in \mathbb{Z}$, and an odd prime $q$.

1. *(No new multiple in $(M, M + 2r - 2]$)* If $q \nmid (M + t)$ for all $1 \le t \le 2r - 2$, then $H = s_M v v^T + A_0$ with $A_0 \in M_r(\mathbb{Z}_{(q)})$. Hence **$v_q(\det H) \ge -e_q(s_M)$** for every $e_q(s_M) \ge 0$ (even when $q^2 \le M$). In particular, when $e_q(s_M) \le 1$, $q H \bmod q = \alpha v v^T$ ($\alpha = q s_M \bmod q$) has exact $\mathbb{F}_q$-rank $\mathbf{1}_{\alpha \ne 0} \le 1$ (and in the simple-pole band regime $q^2 > M$ of `GF-47` Lemma 3.3, rank $0$ occurs precisely when $q > M$ or $\lfloor M/q \rfloor \in D(q)$, i.e. $q \mid A_{\lfloor M/q \rfloor}$, and rank $1$ otherwise), so $v_q(\det H) \ge -1$ instead of $-r$.
2. *(Single simple insertion $m q = M + t \in (M, M + 2r - 2]$)* Suppose $v_q(s_M) \ge -1$ (e.g. $q^2 > M + 2r - 2$), and suppose there is a unique $t \in \{1, \dots, 2r - 2\}$ with $q \mid (M + t)$, satisfying $q^2 \nmid (M + t)$ (write $M + t = m q$, $q \nmid m$). Set $\alpha = q s_M \bmod q$, $\beta = m^{-1} \bmod q \in \mathbb{F}_q^\times$, and $\gamma = (\alpha 2^t + \beta) \bmod q = (q s_{mq}) \bmod q$. Define the major-side residue
   ```math
   \rho_{\mathrm{maj}} := \begin{cases} \gamma & \text{if } 1 \le t \le r - 1, \\ \alpha & \text{if } r \le t \le 2r - 2. \end{cases}
   ```
   Then $q H \in M_r(\mathbb{Z}_{(q)})$ and its **exact** $\mathbb{F}_q$-rank is
   ```math
   s(t) = \operatorname{rank}_{\mathbb{F}_q}(q H \bmod q) = \min(t,\ 2r - 1 - t) + \mathbf{1}_{\rho_{\mathrm{maj}} \ne 0},
   ```
   so $v_q(\det H) \ge -s(t)$.
3. *(Connection to `GF-47` drop events)* When $q^2 > M + 2r - 2$, `GF-47` Lemma 3.3 gives $q s_{mq} \equiv 2^{mq - m} s_m \pmod q$, so $\gamma = 0 \iff m \in D(q)$ (post-insertion drop) and $\alpha = 0 \iff (m = 1 \text{ or } m - 1 \in D(q))$ (first entry or pre-insertion drop). In particular, centering a Hankel matrix at a drop multiple such as $2p = 10$ for $p = 5$ ($2 \in D(5)$ since $A_2 = 5$, $t = r - 1$) drops the rank to $s(r - 1) = r - 1 < r$ and gives $v_5(\det H) \ge -(r - 1)$ instead of $-r$!
4. *(General odd prime with multiple insertions / higher powers)* Rewriting $E^{(t)} = 2^{-t} v v^T - 2^{-t} F^{(t)}$ for all $t < r$ with $q \mid (M+t)$ absorbs those $v v^T$ terms into $2^{-(r-1)} s_{M+r-1} v v^T$, giving via Theorem 3.1(3)
   ```math
   -v_q(\det H) \le e_q(s_{M+r-1}) + \sum_{\substack{1 \le t \le 2r - 2 \\ q \mid (M + t)}} v_q(M + t) \cdot \min(t,\ 2r - 1 - t).
   ```

*Proof.* (1) Every $\frac{1}{M+t} \in \mathbb{Z}_{(q)}$, so $H = s_M v v^T + A_0$ with $A_0 \in M_r(\mathbb{Z}_{(q)})$. Since $\operatorname{rank}_{\mathbb{Q}}(v v^T) = 1$, Theorem 3.1(3) gives $v_q(\det H) \ge -e_q(s_M)$.

(2) Over $\mathbb{F}_q$, $\bar{B} := q H \bmod q = \alpha v v^T + \beta E^{(t)}$.
- *Subcase $r \le t \le 2r - 2$:* Row $0$ and column $0$ of $E^{(t)}$ are identically zero, while the bottom-right $(2r-1-t) \times (2r-1-t)$ submatrix of $E^{(t)}$ is anti-triangular with $1$'s on its anti-diagonal, hence has rank $2r - 1 - t = \min(t, 2r-1-t)$. If $\alpha = 0$, $\operatorname{rank}(\bar{B}) = 2r - 1 - t$. If $\alpha \ne 0$, row $0$ of $\bar{B}$ is $\alpha v^T$ and column $0$ is $\alpha v$; subtracting $2^i \cdot \mathrm{row}_0$ from $\mathrm{row}_i$ ($i \ge 1$) annihilates $\alpha v v^T$ in rows $i \ge 1$ while leaving $E^{(t)}$ untouched, yielding block form $\operatorname{diag}(\alpha,\, \beta \tilde{E}^{(t)})$ of exact rank $1 + (2r - 1 - t) = 2r - t$.
- *Subcase $1 \le t \le r - 1$:* Using $E^{(t)} = 2^{-t}(v v^T - F^{(t)})$ (valid in $\mathbb{F}_q$ since $q$ is odd), $\bar{B} = \gamma 2^{-t} v v^T - \beta 2^{-t} F^{(t)}$. Here $F^{(t)}$ is zero outside its top-left $t \times t$ block, which is upper-left anti-triangular with nonzero anti-diagonal $2^{t-1}$, hence has exact rank $t = \min(t, 2r-1-t)$. If $\gamma = 0$, $\operatorname{rank}(\bar{B}) = t$. If $\gamma \ne 0$, since $t \le r - 1$, row $t$ and column $t$ of $F^{(t)}$ are zero, while row $t$ of $\bar{B}$ is $\gamma v^T$ and column $t$ is $\gamma v$; eliminating with pivot $(t, t) = \gamma 2^t \ne 0$ leaves $-\beta 2^{-t} F^{(t)}$ intact and yields exact rank $1 + t$.

(3) Immediate from (2) and `GF-47` Lemma 3.3. (4) Writing $S_q = \{t \in [1, 2r-2] : q \mid M+t\}$, $H = 2^{-(r-1)} s_{M+r-1} v v^T - \sum_{t \in S_q,\, t < r} \frac{2^{-t}}{M+t} F^{(t)} + \sum_{t \in S_q,\, t \ge r} \frac{1}{M+t} E^{(t)} + \tilde{A}_0^{(q)}$ with $\tilde{A}_0^{(q)} \in M_r(\mathbb{Z}_{(q)})$ since $2$ is a $q$-unit. Applying Theorem 3.1(3) with $\operatorname{rank}_{\mathbb{Q}}(v v^T) = 1$, $\operatorname{rank}_{\mathbb{Q}}(F^{(t)}) = t$, and $\operatorname{rank}_{\mathbb{Q}}(E^{(t)}) = 2r - 1 - t$ yields (4). $\square$

### 3.3 Residue-class block-rank bound and exact global B3–Cauchy cancellation

Theorem 3.2(4) already improves B2 at drop events, but when $r$ grows linearly with $p$, small/medium primes $q \in (r/2, r)$ have overlapping residue classes across rows of $H^{(1)} = L H$. Applying Theorem 3.1(3) directly to $H^{(1)}$ unlocks an **exact** cancellation of the entire quadratic $O(p^2)$ excess of B2.

For integers $M \ge 1$, $r \ge 1$, and $d \ge 1$, partition the rows $1 \le i \le r - 1$ and columns $0 \le j \le r - 1$ of $H^{(1)}$ by residue classes $c \in \mathbb{Z}/d\mathbb{Z}$:

```math
m_c(d) := \#\{1 \le i \le r - 1 : -M - i \equiv c \pmod d\}, \qquad n_c(d) := \#\{0 \le j \le r - 1 : j \equiv c \pmod d\},
```

and set $\mathrm{rk}(M, r, d) := \sum_{c=0}^{d-1} \min\bigl(m_c(d),\, n_c(d)\bigr)$.

**Theorem 3.3 (Residue-class block-rank denominator bound; Paper proof; Finite certificate).** For **every** prime $q$ (including $q = 2$), every $M \ge 1$, $r \ge 1$, and arbitrary integers $(m_n)$, set $e_0(q) := \max_{0 \le c < r} e_q(s_{M+c}) \le \lfloor \log_q(M + r - 1) \rfloor$. Then

```math
-v_q(\det H) \le \sum_{j=1}^{\lfloor \log_q(M + 2r - 2) \rfloor} \min\!\Bigl(r,\ \mathbf{1}_{j \le e_0(q)} + \mathrm{rk}(M, r, q^j)\Bigr) =: v_q\bigl(D_{\mathrm{B3}}(p, r)\bigr).
```

Moreover, for $M = p - r + 1$ ($1 \le r \le p$), **$\operatorname{den}(\det H) \mid D_{\mathrm{B3}}(p, r) \mid D_{\mathrm{row}}(p, r)$**.

*Proof.* Set $A = H^{(1)} = L H$ ($\det A = \det H$) and $e = \lfloor \log_q(M + 2r - 2) \rfloor$, so $q^e A \in M_r(\mathbb{Z}_{(q)})$. Fix $j \in \{1, \dots, e\}$ and split $A = A_{\ge j} + A_{< j}$, where $A_{\ge j}$ retains row $0$ of $A$ if and only if $j \le e_0(q)$, and in rows $1 \le i < r$ retains the term $\frac{1}{M + i + \ell}$ exclusively at entries $(i, \ell)$ with $q^j \mid (M + i + \ell)$ (putting $0$ elsewhere). Every entry of $A_{< j}$ has $q$-adic valuation $\ge -(j - 1)$ (in row $0$ because $j > e_0(q)$ if row $0$ was left in $A_{<j}$; in rows $i \ge 1$ because entries where $q^j \mid (M+i+\ell)$ leave only $-\Delta m_{M+i+\ell} \in \mathbb{Z}$, and all others satisfy $v_q(M+i+\ell) \le j - 1$). Thus $q^{j-1} A_{< j} \in M_r(\mathbb{Z}_{(q)})$.

In rows $1 \le i < r$, $A_{\ge j}$ is nonzero only when $\ell \equiv -M - i \pmod{q^j}$. Grouping rows by $c = (-M - i) \bmod q^j$ and columns by $c = \ell \bmod q^j$ decomposes rows $1 \dots r-1$ of $A_{\ge j}$ into a direct sum of $q^j$ disjoint blocks of sizes $m_c(q^j) \times n_c(q^j)$, whose $\mathbb{Q}$-rank is at most $\sum_{c=0}^{q^j - 1} \min(m_c(q^j), n_c(q^j)) = \mathrm{rk}(M, r, q^j)$. Adding row $0$ increases the rank by at most $\mathbf{1}_{j \le e_0(q)}$, and the total rank is trivially at most $r$. Theorem 3.1(2)–(3) yields $-v_q(\det H) \le v_q(D_{\mathrm{B3}}(p, r))$, hence $\operatorname{den}(\det H) \mid D_{\mathrm{B3}}(p, r)$.

Finally, for $D_{\mathrm{B3}}(p, r) \mid D_{\mathrm{row}}(p, r)$: fix any prime $q$ and $d = q^j \le M + 2r - 2$. Row $i \in \{1, \dots, r-1\}$ contains a multiple of $d$ among $\{M + i + \ell : 0 \le \ell < r\}$ (i.e. $d \mid D_i$) if and only if $c = (-M - i) \bmod d$ satisfies $n_c(d) \ge 1$. Hence $\mathrm{rk}(M, r, d) = \sum_{c=0}^{d-1} \min(m_c(d), n_c(d)) \le \sum_{c : n_c(d) \ge 1} m_c(d) = \#\{1 \le i < r : d \mid D_i\}$. Since $\mathbf{1}_{j \le e_0(q)} \le \mathbf{1}_{q^j \le p}$, summing over $j \ge 1$ gives $v_q(D_{\mathrm{B3}}(p, r)) \le \lfloor \log_q p \rfloor + \sum_{j \ge 1} \#\{1 \le i < r : q^j \mid D_i\} = v_q(L_p) + \sum_{i=1}^{r-1} v_q(D_i) = v_q(D_{\mathrm{row}}(p, r))$, proving $D_{\mathrm{B3}}(p, r) \mid D_{\mathrm{row}}(p, r)$. $\square$

**Theorem 3.4 (Exact Cauchy–Block-Rank Identity & Global B3–Cauchy Cancellation; Paper proof; Finite certificate).** Let $M \ge 1$, $r \ge 1$, and put $p_{\mathrm{eff}} = M + r - 1$ (so $p_{\mathrm{eff}} = p$ when $M = p - r + 1$).

1. *(Exact combinatorial identity)* For every integer $d \ge 1$, with $m_c^{\mathrm{full}}(d) := \#\{0 \le i < r : -M - i \equiv c \pmod d\}$,
   ```math
   \sum_{c=0}^{d-1} \min\bigl(m_c^{\mathrm{full}}(d),\, n_c(d)\bigr) = \sum_{k=0}^{r-1} \left(\left\lfloor \frac{M - 1 + r + k}{d} \right\rfloor - \left\lfloor \frac{M - 1 + k}{d} \right\rfloor - 2 \left\lfloor \frac{k}{d} \right\rfloor\right).
   ```
   When $d = q^j$ is a prime power, summing the right-hand side over $j \ge 1$ equals $v_q\bigl(1/\det C(M - 1, r)\bigr)$ by Legendre's formula (which also certifies $1/\det C(M - 1, r) \in \mathbb{Z}_{>0}$).
2. *(Exact row-0 deletion saving)* For every integer $d \ge 1$, the difference $\delta(M, r, d) := \sum_c \min(m_c^{\mathrm{full}}(d), n_c(d)) - \mathrm{rk}(M, r, d)$ satisfies
   ```math
   \delta(M, r, d) = \begin{cases} 1 & \text{if } d \mid r, \\ \left\lfloor \dfrac{p_{\mathrm{eff}}}{d} \right\rfloor - \left\lfloor \dfrac{r}{d} \right\rfloor - \left\lfloor \dfrac{p_{\mathrm{eff}} - r}{d} \right\rfloor & \text{if } d \nmid r. \end{cases}
   ```
   Multiplying over all prime powers $d = q^j$ gives the **exact integer identity**
   ```math
   \prod_{q\ \mathrm{prime}} q^{\sum_{j \ge 1} \mathrm{rk}(M, r, q^j)} = \frac{1}{r \dbinom{p_{\mathrm{eff}}}{r} \det C(M - 1, r)}.
   ```
3. *(Exact global B3–Cauchy cancellation)* For every prime $p \ge 2$, $1 \le r \le p$, $M = p - r + 1$, and arbitrary integers $m_n \in \mathbb{Z}$:
   ```math
   \operatorname{den}(\det H) \;\Big|\; D_{\mathrm{B3}}(p, r) \;\Big|\; \frac{L_p}{r \dbinom{p}{r} \det C(M - 1, r)}, \qquad D_{\mathrm{B3}}(p, r) \cdot \det C(M, r) \;\le\; \frac{L_p}{r \dbinom{p + r}{r}}.
   ```
4. *(Asymptotic collapse of the logarithmic denominator height)* For $r = (\alpha + o(1)) p$ with fixed $\alpha \in (0, 1]$, all $\Theta(p^2)$ terms cancel identically between $\log D_{\mathrm{B3}}(p, r)$ and $-\log \det C(M, r)$ (at $\alpha = 1$, $\log D_{\mathrm{B3}}(p, p)$ drops from B2's $\frac{3}{2} p^2$ to $(2\ln 2 + o(1)) p^2$, saving $(\frac{3}{2} - 2\ln 2) p^2 \approx 0.11371\, p^2$), leaving the **linear** residual
   ```math
   \limsup_{p \to \infty} \frac{\log\bigl(D_{\mathrm{B3}}(p, r) \cdot \det C(M, r)\bigr)}{p} \le \Phi_{\mathrm{B3}}(\alpha) := 1 + \alpha \log \alpha - (1 + \alpha) \log(1 + \alpha),
   ```
   which is **strictly negative** for all $\alpha > \alpha_C = 0.542211\ldots$ (reaching $1 - 2\ln 2 \approx -0.386294$ at $\alpha = 1$).

*Proof.* (1) Write $r = a d + b$ with $0 \le b < d$. On $\mathbb{Z}/d\mathbb{Z}$, $n_c(d) = a + 1$ on $S_n = \{0, \dots, b - 1\}$ and $a$ elsewhere; $m_c^{\mathrm{full}}(d) = a + 1$ on $S_m = \{-M, -M - 1, \dots, -M - b + 1\} \bmod d$ and $a$ elsewhere. Hence $\sum_c \min(m_c^{\mathrm{full}}, n_c) = a d + |S_n \cap S_m|$. Here $|S_n \cap S_m|$ counts pairs $(u, v) \in \{0, \dots, b-1\}^2$ with $d \mid (M + u + v)$, which equals $\sum_{u=0}^{b-1} \bigl(\lfloor \frac{M-1+b+u}{d} \rfloor - \lfloor \frac{M-1+u}{d} \rfloor\bigr)$. On the right-hand side, substituting $r = a d + b$ extracts $a r$ from the first floor; splitting $k \in \{0, \dots, r-1\}$ into $k \in \{0, \dots, b-1\}$ plus $a$ full blocks of length $d$ (each contributing $\sum_{k=0}^{d-1}(\lfloor\frac{x+b+k}{d}\rfloor - \lfloor\frac{x+k}{d}\rfloor) = b$ by Hermite's identity $\sum_{k=0}^{d-1}\lfloor\frac{x+k}{d}\rfloor = x$) gives $a r + a b + |S_n \cap S_m|$. Meanwhile $2 \sum_{k=0}^{r-1} \lfloor k / d \rfloor = a(a-1) d + 2 a b = a r + a b - a d$. Subtracting yields $a d + |S_n \cap S_m|$, proving (1).

(2) Deleting row $i = 0$ decrements only class $c_0 := (-M) \bmod d$, so $\delta(M, r, d) = 1 \iff m_{c_0}^{\mathrm{full}}(d) \le n_{c_0}(d)$. Write $M - 1 = k_1 d + u_1$ and $r = k_2 d + u_2$ ($0 \le u_1, u_2 < d$). If $u_2 = 0$ ($d \mid r$), then $m_{c_0}^{\mathrm{full}} = a = n_{c_0}$, so $\delta = 1$ (while $\lfloor p_{\mathrm{eff}}/d \rfloor - \lfloor r/d \rfloor - \lfloor (p_{\mathrm{eff}}-r)/d \rfloor = \lfloor u_1/d \rfloor = 0$). If $u_2 > 0$, then $c_0 \in S_m$ so $m_{c_0}^{\mathrm{full}} = a + 1$, hence $m_{c_0}^{\mathrm{full}} \le n_{c_0} \iff c_0 \in S_n \iff (d - 1 - u_1) < u_2 \iff u_1 + u_2 \ge d \iff \lfloor (u_1 + u_2)/d \rfloor = 1 = \lfloor p_{\mathrm{eff}}/d \rfloor - \lfloor r/d \rfloor - \lfloor (p_{\mathrm{eff}} - r)/d \rfloor$. Since the two cases $d \mid r$ and $d \nmid r$ are disjoint, summing over prime powers $q^j$ gives $\sum_{j \ge 1} \delta(M, r, q^j) = v_q(r) + v_q\bigl(\binom{p_{\mathrm{eff}}}{r}\bigr)$, proving the exact integer product identity.

(3) Since $\mathbf{1}_{j \le e_0(q)} \le \mathbf{1}_{q^j \le p}$ and $\prod_q q^{\lfloor \log_q p \rfloor} = L_p$, Theorem 3.3 and (2) give $D_{\mathrm{B3}}(p, r) \mid \frac{L_p}{r \binom{p}{r} \det C(M-1, r)}$. Using the exact Cauchy determinant (§4.2),

```math
\frac{\det C(M, r)}{\det C(M - 1, r)} = \prod_{k=0}^{r-1} \frac{M + k}{M + r + k} = \frac{(M + r - 1)! / (M - 1)!}{(M + 2r - 1)! / (M + r - 1)!} = \frac{(p!)^2}{(p - r)!\, (p + r)!}.
```

Multiplying by $\frac{L_p}{r \binom{p}{r}} = L_p \frac{(r-1)!\, (p-r)!}{p!}$ cancels $(p - r)!$ and one $p!$ to yield $\frac{L_p \, (r-1)!\, p!}{(p+r)!} = \frac{L_p}{r \binom{p+r}{r}}$.

(4) Follows immediately from (3) by PNT ($\log L_p = (1 + o(1)) p$) and Stirling's formula on $\binom{p+r}{r}$. $\square$

---

## 4. B4: Positive-Moment Representation, Loewner Comparison, Exact Uvarov–Christoffel Reduction and Literature Comparison

### 4.1 Positive-moment representation and clean-window threshold

**Proposition 4.1 (Integral tail and clean-window threshold; Paper proof; Finite certificate).**
1. For every integer $n \ge 0$, $T_n = \int_0^1 \frac{t^n}{2 - t}\,dt$ and $\frac{1}{n + 2} < T_n < \frac{1}{n + 1} - \frac{1}{2(n + 1)(n + 2)} < \frac{1}{n + 1}$ (in particular $\frac{1}{2(n+1)} < T_n < \frac{1}{n+1}$).
2. *(Nearest-integer recurrence thresholds)*
   - Let $m_n = \mathrm{round}(s_n)$ (nearest integer). Then $m_{n+1} = 2 m_n$ holds uniquely whenever
     ```math
     -\frac{1}{4} - \frac{1}{2(n + 1)} < s_n - m_n < \frac{1}{4} - \frac{1}{2(n + 1)} \qquad \left(\text{in particular whenever } \|s_n\| < \frac{1}{4} - \frac{1}{2(n + 1)}\right).
     ```
   - Let $m_n = \mathrm{round}(2^n \ln 2)$. Then $m_{n+1} = 2 m_n$ holds uniquely whenever $\|2^n \ln 2\| < \frac{1}{4}$ — **equivalently, whenever position $n$ is a binary non-transition** ($d_{n+1} = d_{n+2}$ in `CC-04`). A run of $L \ge 2r - 1$ consecutive equal binary digits starting after position $M$ gives $m_{M+k} = 2^k m_M$ for $0 \le k \le 2r - 2$ and $|\varepsilon| = |2^M \ln 2 - m_M| < 2^{-L}$.
3. *(Rank-1 perturbation identity)* For **any** integer $m_M \in \mathbb{Z}$, setting $m_{M+k} := 2^k m_M$ ($0 \le k \le 2r - 2$) and $\varepsilon := 2^M \ln 2 - m_M$ gives
   ```math
   H_c = \varepsilon v v^T - K(M, r), \qquad \det H_c = (-1)^r \det K(M, r) \cdot \bigl(1 - \varepsilon \, v^T K(M, r)^{-1} v\bigr).
   ```

*Proof.* (1) Expanding $\frac{1}{2 - t} = \sum_{k=1}^\infty \frac{t^{k-1}}{2^k}$ on $[0, 1]$ and integrating term by term by monotone convergence gives $T_n = \sum_{k=1}^\infty \frac{1}{(n+k)2^k}$. Writing $\frac{1}{2 - t} = 1 - \frac{1 - t}{2 - t}$ and using $\frac{1}{2} \le \frac{1}{2 - t} \le 1$ (strict on $(0, 1)$) gives $\frac{1}{2(n+1)(n+2)} < \frac{1}{n+1} - T_n < \frac{1}{(n+1)(n+2)}$, hence $\frac{1}{n+2} < T_n < \frac{1}{n+1} - \frac{1}{2(n+1)(n+2)}$.

(2) From $s_{n+1} - 2 m_n = 2(s_n - m_n) + \frac{1}{n+1}$, we have $|s_{n+1} - 2 m_n| < \frac{1}{2}$ iff $-\frac{1}{4} - \frac{1}{2(n+1)} < s_n - m_n < \frac{1}{4} - \frac{1}{2(n+1)}$. Similarly $2^{n+1}\ln 2 - 2 m_n = 2(2^n \ln 2 - m_n)$ has absolute value $< \frac{1}{2}$ iff $|2^n \ln 2 - m_n| < \frac{1}{4}$ (strict since $\ln 2$ is irrational).

(3) $H_{c;i,j} = s_{M+i+j} - 2^{i+j} m_M = (2^{M+i+j}\ln 2 - T_{M+i+j}) - 2^{i+j} m_M = \varepsilon \cdot 2^{i+j} - K_{i,j}$. For any nonzero $c \in \mathbb{R}^r$, $c^T K c = \int_0^1 (\sum_i c_i t^i)^2 \frac{t^M}{2 - t}\,dt > 0$, so $K$ is symmetric positive definite and invertible; factoring $-K$ gives $\det(\varepsilon v v^T - K) = (-1)^r \det K \cdot \det(I - \varepsilon K^{-1} v v^T) = (-1)^r \det K \cdot (1 - \varepsilon v^T K^{-1} v)$ by the matrix determinant lemma. $\square$

Crucially, Theorem 1.1, Theorem 3.3, and Proposition 4.1(3) hold for **arbitrary** $m_M \in \mathbb{Z}$ with $m_{M+k} := 2^k m_M$ — **no clean-window hypothesis on the binary digits of $\ln 2$ is needed** to obtain an unconditional lower bound on $|2^M \ln 2 - m_M|$.

### 4.2 Loewner comparison, Cauchy determinant, shifted Jacobi polynomials and Hadamard–Jacobi bounds

**Proposition 4.2 (Loewner comparison, exact $v^T C^{-1} v$, and elementary Hadamard–Jacobi bound; Paper proof; Finite certificate).** For all integers $M \ge 0$ and $r \ge 1$:

1. *(Loewner order)* $\frac{1}{2} C(M, r) \prec K(M, r) \prec C(M, r)$ and $C(M, r)^{-1} \prec K(M, r)^{-1} \prec 2 C(M, r)^{-1}$. Hence
   ```math
   2^{-r} \det C(M, r) < \det K(M, r) < \det C(M, r) \qquad \text{and} \qquad v^T C(M, r)^{-1} v < v^T K(M, r)^{-1} v < 2\, v^T C(M, r)^{-1} v.
   ```
2. *(Exact Cauchy determinant)*
   ```math
   \det C(M, r) = \frac{\prod_{0 \le i < j < r} (j - i)^2}{\prod_{i=0}^{r-1}\prod_{j=0}^{r-1} (M + 1 + i + j)} = \frac{\left(\prod_{k=0}^{r-1} k!\right)^2 \prod_{k=0}^{r-1} (M + k)!}{\prod_{k=0}^{r-1} (M + r + k)!}.
   ```
   For $r = o(M)$, $\log \det C(M, r) = -r^2 \log(M/r) - \frac{3}{2} r^2 + O(r\log r + r^3/M)$. For $M = (1-\alpha)p$, $r = \alpha p$ with fixed $\alpha \in (0, 1]$,
   ```math
   \log \det C(M, r) = p^2 \left[\alpha^2 \log \alpha - \frac{1}{2}(1 - \alpha)^2 \log(1 - \alpha) - \frac{1}{2}(1 + \alpha)^2 \log(1 + \alpha)\right] + O(p \log p)
   ```
   (which equals $-2 \ln 2 \cdot p^2 + O(p \log p)$ at $\alpha = 1$).
3. *(Exact reproducing-kernel identity)* Let $P_k^{(0, M)}(2t - 1)$ be the shifted Jacobi polynomial
   ```math
   P_k^{(0, M)}(2t - 1) = \frac{1}{k!\, t^M} \frac{d^k}{dt^k}\bigl(t^{M+k}(t - 1)^k\bigr) = \sum_{j=0}^{k} \binom{k}{j}\binom{M + k}{j} t^{k-j}(t - 1)^j = \sum_{j=0}^{k} (-1)^{k-j}\binom{k}{j}\binom{M + k + j}{k} t^j.
   ```
   Then $\varphi_k(t) = \sqrt{2k + M + 1}\, P_k^{(0, M)}(2t - 1)$ ($0 \le k < r$) are orthonormal on $[0, 1]$ with respect to $t^M\,dt$, and
   ```math
   v^T C(M, r)^{-1} v = \sum_{k=0}^{r-1} (2k + M + 1)\, P_k^{(0, M)}(3)^2, \qquad P_k^{(0, M)}(3) = \sum_{j=0}^{k} \binom{k}{j}\binom{M + k}{j} 2^{k-j} \in \mathbb{Z}_{>0}.
   ```
4. *(Elementary Hadamard–Jacobi upper bound)* Using $\frac{1}{2 - t} \le \frac{1 + t}{2}$ on $[0, 1]$ and the Jacobi three-term expectation $\int_0^1 t\, \varphi_k(t)^2 t^M\,dt = \frac{1}{2} + \frac{M^2}{2(2k+M)(2k+M+2)}$ (for $(k, M) \ne (0,0)$, and $\frac{1}{2}$ at $(0,0)$), Hadamard's inequality on the positive-definite Gram matrix $G_{k,\ell} = \int_0^1 \varphi_k(t)\varphi_\ell(t) \frac{t^M}{2 - t}\,dt$ yields
   ```math
   \frac{\det K(M, r)}{\det C(M, r)} = \det G \le \prod_{k=0}^{r-1} \left(\frac{3}{4} + \frac{M^2}{4(2k + M)(2k + M + 2)}\right).
   ```

*Proof.* (1) Since $\frac{1}{2} < \frac{1}{2 - t} < 1$ on $(0, 1)$, $\frac{1}{2} c^T C c < c^T K c < c^T C c$ for all $c \ne 0$. Eigenvalue monotonicity (Courant–Fischer) gives $2^{-r} \det C < \det K < \det C$, and operator antitonicity of inversion on positive-definite matrices gives $C^{-1} \prec K^{-1} \prec 2 C^{-1}$.

(2) Cauchy's determinant formula for $x_i = M + 1 + i$, $y_j = j$ gives $\det C = \frac{\prod_{i < j}(j-i)^2}{\prod_{i,j}(M+1+i+j)} = \frac{(\prod_{k=0}^{r-1} k!)^2 \prod_{k=0}^{r-1}(M+k)!}{\prod_{k=0}^{r-1}(M+r+k)!}$. Since $M + r = p + 1$ and $G(n + 1) = \prod_{k=0}^{n-1} k!$, applying $\log G(n + 1) = \sum_{k=0}^{n-1} \log(k!) = \frac{1}{2} n^2 \log n - \frac{3}{4} n^2 + O(n\log n)$ to $2\log G(r+1) + 2\log G(p+2) - \log G(M+1) - \log G(p+r+2)$ yields the stated asymptotics (noting the $-\frac{3}{4}$ constants cancel since $2\alpha^2 + 2 - (1-\alpha)^2 - (1+\alpha)^2 = 0$!).

(3) Integrating by parts $k$ times shows $\int_0^1 t^\ell \frac{d^k}{dt^k}(t^{M+k}(t-1)^k)\,dt = 0$ for $\ell < k$, and for $\ell = k$ gives $(-1)^k k! \int_0^1 t^{M+k}(t-1)^k\,dt = (k!)^2 \frac{(M+k)!}{(M+2k+1)!}$, while the leading coefficient of $P_k^{(0,M)}(2t-1)$ is $\binom{M+2k}{k}$, giving $\int_0^1 P_k^{(0,M)}(2t-1)^2 t^M\,dt = \frac{1}{2k+M+1}$. The two explicit sums follow from Leibniz's rule on $t^{M+k}(t-1)^k$ and direct expansion of $(t-1)^k$. Writing $\varphi_k(t) = \sum_{i=0}^{r-1} U_{k,i} t^i$ gives $U C U^T = I_r$, hence $C^{-1} = U^T U$ and $v^T C^{-1} v = \|U v\|_2^2 = \sum_{k=0}^{r-1} \varphi_k(2)^2 = \sum_{k=0}^{r-1} (2k+M+1) P_k^{(0,M)}(3)^2$.

(4) Since $G = U K U^T \succ 0$ and $\det U = (\det C)^{-1/2}$, $\det G = \det K / \det C \le \prod_{k=0}^{r-1} G_{k,k}$ by Hadamard's inequality. On $[0, 1]$, $(1+t)(2-t) = 2 + t(1-t) \ge 2$, so $\frac{1}{2-t} \le \frac{1+t}{2}$ and $G_{k,k} \le \frac{1}{2}(1 + \int_0^1 t\,\varphi_k(t)^2 t^M\,dt)$. Under $u = 2t - 1 \in [-1, 1]$, the standard diagonal three-term Jacobi coefficient for $P_k^{(0, M)}(u)$ is $\frac{M^2}{(2k+M)(2k+M+2)}$, so $\int_0^1 t\,\varphi_k(t)^2 t^M\,dt = \frac{1}{2} + \frac{M^2}{2(2k+M)(2k+M+2)}$. $\square$

### 4.3 Exact Uvarov–Christoffel reduction and complete Hankel–Padé equivalence

Remarkably, the Loewner and Hadamard bounds on $\det K$ and $v^T K^{-1} v$ can be upgraded to **100% exact finite algebraic identities** by column reduction using the defining relation $2 K_{i,j} - K_{i,j+1} = C_{i,j}$.

**Theorem 4.3 (Exact Uvarov–Christoffel Hankel–Padé Reduction; Paper proof; Finite certificate).** For every integer $M \ge 0$, $r \ge 1$, and $m_M \in \mathbb{Z}$, set $P_{r-1}^{(0, M)}(2t - 1) = \sum_{j=0}^{r-1} c_j t^j$ ($c_j = (-1)^{r-1-j}\binom{r-1}{j}\binom{M+r-1+j}{r-1} \in \mathbb{Z}$) and define the asymmetric Jacobi Padé integral

```math
I_{M, r-1} := \int_0^1 \frac{t^{M + r - 1} (1 - t)^{r - 1}}{(2 - t)^r}\,dt = \int_0^1 \frac{t^M P_{r-1}^{(0, M)}(2t - 1)}{2 - t}\,dt = 2^M P_{r-1}^{(0, M)}(3)\,\ln 2 - \sum_{j=0}^{r-1} c_j s_{M + j} > 0.
```

Then:
1. $\displaystyle \frac{\det K(M, r)}{\det C(M, r)} = r \dbinom{M + 2r - 1}{r}\, I_{M, r-1}$.
2. $\displaystyle v^T K(M, r)^{-1} v = \frac{P_{r-1}^{(0, M)}(3)}{I_{M, r-1}}$.
3. For the clean-window matrix $H_c = \varepsilon v v^T - K(M, r)$ ($\varepsilon = 2^M \ln 2 - m_M$),
   ```math
   \det H_c = (-1)^r\, r \dbinom{M + 2r - 1}{r} \det C(M, r) \cdot \Bigl(I_{M, r-1} - \varepsilon\, P_{r-1}^{(0, M)}(3)\Bigr) = (-1)^r\, r \dbinom{M + 2r - 1}{r} \det C(M, r) \cdot \Lambda_{M, r}(m_M),
   ```
   where $\Lambda_{M, r}(m_M) := m_M P_{r-1}^{(0, M)}(3) - \sum_{j=0}^{r-1} c_j s_{M + j} \in \mathbb{Q}$.
4. When $M = p - r + 1$ ($p$ prime, $1 \le r \le p$), combining (1) with Theorem 3.4(3) cancels $r \binom{p+r}{r} \det C(M, r)$ **identically**:
   ```math
   D_{\mathrm{B3}}(p, r) \cdot \det K(M, r) \;\le\; L_p \cdot I_{M, r-1}, \qquad v_p\bigl(\Lambda_{M, r}(m_M)\bigr) = -1.
   ```

*Proof.* Integrate $\int_0^1 \frac{t^M P_{r-1}^{(0, M)}(2t - 1)}{2 - t}\,dt$ by parts $r - 1$ times using Rodrigues' formula $t^M P_{r-1}^{(0,M)}(2t-1) = \frac{1}{(r-1)!}\frac{d^{r-1}}{dt^{r-1}}(t^{M+r-1}(t-1)^{r-1})$: all boundary terms at $0, 1$ vanish, and $\frac{d^{r-1}}{dt^{r-1}}(2-t)^{-1} = (r-1)! (2-t)^{-r}$, yielding $I_{M, r-1} = \int_0^1 \frac{t^{M+r-1}(1-t)^{r-1}}{(2-t)^r}\,dt > 0$. Expanding $P_{r-1}^{(0,M)}(2t-1) = \sum_{j=0}^{r-1} c_j t^j$ and substituting $T_{M+j} = 2^{M+j}\ln 2 - s_{M+j}$ gives $I_{M,r-1} = 2^M P_{r-1}^{(0,M)}(3)\ln 2 - \sum_{j=0}^{r-1} c_j s_{M+j}$.

Now consider $K(M, r) - \varepsilon v v^T = -H_c$ (for any real $\varepsilon$, including $\varepsilon = 0$). For every $0 \le i < r$ and $1 \le j < r$,

```math
2(K_{i, j-1} - \varepsilon 2^{i+j-1}) - (K_{i, j} - \varepsilon 2^{i+j}) = 2 K_{i, j-1} - K_{i, j} = \int_0^1 \frac{(2 - t) t^{M + i + j - 1}}{2 - t}\,dt = C(M, r)_{i, j-1}.
```

Applying the right-to-left column operations $\mathrm{col}_j \leftarrow 2\,\mathrm{col}_{j-1} - \mathrm{col}_j$ ($j = r - 1, \dots, 1$, determinant factor $(-1)^{r-1}$) transforms $K - \varepsilon v v^T$ into the matrix $\widetilde{K}(\varepsilon) = [\mathbf{t} - \varepsilon v,\ \mathbf{c}_0,\ \dots,\ \mathbf{c}_{r-2}]$, where $\mathbf{t} = (T_M, \dots, T_{M+r-1})^T$ and $\mathbf{c}_k$ is column $k$ of $C(M, r)$. Left-multiply by the lower-triangular orthonormalization matrix $U$ ($U C U^T = I_r$, $\det U = \prod_{k=0}^{r-1} \ell_k = (\det C)^{-1/2}$, where $\ell_k = \sqrt{2k+M+1}\binom{M+2k}{k}$ is the leading coefficient of $\varphi_k(t)$). Since $U C = (U^T)^{-1}$ is upper-triangular with diagonal $(1/\ell_0, \dots, 1/\ell_{r-1})$, row $r - 1$ of $U \widetilde{K}(\varepsilon)$ is zero in columns $1, \dots, r - 1$, and its $(r - 1, 0)$ entry is

```math
\bigl(U(\mathbf{t} - \varepsilon v)\bigr)_{r-1} = \int_0^1 \frac{\varphi_{r-1}(t)\, t^M}{2 - t}\,dt - \varepsilon \varphi_{r-1}(2) = \sqrt{2r + M - 1}\,\bigl(I_{M, r-1} - \varepsilon P_{r-1}^{(0, M)}(3)\bigr).
```

Expanding $\det(U \widetilde{K}(\varepsilon))$ along row $r - 1$ yields

```math
(\det C)^{-1/2} (-1)^{r-1} \det(K - \varepsilon v v^T) = (-1)^{r-1} \bigl(U(\mathbf{t} - \varepsilon v)\bigr)_{r-1} \prod_{k=0}^{r-2} \frac{1}{\ell_k} = (-1)^{r-1} \ell_{r-1} (\det C)^{1/2} \bigl(U(\mathbf{t} - \varepsilon v)\bigr)_{r-1}.
```

Cancelling $(-1)^{r-1}$ and multiplying by $(\det C)^{1/2}$, with $\ell_{r-1}\sqrt{2r+M-1} = (M + 2r - 1)\binom{M + 2r - 2}{r - 1} = r \binom{M + 2r - 1}{r}$, yields

```math
\det(K - \varepsilon v v^T) = r \dbinom{M + 2r - 1}{r} \det C(M, r) \cdot \Bigl(I_{M, r-1} - \varepsilon P_{r-1}^{(0, M)}(3)\Bigr).
```

Setting $\varepsilon = 0$ proves (1). Comparing with $\det(K - \varepsilon v v^T) = \det K \cdot (1 - \varepsilon v^T K^{-1} v)$ as linear polynomials in $\varepsilon$ proves (2) and (3). For (4), multiplying (1) by Theorem 3.4(3) gives $D_{\mathrm{B3}}(p, r)\det K(M, r) \le \frac{L_p}{r \binom{p+r}{r}} \cdot r\binom{p+r}{r} I_{M, r-1} = L_p I_{M, r-1}$; and since $M + j < p$ for $j < r - 1$ while $c_{r-1} = \binom{p + r - 1}{r - 1}$ is coprime to $p$ ($r \le p$), $p \Lambda_{M, r}(m_M) \equiv -c_{r-1} \not\equiv 0 \pmod p$, so $v_p(\Lambda_{M, r}(m_M)) = -1$. $\square$

### 4.4 Non-asymptotic bounds, unconditional dyadic irrationality measure and comparison with classical literature

**Lemma 4.4 (Non-asymptotic generating & saddle bounds; Paper proof).** For any $\alpha \in (0, 1)$, let

```math
x_*(\alpha) := \frac{-(1 + \alpha) + \sqrt{\alpha^2 + 6\alpha + 1}}{2} \in (0, \alpha), \qquad g(\alpha) := \alpha \log\!\left(\frac{1 + x_*}{x_*}\right) - \log(1 - x_*).
```

Then for every $p \ge 2$ and $1 \le r \le p$ with $M = p - r + 1$ and $\alpha_0 := (r - 1)/p \in [0, 1)$:

```math
I_{M, r-1} \le e^{-g(\alpha_0) p} \qquad \text{and} \qquad P_{r-1}^{(0, M)}(3) \le e^{g(\alpha_0) p}
```

(with $g(0) := 0$). Furthermore, for $r \ge 2$ ($\alpha_0 \in (0, 1)$) with $t_* := 1 - x_*(\alpha_0) \in (0, 1)$,

```math
I_{M, r-1} \ge \frac{\min(t_*,\ 1 - t_*)}{2 e\, p}\, e^{-g(\alpha_0) p}.
```

Moreover, as $p \to \infty$ with $r/p \to \alpha \in (0, 1)$, $\frac{1}{p}\log P_{r-1}^{(0, M)}(3) \to g(\alpha)$, $\frac{1}{p}\log I_{M, r-1} \to -g(\alpha)$, and $\frac{1}{p}\log(v^T K^{-1} v) = \frac{1}{p}\log(v^T C^{-1} v) + o(1) \to 2 g(\alpha)$.

*Proof.* For the upper bound on $I_{M, r-1}$: on $[0, 1]$, $\frac{t^p (1-t)^{r-1}}{(2-t)^r} = \frac{1}{2-t} \bigl(\frac{t(1-t)^{\alpha_0}}{(2-t)^{\alpha_0}}\bigr)^p = \frac{1}{2 - t} e^{p \phi(t)}$, where $\phi(t) = \log t + \alpha_0 \log(1-t) - \alpha_0 \log(2-t)$. Differentiating gives $\phi'(t) = 0 \iff t^2 - (3 + \alpha_0)t + 2 = 0$, whose unique root in $(0, 1)$ is $t_* = 1 - x_*(\alpha_0)$, giving $-\phi(t_*) = g(\alpha_0)$. Since $\frac{1}{2 - t_*} < 1$, $I_{M, r-1} \le \max_{t \in [0, 1]} \frac{t^p (1-t)^{r-1}}{(2-t)^r} < e^{-g(\alpha_0) p}$.

For the matching lower bound on $I_{M, r-1}$ ($r \ge 2$): set $\eta := \min(t_*, 1 - t_*)$ and $\delta := \frac{\eta}{2p}$. For every $t \in [t_* - \delta, t_* + \delta] \subset (0, 1)$, we have $t \ge t_*/2$ and $1 - t \ge (1 - t_*)/2$, while $\phi''(t) = -\frac{1}{t^2} - \alpha_0\bigl(\frac{1}{(1-t)^2} - \frac{1}{(2-t)^2}\bigr) \in \bigl(-(\frac{1}{t^2} + \frac{\alpha_0}{(1-t)^2}),\, 0\bigr)$, so $-\phi''(t) \le \frac{4}{t_*^2} + \frac{4\alpha_0}{(1-t_*)^2}$. By Taylor's theorem at $t_*$ ($\phi'(t_*) = 0$), every $t \in [t_* - \delta, t_* + \delta]$ satisfies $\phi(t) \ge -g(\alpha_0) - \frac{1}{2}\bigl(\frac{4}{t_*^2} + \frac{4\alpha_0}{(1-t_*)^2}\bigr)\delta^2 \ge -g(\alpha_0) - \frac{1 + \alpha_0}{2 p^2} > -g(\alpha_0) - \frac{1}{p^2}$. Integrating $\frac{1}{2 - t} \ge \frac{1}{2}$ over $[t_* - \delta, t_* + \delta]$ (length $2\delta = \eta/p$) gives $I_{M, r-1} \ge \frac{\eta}{2p} e^{-g(\alpha_0) p - 1/p} \ge \frac{\eta}{2 e\, p} e^{-g(\alpha_0) p}$.

For $P_{r-1}^{(0, M)}(3)$: for every $y > 0$, since all summands are positive,

```math
P_{r-1}^{(0, M)}(3) = \sum_{j=0}^{r-1} \binom{r - 1}{j} 2^{r - 1 - j} y^j \cdot \binom{p}{j} y^{-j} \le \left(\sum_{j=0}^{r-1} \binom{r - 1}{j} 2^{r - 1 - j} y^j\right)\left(\sum_{j=0}^{p} \binom{p}{j} y^{-j}\right) = (2 + y)^{r-1} (1 + y^{-1})^p.
```

Setting $y = \frac{1 - x_*(\alpha_0)}{x_*(\alpha_0)} > 0$ gives $2 + y = \frac{1 + x_*}{x_*}$ and $1 + y^{-1} = \frac{1}{1 - x_*}$, so $(2 + y)^{r-1}(1 + y^{-1})^p = e^{g(\alpha_0) p}$. Conversely, retaining the single positive summand $j_0 = \lfloor x_*(\alpha_0) p \rfloor \in \{0, \dots, r - 1\}$ in $P_{r-1}^{(0, M)}(3)$ and applying Stirling's formula (using $x_*^2 + (1+\alpha_0)x_* - \alpha_0 = 0 \implies (\alpha_0 - x_*)(1 - x_*) = 2 x_*^2$ and $\frac{2\alpha_0}{\alpha_0 - x_*} = \frac{1 + x_*}{x_*}$) gives $\frac{1}{p}\log P_{r-1}^{(0, M)}(3) \ge g(\alpha_0) + O(\frac{\log p}{p})$. The limit for $v^T K^{-1} v = P_{r-1}^{(0, M)}(3)/I_{M, r-1}$ (and $v^T C^{-1} v$ via Prop. 4.2(1)) follows immediately. $\square$

**Theorem 4.5 (Unconditional dyadic irrationality measure & run bound from B1+B3+B4; Paper proof + PNT external).** Let $\alpha_* = 0.442847\ldots$ be the unique root in $(0, 1)$ of $g(\alpha_*) = 1$, and set

```math
\mu_2^{\mathrm{Hankel}} := 1 + \frac{2}{(1 - \alpha_*) \ln 2} = 6.178813\ldots
```

Then for every $\eta > 0$, all sufficiently large integers $M$, and every integer $m \in \mathbb{Z}$,

```math
\bigl|2^M \ln 2 - m\bigr| \ge 2^{-(\mu_2^{\mathrm{Hankel}} - 1 + \eta) M} = 2^{-(5.178813\ldots + \eta) M}.
```

Consequently:
1. Every binary digit run of equal digits in $\ln 2$ starting after position $M$ has length at most $(5.178813\ldots + o(1)) M$.
2. Among the first $N$ binary digits of $\ln 2$, there are at least $\bigl(\frac{1}{\log_2 \mu_2^{\mathrm{Hankel}}} - o(1)\bigr) \log_2 N \approx 0.3806 \log_2 N$ binary transitions (nearly doubling `CC-05`'s Lean transition constant $\frac{1}{\log_2 34} \approx 0.1966$).

*Proof.* Fix $\alpha \in (\alpha_*, 1)$ close to $\alpha_*$, so $g(\alpha) > 1$. For large $M$, by PNT (or Bertrand + prime gaps $p_{k+1} - p_k = o(p_k)$) pick a prime $p = \frac{M}{1 - \alpha}(1 + o(1))$ with $r := p - M + 1 \le p$, so $\alpha_0 = (r - 1)/p = \alpha + o(1)$. Put $m_{M+k} := 2^k m$ and form $H_c$. By Theorem 1.1, $\det H_c \ne 0$; by Theorem 3.3 and Theorem 4.3(4),

```math
\frac{1}{D_{\mathrm{B3}}(p, r)} \le |\det H_c| = \det K(M, r) \cdot \bigl|1 - \varepsilon\, v^T K(M, r)^{-1} v\bigr| \le \det K(M, r) \cdot \bigl(1 + |\varepsilon|\, v^T K(M, r)^{-1} v\bigr),
```

and equivalently $|\Lambda_{M, r}(m)| \ge 1/L_p$, where $L_p I_{M, r-1} \le L_p e^{-g(\alpha_0) p} = e^{(1 - g(\alpha) + o(1)) p} \to 0$. For large $M$, $L_p I_{M, r-1} \le \frac{1}{2}$, hence by Theorem 4.3(1)–(4) and Lemma 4.4,

```math
|\varepsilon| \ge \frac{1 - D_{\mathrm{B3}}(p, r)\det K(M, r)}{D_{\mathrm{B3}}(p, r)\det K(M, r) \cdot v^T K(M, r)^{-1} v} \ge \frac{1 - L_p I_{M, r-1}}{L_p \, P_{r-1}^{(0, M)}(3)} \ge \frac{1}{2 L_p \, e^{g(\alpha_0) p}} = \exp\!\Bigl(-\bigl(1 + g(\alpha) + o(1)\bigr) p\Bigr).
```

(Note that the same inequality holds with zero Szegő theory using only the weaker Matrix Determinant Lemma upper bounds: trivial Loewner $\det K < \det C$ gives $\alpha_C = 0.542211$, $\mu_2 = 8.258694$; linear Hadamard–Jacobi gives $\alpha_{\mathrm{HL}} = 0.467206$, $\mu_2 = 6.621956$; quadratic Hadamard–Jacobi gives $\alpha_{\mathrm{HQ}} = 0.453074$, $\mu_2 = 6.360478$.) Letting $\alpha \to \alpha_*^+$ (where $g(\alpha_*) = 1$, so $1 + g(\alpha_*) = 2$ and $p/M \to \frac{1}{1 - \alpha_*}$) yields $|\varepsilon| \ge 2^{-(2/((1-\alpha_*)\ln 2) + o(1)) M}$. For (1)–(2), a run of $L$ equal binary digits after position $M$ gives $|\varepsilon| < 2^{-L}$ (Prop. 4.1(2)), forcing $L \le (\mu_2^{\mathrm{Hankel}} - 1 + o(1)) M$, so each transition at $M$ is followed by another by position $(\mu_2^{\mathrm{Hankel}} + o(1)) M$. $\square$

*(Effective version remark)* Replacing PNT by Rosser–Schoenfeld's completely explicit $\psi(p) < 1.03883 p$ (for all $p \ge 1$) and prime-gap bounds yields a completely effective bound at $g(\alpha_{\mathrm{RS}}) > 1.03883$.

### 4.5 Comparison with classical Padé / Legendre irrationality measures for $\ln 2$

| Method / Author | Integrand / Denominator | Threshold $\alpha_*$ | Run cap $c_{\mathrm{run}}$ ($|2^M \ln 2 - m| \ge 2^{-c M}$) | Exponent $\mu$ (or $\mu_2$) |
| --- | --- | --- | --- | --- |
| `CC-05` (Lean, repository) | Auxiliary integral | — | $33$ (window $[n, 34n)$) | window factor $34$ ($0.1966 \log_2 N$) |
| **B1+B3+B4 (Loewner $\det K < \det C$)** | Asymmetric BBP Hankel, $L_p$ | $0.542211$ | $7.258694$ | $\mu_2 \le 8.258694$ |
| **B1+B3+B4 (Linear Hadamard–Jacobi)** | Asymmetric BBP Hankel, $L_p$ | $0.467206$ | $5.621956$ | $\mu_2 \le 6.621956$ |
| **B1+B3+B4 (Exact Uvarov–Christoffel)** | $I_{M, r-1}$ ($M = (1-\alpha)p$), $L_p$ | $0.442847$ | $5.178813$ | $\mu_2 \le 6.178813$ |
| Danilov (1978); Alladi–Robinson (1980) | Symmetric Legendre ($M = 0$), $L_r$ | — | $3.622101$ | $\mu \le 4.622101$ |
| G. V. Chudnovsky (1979) | Hermite–Padé / differential method | — | $3.1344$ | $\mu \le 4.1344$ |
| Rhin (1987) | Arithmetical prime-factor refinement | — | $3.0765$ | $\mu \le 4.0765$ |
| Rukhadze (1987); Hata (1990) | Legendre-type + prime divisibility | — | $2.891400$ | $\mu \le 3.891400$ |
| Marcovecchio (2009) (via Rhin–Viola 1996) | Permutation-group double integral | — | $2.574554$ | $\mu \le 3.574554$ |
| Optimal hypothetical ($\mu = 2$) | Dirichlet limit | — | $1.000000$ | $\mu = 2$ |

*Why the prime-centered BBP Hankel determinant stops at $6.178813$ rather than Alladi–Robinson's $4.622101$:*
1. **Exact equivalence to 1-D asymmetric Jacobi Padé:** By Theorem 4.3, forming the $r \times r$ Hankel determinant $\det H_c$ adds **no new arithmetic amplification** beyond the 1-dimensional asymmetric shifted-Jacobi form $\Lambda_{M, r}(m_M) = I_{M, r-1} - \varepsilon P_{r-1}^{(0,M)}(3)$; the $r \times r$ matrix prefactor $(-1)^r r\binom{p+r}{r}\det C(M, r)$ cancels identically against the B3 denominator bound.
2. **Asymmetric denominator penalty ($L_{M+r-1}$ vs $L_r$):** Anchoring the BBP window at $M = (1-\alpha)p$ forces the integrand to include $t^M$ and pay common denominator $L_{M+r-1} = L_p \sim e^p$, whereas Alladi–Robinson (1980) takes $M = 0$ (symmetric Legendre polynomial $P_r(2t-1)$), pays only $L_r \sim e^r$, and then compares with $m/2^M$ externally at $r \approx \frac{\ln 2}{2\ln(1+\sqrt 2) - 1} M \approx 0.9088 M$. What the prime-centered Hankel construction gains in return is **one-shot unconditional nonvanishing** ($v_p(\Lambda_{M,r}) = -1$ for every $m \in \mathbb{Z}$, needing no second approximant $r + 1$). Note also Rivoal (2007), who analyzed restricted-denominator irrationality measures of $\log(1 \pm a/b)$ (including powers of $b$ and $d_{\lfloor \nu m \rfloor}^s B^m$) via upper Padé tables.

---

## 5. B5: Adversarial Test Against `GF-47` Reset Countermodels and Local Limitation Theorem

Recall `GF-47` Theorem 3.6: for $n_0 \ge 240$ and $n_{i+1} = \lfloor \frac{3}{2} n_i \rfloor$, there exist rational states $\tilde{s}_n = s_n + 2^{n - n_i} \delta_i$ on each block $[n_i, n_{i+1})$ with $\delta_i = a_i / M_i$, $M_i = \prod_{n_i/2 < q \le n_i} q$, such that: (i) $\operatorname{den}(\tilde{s}_n) = Q_n$ for every $n \ge n_0$; (ii) $\tilde{s}_{n+1} = 2 \tilde{s}_n + \frac{1}{n+1}$ holds identically inside every block $[n_i, n_{i+1})$ (failing only at the $O(\log N)$ resets $n_i$); (iii) writing $y_i = \ln 2 + 2^{-n_i}\delta_i$, we have $\tilde{s}_n = 2^n y_i - T_n$ and $\|\tilde{s}_n\| \le (n_i^2 + 2) 2^{-0.05 n_i - 1} + 1/n \to 0$, so $S_N(1; \tilde{x}) \to 1$ and $D^+(\tilde{x}) = 1$.

**Theorem 5.1 (Reset-Countermodel Survival and Local Hankel Limitation Theorem; Paper proof; Finite certificate).**
Let $(\tilde{s}_n)_{n \ge n_0}$ be any `GF-47` Theorem 3.6 countermodel with reset schedule $n_{i+1} = \lfloor \frac{3}{2} n_i \rfloor$ ($n_0 \ge 240$), and let $\tilde{m}_n = \mathrm{round}(\tilde{s}_n)$ (which automatically satisfies $\tilde{m}_{n+1} = 2 \tilde{m}_n$ throughout every block $[n_i, n_{i+1})$ for large $i$, and for all $n \in [240, 360) \cup [360, 540)$).

1. *(Complete survival inside reset-free blocks)* Let $p$ be any prime and $r \ge 1$ such that the prime-centered Hankel window $[M, M + 2r - 2] = [p - r + 1, p + r - 1]$ lies inside a single reset-free block $[n_i, n_{i+1})$. Put $\widetilde{H}_{j,k} = \tilde{s}_{M+j+k} - \tilde{m}_{M+j+k}$ ($0 \le j, k < r$) and $\tilde{\varepsilon} = 2^M y_i - \tilde{m}_M$. Then **all four theorems B1, B2, B3, and B4 hold verbatim for $\widetilde{H}$**:
   - **B1:** $v_p(\det \widetilde{H}) = -r$ and $\det \widetilde{H} \ne 0$;
   - **B2 & B3:** $\operatorname{den}(\det \widetilde{H}) \mid D_{\mathrm{B3}}(p, r) \mid D_{\mathrm{row}}(p, r)$ (by Theorem 3.3);
   - **B4:** $\widetilde{H} = \tilde{\varepsilon} v v^T - K(M, r)$ and $\det \widetilde{H} = (-1)^r r \binom{p+r}{r} \det C(M, r) \cdot \bigl(I_{M, r-1} - \tilde{\varepsilon} P_{r-1}^{(0, M)}(3)\bigr)$.
2. *(Exact reset-ratio barrier: activation threshold vs exclusion threshold)*
   - *(a) Activation (vacuity) threshold $\rho_*^{\mathrm{Hankel}} = 2.5897$:* Any reset-free block of multiplicative ratio $\rho = n_{i+1}/n_i > 1$ restricts every contained prime-centered Hankel window to
     ```math
     \frac{p + r - 1}{p - r + 1} < \rho \implies \alpha = \frac{r}{p} < \alpha_{\max}(\rho) := \frac{\rho - 1}{\rho + 1} + O\!\left(\frac{1}{p}\right).
     ```
     Comparing against the B1+B3+B4 **activation** threshold $\alpha_* = 0.442847\ldots$ (multiplicative block ratio $\rho_*^{\mathrm{Hankel}} = \frac{1 + \alpha_*}{1 - \alpha_*} = 2.589679\ldots$, where $g(\alpha_*) = 1$):
     ```math
     \underbrace{\rho_{\mathrm{GF\text{-}47}} = 1.500}_{\alpha < 0.2000} \;<\; \underbrace{\rho_{\mathrm{top\text{-}band}} = 1 + \frac{1}{2\ln 2} = 1.7213}_{\alpha < 0.2651} \;<\; \underbrace{\rho_{\mathrm{info}} = 1 + \frac{1}{\ln 2} = 2.4427}_{\alpha < 0.4191} \;<\; \underbrace{\rho_*^{\mathrm{Hankel}} = 2.5897}_{\alpha_* = 0.4428}.
     ```
     Thus for every window inside a reset-free block of ratio $\rho < \rho_*^{\mathrm{Hankel}}$ (including every `GF-47` Theorem 3.6 block, and even a hypothetical full-denominator reset block of `GF-47` Open Question 4), $L_p I_{M, r-1} = e^{(1 - g(\alpha) + o(1)) p} \to +\infty$ (at $\alpha = 0.20$, $1 - g(0.20) \approx +0.4301 > 0$), so the B1+B3+B4 lower bound $\frac{1}{D_{\mathrm{B3}}} \le \det K (1 + |\tilde{\varepsilon}| v^T K^{-1} v)$ is trivially satisfied already at $\tilde{\varepsilon} = 0$ and imposes **no nontrivial lower bound** on $|\tilde{\varepsilon}|$.
   - *(b) True exclusion threshold $\rho_{\mathrm{excl}}^{\mathrm{Hankel}} = \mu_2^{\mathrm{Hankel}} \approx 6.1788$ (bits/index gap $1.44$ vs $5.18$):* Importantly, $\rho_*^{\mathrm{Hankel}} = 2.5897$ is **only the activation (positivity/nontriviality) threshold** of the Hankel form; actually *excluding* (contradicting) a clean reset-free block $[n_i, n_{i+1})$ of ratio $\rho$ requires far more. Inside a clean block ($|\tilde{s}_n - \tilde{m}_n| \le \frac{1}{2}$ with $\tilde{m}_{n+1} = 2\tilde{m}_n$ throughout $[n_i, n_{i+1})$), $\tilde{s}_n - \tilde{m}_n = 2^{n-M}\tilde{\varepsilon} - T_n$ evaluated at $n = n_{i+1} - 1$ forces $|\tilde{\varepsilon}| \le 2^{-(n_{i+1} - 1 - M)}$ (strongest at $M = n_i$, giving $|\tilde{\varepsilon}| \le 2^{-((\rho - 1) M - 1)}$). Meanwhile, B1+B3+B4 at any contained window $[M, p+r-1] \subset [n_i, n_{i+1})$ with $r/p \to \alpha > \alpha_*$ yields at best $|\tilde{\varepsilon}| \ge 2^{-(c_{\mathrm{run}}(\alpha) + o(1)) M}$, where $c_{\mathrm{run}}(\alpha) = \frac{1 + g(\alpha)}{(1 - \alpha)\ln 2}$ is strictly increasing on $[\alpha_*, 1)$ with $c_{\mathrm{run}}(\alpha_*) = \mu_2^{\mathrm{Hankel}} - 1 = 5.178813\ldots$. Hence a contradiction requires
     ```math
     \rho > \inf_{\alpha \ge \alpha_*} \max\!\left(\frac{1 + \alpha}{1 - \alpha},\; 1 + c_{\mathrm{run}}(\alpha)\right) = 1 + c_{\mathrm{run}}(\alpha_*) = \mu_2^{\mathrm{Hankel}} = 6.178813\ldots,
     ```
     i.e., **$\rho - 1 > \mu_2^{\mathrm{Hankel}} - 1 \approx 5.1788$** (at $\alpha_*$, the window-fit constraint $\rho > 2.5897$ is slack). Equivalently, any `GF-47`-type reset at $n_i$ with denominator dividing $L_{n_i}$ carries at most $\log_2 L_{n_i} = (\frac{1}{\ln 2} + o(1)) n_i \approx 1.4427\, n_i$ bits of resolution, whereas B1+B3+B4 requires $> 5.1788\, n_i$ bits to contradict a block: the true gap is **$1.44$ vs $5.18$ bits per index** ($\rho_{\mathrm{info}} = 2.4427$ vs $\rho_{\mathrm{excl}}^{\mathrm{Hankel}} = 6.1788$), **not** a near miss $2.4427$ vs $2.5897$. On the explicit countermodel blocks certified in `scripts/phase26_hankel_ln2.py`, at $M = 240$ in $[240, 360)$ we have $|\tilde{\varepsilon}| \in (2^{-166}, 2^{-165})$ ($\approx 2^{-165.7}$, matching $1/M_0 \approx 2^{-164.5}$) versus the Hankel exclusion threshold $2^{-5.1788 \cdot 240} \approx 2^{-1243}$; at $M = 360$ in $[360, 540)$, $|\tilde{\varepsilon}| \in (2^{-251}, 2^{-250})$ ($\approx 2^{-250.3}$) versus $2^{-1864}$.
3. *(Reset-crossing breakdown & zero-reset limitation)* If a Hankel window crosses a reset $n_i$, the recurrence defect $\eta_i = \delta_i - 2^{n_i - n_{i-1}}\delta_{i-1}$ injects primes dividing $M_i M_{i-1}$ across the anti-diagonal $M + j + k = n_i$, breaking both B2/B3 (amplifying reset primes to pole order $\ge 2$) and B4 (destroying the rank-1 structure $\varepsilon v v^T - K$). Finally, **even with zero resets** (actual $\ln 2$), the B1+B3+B4 framework extracts only a single-block lower bound $|\varepsilon| \ge 2^{-(5.178813 + o(1)) M}$, ruling out clean windows of length $L > 5.178813 M$ (linear runs) while remaining completely blind to runs of length $o(M)$ and to $D^+(\ln 2; 2) \le 0.9999$ (`GF-28` Corollary 3.2).

*Proof.* (1) For $r \ge 2$, $p = M + r - 1 > M \ge n_i$, so $p \notin (n_i/2, n_i]$, hence $p \nmid M_i$ and $\delta_i \in \mathbb{Z}_{(p)}$. Therefore $p \widetilde{H}_{j,k} \equiv p H_{j,k} \pmod{p \mathbb{Z}_{(p)}}$ and Theorem 1.1 applies verbatim. (For $r = 1$, $M = p \ge n_i$ and `GF-47` Theorem 3.6(1) preserves $v_p(\operatorname{den}(\tilde{s}_p)) = v_p(Q_p) = 1$, so $v_p(\det \widetilde{H}) = -1$ still holds.) Because $\tilde{s}_{n+1} = 2 \tilde{s}_n + \frac{1}{n+1}$ holds throughout $[M, M + 2r - 2]$ and $\operatorname{den}(\tilde{s}_{M+k}) = Q_{M+k} \mid L_p$, the row-reduced matrix $\widetilde{H}^{(1)} = L \widetilde{H}$ has the exact same row-$0$ denominator divisors and the exact same rows $i \ge 1$ as $H^{(1)}$, so Theorems 2.1 and 3.3 apply verbatim (including $D_{\mathrm{B3}}(p, r) \mid D_{\mathrm{row}}(p, r)$). Finally, $\tilde{s}_n = 2^n y_i - T_n$ and $\tilde{m}_{M+t} = 2^t \tilde{m}_M$ give $\widetilde{H}_{j,k} = \tilde{\varepsilon} 2^{j+k} - T_{M+j+k} = (\tilde{\varepsilon} v v^T - K)_{j,k}$, so Theorem 4.3 applies verbatim.

(2) For (a), $n_i \le p - r + 1 < p + r - 1 < \rho n_i$ implies $\frac{p + r - 1}{p - r + 1} < \rho$, hence $\alpha = r/p < \frac{\rho - 1}{\rho + 1} + O(1/p)$. For $r = 1$, $I_{M, 0} = T_p > \frac{1}{p+2}$ gives $L_p I_{M, 0} \to +\infty$; for $r \ge 2$ with $\alpha_0 = (r - 1)/p$ bounded away from $\alpha_*$ below, Lemma 4.4's non-asymptotic lower bound $I_{M, r-1} \ge \frac{\min(t_*, 1-t_*)}{2 e p} e^{-g(\alpha_0) p}$ together with PNT ($\log L_p = (1 + o(1)) p$) and $g(\alpha) < 1$ proves $L_p I_{M, r-1} \to +\infty$. For (b), at $n = n_{i+1} - 1 \ge 2$, $2^{n_{i+1}-1-M}|\tilde{\varepsilon}| = |\tilde{s}_{n_{i+1}-1} - \tilde{m}_{n_{i+1}-1} + T_{n_{i+1}-1}| \le \frac{1}{2} + \frac{1}{n_{i+1}} \le 1$, so $|\tilde{\varepsilon}| \le 2^{-(n_{i+1}-1-M)} \le 2^{-((\rho - 1)M - 1)}$ (maximized at $M = n_i$). Differentiating $g(\alpha) = \alpha\log\frac{1+x_*}{x_*} - \log(1-x_*)$ gives $g'(\alpha) = \log\frac{1+x_*(\alpha)}{x_*(\alpha)} > 0$ (the $x_*'(\alpha)$ coefficient $\frac{-\alpha}{x_*(1+x_*)} + \frac{1}{1-x_*} = \frac{x_*^2 + (1+\alpha)x_* - \alpha}{x_*(1+x_*)(1-x_*)} = 0$ vanishes by the saddle equation), so $c_{\mathrm{run}}(\alpha) = \frac{1+g(\alpha)}{(1-\alpha)\ln 2}$ is strictly increasing on $[\alpha_*, 1)$. Hence $\inf_{\alpha \ge \alpha_*} \max\bigl(\frac{1+\alpha}{1-\alpha}, 1 + c_{\mathrm{run}}(\alpha)\bigr)$ is attained at $\alpha = \alpha_*$ with value $1 + c_{\mathrm{run}}(\alpha_*) = \mu_2^{\mathrm{Hankel}} = 6.178813\ldots$, and the certified $|\tilde{\varepsilon}|$ enclosures on $[240, 360)$ and $[360, 540)$ are verified in `scripts/phase26_hankel_ln2.py`.

(3) At $n = n_i$, $\tilde{s}_{n_i} - 2 \tilde{s}_{n_i - 1} = \frac{1}{n_i} + \eta_i$ where $\eta_i$ has poles at primes $q \mid M_i M_{i-1}$ lying below $M$; this destroys the clean row-difference $\frac{1}{M+i+j} - \Delta \tilde{m}$ along the anti-diagonal $M + j + k = n_i$, as certified explicitly in `scripts/phase26_hankel_ln2.py` at $(p, r) = (359, 3)$ crossing reset $360$ ($30$ primes dividing $M_1$ acquire amplified pole $v_q(\det \widetilde{H}) \le -2$). The zero-reset statement follows from Theorem 4.5 and `GF-28` Corollary 3.2 (Kempner's number $\kappa \in K_2$ satisfies $\mu(\kappa) = 2$ and has $D_N(\kappa; 2) \to 1$). $\square$

---

## 6. B6: Complete Amplification-Cost Ledger

| Ledger Row | **B1 + B2** (Prime pole + Row/Double clearing) | **B1 + B3** (Prime pole + Rank-sensitive local lemma) | **B1 + B3 + B4** (Full synthesis + Uvarov–Christoffel) |
| --- | --- | --- | --- |
| **1. Arithmetic signal** | Exact pole $v_p(\det H) = -r$, $\det(p H) \equiv (-1)^{r(r-1)/2} \pmod p$, $\det H \ne 0$ (amplified denominator pole, **zero** numerator divisibility gain). | Same exact pole $v_p(\det H) = -r$ and $\det H \ne 0$, plus local rank drop $s(t) = \min(t, 2r-1-t) + \mathbf{1}_{\rho_{\mathrm{maj}}\ne 0}$ and block-rank collapse at all $q$. | Same $v_p(\det H_c) = -r \iff v_p(\Lambda_{M,r}(m_M)) = -1$, giving one-shot $L_p \Lambda_{M,r}(m_M) \in \mathbb{Z} \setminus \{0\}$ with zero numerator gain beyond $|L_p \Lambda| \ge 1$. |
| **2. Analytic signal** | None used (purely $p$-adic / rational). | None used (purely $q$-adic / rational). | Positive-definite $K(M,r)$ ($\frac{1}{2}C \prec K \prec C$), $\det K = r\binom{p+r}{r}\det C \cdot I_{M,r-1}$, $I_{M,r-1} \asymp e^{-g(\alpha) p}$, $v^T K^{-1} v = P_{r-1}^{(0,M)}(3)/I_{M,r-1} \asymp e^{2g(\alpha)p}$. |
| **3. Dimension** | Arbitrary $1 \le r \le p$; sublinear sweet spot $r \asymp \sqrt{p/\log p}$ gives $\log D_{\mathrm{row}} = O(p)$. | Arbitrary $1 \le r \le p$; linear scale $r = \alpha p$ ($\alpha > \alpha_C = 0.5422$) sufficient for $D_{\mathrm{B3}}\det C < 1$. | Optimal at linear scale $r = (\alpha_* + o(1)) p$, $\alpha_* = 0.442847\ldots$ ($M = (1-\alpha_*)p$, activation window ratio $\rho_* = 2.5897$). |
| **4. Denominator cost** | $\log D_{\mathrm{row}} = \psi(p) + r(r-1)\log(p/r) + \kappa_D r^2$; at $r = p$, $\frac{3}{2} p^2$ beats naive $r\psi(p+r) \sim r p$ but exceeds $-\log \det C \approx 2\ln 2\cdot p^2$ by $+0.1137 p^2$ (proved at $\alpha = 1$; finite measurement / heuristic for $\alpha \in (0, 1)$). | $\operatorname{den}(\det H) \mid D_{\mathrm{B3}} \mid D_{\mathrm{row}}$ and $D_{\mathrm{B3}} \mid \frac{L_p}{r\binom{p}{r}\det C(M-1,r)}$; cancels ALL $\Theta(p^2)$ terms against $-\log \det C$ identically (at $r=p$: $\frac{3}{2}p^2 \to 2\ln 2 \cdot p^2$), leaving linear cost $\Phi_{\mathrm{B3}}(\alpha) p$. | Exact cancellation $D_{\mathrm{B3}}\det K \le L_p I_{M,r-1} = e^{(1 - g(\alpha) + o(1)) p}$; effective denominator cost reduces completely to $L_p = e^{(1 + o(1)) p}$. |
| **5. Approximation error** | Not bounded (no real input). | Not bounded (no real input). | Clean-window error $|\varepsilon| = |2^M \ln 2 - m_M|$ enters linearly via $\det H_c = (-1)^r \det K (1 - \varepsilon v^T K^{-1} v)$, competing against $I_{M,r-1}/P_{r-1}^{(0,M)}(3) \asymp e^{-2g(\alpha)p}$. |
| **6. Exceptional indices** | **Zero** for nonvanishing (holds for every prime $p$, every $1 \le r \le p$, every $m_n \in \mathbb{Z}$). | **Zero** for nonvanishing and divisibility (every $p, r, m_n$; `GF-47` drop events in $s_M$ can weakly lower $e_0(q)$ inside $D_{\mathrm{B3}}$, while Thm 3.2(2)'s single-insertion rank drops are not built into $D_{\mathrm{B3}}$ or used in Thm 4.5). | **Zero** exceptional $M$ or $m \in \mathbb{Z}$ (holds uniformly for all sufficiently large $M$ via prime $p \approx M/(1-\alpha_*)$, with no consecutive-index fallback needed). |
| **7. Uniformity** | Uniform over all $m_n \in \mathbb{Z}$ and all primes $p$. | Uniform over all $m_n \in \mathbb{Z}$ and all primes $p, q$ (including $q = 2$). | Uniform over all $m \in \mathbb{Z}$ and all $M \ge M_0(\eta)$; survives verbatim inside any reset-free `GF-47` block (vacuous below activation ratio $\rho_* = 2.5897$; contradicting a clean block requires $\rho > \rho_{\mathrm{excl}} = \mu_2^{\mathrm{Hankel}} \approx 6.1788$, i.e. $5.18$ vs $1.44$ bits/index). |
| **8. Net result & dominant loss** | Unconditional $\det H \ne 0$ and $\log D_{\mathrm{row}} = O(p)$ at $r \asymp \sqrt{p/\log p}$. **Dominant loss:** at $r = p$, $+0.1137 p^2$ excess over $-\log\det C$ prevents $D_{\mathrm{row}}\det C < 1$ (and finite measurements/heuristics indicate no linear-scale win at $\alpha \in (0, 1)$, motivating B3). | Unconditional $\det H \ne 0$ and exact $\Theta(p^2)$ cancellation $D_{\mathrm{B3}}\det C \le L_p / (r\binom{p+r}{r}) < 1$ for $\alpha > 0.5422$. **Dominant loss:** purely arithmetic (no analytic upper bound on $|\det H|$). | Unconditional **$\mu_2(\ln 2) \le 6.178813$** ($|2^M\ln 2 - m| \ge 2^{-(5.1788 + o(1))M}$, $\ge 0.3806 \log_2 N$ transitions). **Two exact barriers:** (i) asymmetric shift penalty $L_{M+r-1}$ vs $L_r$ raises $\mu$ from Alladi–Robinson's $4.6221$ to $6.1788$; (ii) single-block linear-run barrier cannot touch $D^+(\ln 2; 2) < 1$ or exclude `GF-47`-type resets (needs $\rho > \rho_{\mathrm{excl}} \approx 6.1788$, i.e. $5.18$ vs $1.44$ bits/index, far above $\rho_{\mathrm{info}} = 2.4427$; vacuous already below $\rho_* = 2.5897$). |

---

## 7. B7: Extensions to $\pi$ (Base 16 BBP), $e$ (Factorial Prefixes), and $\zeta(3)$ (Broadhurst Base $2^{12}$)

### 7.1 $\pi$ (base-16 BBP formula, `CC-08`)

Recall $\pi = \sum_{k=0}^\infty 16^{-k} r_k$ with $r_k = \frac{4}{8k+1} - \frac{2}{8k+4} - \frac{1}{8k+5} - \frac{1}{8k+6} = \int_0^1 t^{8k} P_\pi(t)\,dt$, $P_\pi(t) = 4 - 2t^3 - t^4 - t^5 = (1 - t)(4 + 4t + 4t^2 + 2t^3 + t^4) > 0$ on $[0, 1)$, and shifted prefixes $y_n = \sum_{k=0}^n 16^{n-k} r_k$ obeying $y_{n+1} = 16 y_n + r_{n+1}$ and $16^n \pi = y_n + T_n^{(\pi)}$, where

```math
T_n^{(\pi)} = \int_0^1 \frac{t^{8n+8} P_\pi(t)}{16 - t^8}\,dt = \int_0^1 u^n \, w_\pi(u)\,du, \qquad w_\pi(u) := \frac{u^{1/8} P_\pi(u^{1/8})}{8(16 - u)} > 0 \quad (u \in (0, 1)).
```

**Theorem 7.1 (Prime-centered BBP Hankel determinant for $\pi$; Parts (1)–(2): Paper proof & Finite certificate; Part (3): Heuristic / $M = 0$ benchmark).**
1. *(B1 transfers across all four odd residue classes mod $8$)* For every odd prime $p$, the first and second indices $k_0(p) < k_1(p)$ at which $p$ divides $(8k+1)(2k+1)(8k+5)(4k+3)$, the pole residue $u_p \in \mathbb{Z}_{(p)}^\times$, and the maximum isolated dimension $r_{\max}(p) = \min(k_0(p) + 1,\, k_1(p) - k_0(p))$ are:

   | Class of $p \bmod 8$ | $k_0(p)$ | $k_1(p)$ | Pole residue $u_p$ | $r_{\max}(p)$ |
   | --- | --- | --- | --- | --- |
   | $p \equiv 1 \pmod 8$ | $(p - 1)/8$ | $(p - 1)/2$ | $+4$ | $(p + 7)/8$ |
   | $p \equiv 5 \pmod 8$ | $(p - 5)/8$ | $(p - 1)/2$ | $-1$ | $(p + 3)/8$ |
   | $p \equiv 3 \pmod 8$ | $(p - 3)/4$ | $(3p - 1)/8$ | $-1/2$ | $(p + 5)/8$ |
   | $p \equiv 7 \pmod 8$ | $(p - 3)/4$ | $(3p - 5)/8$ | $-1/2$ | $(p + 1)/8$ |

   For every $1 \le r \le r_{\max}(p)$, $M = k_0(p) - r + 1 \ge 0$, and arbitrary $m_{i,j} \in \mathbb{Z}_{(p)}$, $H^{(\pi)}_{i,j} = y_{M+i+j} - m_{i,j}$ satisfies $p H^{(\pi)}_{i,j} \equiv \mathbf{1}_{i+j \ge r-1} u_p \cdot 16^{i+j-(r-1)} \pmod{p \mathbb{Z}_{(p)}}$, hence **$v_p(\det H^{(\pi)}) = -r$** and **$\det H^{(\pi)} \ne 0$**.
2. *(B2, B3, and B4 positivity transfer)* Row reduction $\mathrm{row}_i \leftarrow \mathrm{row}_i - 16\mathrm{row}_{i-1}$ clears prior primes into row $0$; every odd prime $q$ not entering $r_k$ on $(M, M + 2r - 2]$ has $H^{(\pi)} = y_M v_{16} v_{16}^T + A_0$ ($A_0 \in M_r(\mathbb{Z}_{(q)})$), so $v_q(\det H^{(\pi)}) \ge -e_q(y_M)$ (rank $\le 1$ when $e_q \le 1$). For any prime $q \ge 7$ (or any odd prime $q$ with nonzero residue $\beta := (q r_{M+t}) \bmod q \not\equiv 0 \pmod q$) having $v_q(y_M) \ge -1$ and a single simple insertion at $k = M + t \in (M, M + 2r - 2]$ ($q^2 \nmid (8k+1)(2k+1)(8k+5)(4k+3)$), the exact rank law $s(t) = \min(t, 2r - 1 - t) + \mathbf{1}_{\rho_{\mathrm{maj}} \ne 0}$ of Theorem 3.2(2) transfers verbatim (excluding $q \in \{3, 5\}$ without $\beta \ne 0$, where two progressions can share an index $k$ and cancel modulo $q$, e.g. $q = 3, k = 7$ and $q = 5, k = 23$ both yield $\beta = 0$). On a base-$16$ clean window ($m_{M+k} = 16^k m_M$, valid when $\|16^n \pi\| < \frac{1}{32}$), $H^{(\pi)}_c = \varepsilon_\pi v_{16} v_{16}^T - K^{(\pi)}$ with **strictly positive-definite** $K^{(\pi)}_{i,j} = \int_0^1 u^{M+i+j} w_\pi(u)\,du$.
3. *(Heuristic obstructions & $M = 0$ linear-balance benchmark; **Heuristic / $M = 0$ benchmark comparison**, not a paper proof of prime-centered $M > 0$ failure)*
   - *Heuristic quadratic $O(r^2)$ comparison:* Unlike $\ln 2$ (single progression $n$), $r_k$ injects primes from **four** distinct linear progressions ($8k+1, 2k+1, 8k+5, 4k+3$), which heuristically suggests that the block-rank denominator cost $\log D_{\mathrm{B3}}^{(\pi)}$ exceeds the single-measure moment decay $-\log \det K^{(\pi)} \sim 2\ln 2 \cdot r^2$ at quadratic scale (no formal proof is given here).
   - *Symmetric $M = 0$ Legendre linear-balance benchmark (exact for $M = 0$ benchmark; Heuristic as a prime-centered obstruction):* for the symmetric $M = 0$ Legendre integral benchmark, PNT in arithmetic progressions mod $8$ gives $\log \operatorname{den}(y_{r-1}) \sim (\frac{1}{2}\cdot 8 + \frac{1}{2}\cdot 4) r = 6 r$ (matching `SY-21`'s exact rate $3/2$ per binary shift), while $\max_{u \in [0, 1]} \frac{u(1-u)}{16 - u} = (4 - \sqrt{15})^2$ gives analytic decay rate only $2 \log(4 + \sqrt{15}) \approx 4.12687$, leaving net $M = 0$ benchmark balance $6 - 4.12687 = +1.87313\, r > 0$. This is an $M = 0$ symmetric-integral heuristic and does not itself constitute a paper proof of failure for the prime-centered ($M > 0$) construction.

*Proof.* (1) Checking the least $k \ge 0$ solving $8k+1 \equiv 0$, $2k+1 \equiv 0$, $8k+5 \equiv 0$, or $4k+3 \equiv 0 \pmod p$ for each odd class mod $8$ yields the exact table of $k_0(p) < k_1(p)$ and $u_p \in \{4, -1, -1/2\} \subset \mathbb{Z}_{(p)}^\times$. Since $0 \le M \le k_0 \le M + 2r - 2 < k_1$, $k = k_0$ is the unique entry of $p$ in $[0, M+2r-2]$, so $p H^{(\pi)} \bmod p$ is lower-right anti-triangular with anti-diagonal $u_p$, giving $\det(p H^{(\pi)}) \equiv (-1)^{r(r-1)/2} u_p^r \not\equiv 0 \pmod p$. (2) From $y_{M+i+j} = 16^{i+j} y_M + \sum_{t=1}^{i+j} 16^{i+j-t} r_{M+t}$, the non-entering bound and positive definiteness follow verbatim from Theorem 3.1(3) and $w_\pi(u) > 0$ on $(0, 1)$. For the pairwise linear combinations of $\{8k+1, 2k+1, 8k+5, 4k+3\}$ eliminating $k$, the only odd-prime resultants are $(8k+1) - 4(2k+1) = -3$ and $(8k+1) - 2(4k+3) = -5$, so for every prime $q \ge 7$ at most one progression is divisible by $q$ at any $k$, forcing $\beta = (q r_{M+t}) \bmod q \in \mathbb{F}_q^\times$; since $16$ is a $q$-unit, the proof of Theorem 3.2(2) transfers verbatim (certified on `124` windows in `scripts/phase26_hankel_ln2.py`, alongside the $\beta = 0$ cancellations at $q = 3, k = 7$ and $q = 5, k = 23$). (3) The $M = 0$ linear balance follows from PNT in progressions mod $8$ and elementary calculus on $\frac{u(1-u)}{16-u}$; both the quadratic remark and the transfer from $M = 0$ to prime-centered $M > 0$ windows are heuristics. $\square$

### 7.2 $e$ (factorial prefixes $e_K$, `GF-47` Theorem 4.3 and `CC-09`)

Let $e_K = \sum_{k=0}^K \frac{1}{k!} = E_K / K!$ and $R_K = e - e_K = \frac{1}{K!} \int_0^1 t^K e^{1-t}\,dt$.

**Theorem 7.2 (Factorial-prefix Hankel determinant for $e$; Paper proof; Finite certificate).**
1. *(B1 transfers across ALL bands $1 \le m < p$, with zero drop events on the anti-diagonal!)* For every prime $p$, every band $1 \le m < p$, every $1 \le r \le p$ with $M = m p - r + 1 \ge 0$, and arbitrary $m_{i,j} \in \mathbb{Z}_{(p)}$, the matrix $H^{(e)}_{i,j} = e_{M+i+j} - m_{i,j}$ satisfies $p^m H^{(e)} \in M_r(\mathbb{Z}_{(p)})$, $p^m H^{(e)}_{i,j} \equiv 0 \pmod p$ for $i + j < r - 1$, and $p^m H^{(e)}_{i, r-1-i} \equiv \frac{(-1)^m}{m!} \not\equiv 0 \pmod p$ on the anti-diagonal. Hence
   ```math
   v_p(\det H^{(e)}) = -m r \qquad \text{and} \qquad \det H^{(e)} \ne 0.
   ```
2. *(What fails: four structural obstructions)*
   - *Small primes do not clear under B2:* after $\mathrm{row}_i \leftarrow \mathrm{row}_i - \mathrm{row}_{i-1}$, rows $i \ge 1$ become $\frac{1}{(M+i+j)!} - \Delta_1 m_{M+i+j}$, which still carry $q^{-v_q(M!)}$ in **every** entry for every prime $q \le M$.
   - *B3 rank collapse fails for $t < r$:* for a prime $q \in (M, M + r)$ ($t = q - M < r$), `GF-47` Theorem 4.3 gives $q H^{(e)}_{i,j} \equiv -e_{i+j-t} \pmod q$ for $i + j \ge t$, which varies nonlinearly along the window rather than as a rank-1 geometric progression; rank need not drop to $t + 1$ (exact counterexample: $q = 7, M = 5, r = 5, t = 2$ has $\operatorname{rank}_{\mathbb{F}_7}(7 H^{(e)} \bmod 7) = 5 > t + 1 = 3$). (For $t \ge r$, the bottom-right $(2r-1-t)\times(2r-1-t)$ block still has exact rank $2r - 1 - t$.)
   - *B4 positivity fails:* the tail matrix $K^{(e)}_{i,j} = R_{M+i+j}$ is **not** positive definite, because $R_K$ decays super-exponentially and is log-concave ($R_1 R_3 - R_2^2 < 0$, already failing at $M = 1, r = 2$).
   - *Binary-shifted `GF-47` Corollary 4.4 states $z_n = 2^n e_{K(n)}$ degenerate under geometric shifts:* $K(n) \sim n \ln 2 / \ln n$ is piecewise constant on stretches of length $\asymp \log n$. For **geometric (clean) shifts** $m_{n+1} = 2 m_n$ (so $z_{M+i+j} - 2^{i+j} m_M = 2^{i+j}(2^M e_{K(M+i+j)} - m_M)$), any Hankel window of size $r \ge 2$ contained in a constant stretch of $K(n)$ has rank $\le 1$ and $\det = 0$ (more generally, whenever $K$ is identical across two adjacent rows $i_0$ and $i_0 + 1$, row $i_0 + 1$ equals $2 \cdot \mathrm{row}_{i_0}$, forcing $\det = 0$). With arbitrary non-geometric integer shifts $m_n$, the determinant need not vanish.

*Proof.* (1) For $i + j < r - 1$, $K = M + i + j < m p$, so $v_p(K!) \le m - 1$ (as $m < p$) and $p^m e_K \equiv 0 \pmod{p \mathbb{Z}_{(p)}}$. For $i + j \ge r - 1$, $m p \le K < (m + 1) p$, so `GF-47` Theorem 4.3 gives $p^m e_K \equiv \frac{(-1)^m}{m!} e_{K - mp} \pmod{p \mathbb{Z}_{(p)}}$ (note that the Wilson proof of `GF-47` Theorem 4.3 applies verbatim for $m < p$ even without $p > \sqrt{K}$, since $K < (m+1)p \le p^2$!). On $i + j = r - 1$, $K = m p$ and $e_0 = 1$, so the anti-diagonal is the nonzero unit $\frac{(-1)^m}{m!} \bmod p$, giving $v_p(\det H^{(e)}) = -m r$. (2) Checked directly above and certified in `scripts/phase26_hankel_ln2.py`. $\square$

### 7.3 $\zeta(3)$ (Broadhurst's dyadic base-$2^{12}$ BBP formula, 1998)

Broadhurst (1998, `math/9803067`) established the base-$4096$ ($2^{12}$) BBP-type series

```math
672\,\zeta(3) = \sum_{k=0}^{\infty} \frac{c_k}{4096^k}, \qquad c_k = \sum_{j=1}^{23} \frac{a_j}{(24k + j)^3},
```

with integer coefficients $(a_1, \dots, a_{23}) = (2048, -11264, -1024, 11776, -512, 4096, 256, 3456, 128, -704, -64, -128, -32, -176, 16, 216, 8, 64, -4, 46, -2, -11, 1)$ (every reduced residue $j \in (\mathbb{Z}/24\mathbb{Z})^\times$ has $a_j = \pm 2^{e_j}$, coprime to all odd primes). Define $z_n = \sum_{k=0}^n 4096^{n-k} c_k$ ($z_{n+1} = 4096 z_n + c_{n+1}$) and $672 \cdot 4096^n \zeta(3) = z_n + T_n^{(\zeta(3))}$, where

```math
T_n^{(\zeta(3))} = \frac{1}{2} \int_0^1 \frac{t^{24n + 24} (\ln t)^2 Q_{\zeta(3)}(t)}{4096 - t^{24}}\,dt, \qquad Q_{\zeta(3)}(t) := \sum_{j=1}^{23} a_j t^{j - 1}.
```

**Theorem 7.3 (Cubic-pole prime-centered Hankel determinant for $\zeta(3)$; Parts (1)–(2) & (3a): Paper proof & Finite certificate; Part (3b): Heuristic / $M = 0$ benchmark).**
1. *(B1 transfers with **cubic amplification** $v_p = -3r$)* Let $p \ge 13$ be prime, set $k_0(p) = \lfloor p / 24 \rfloor$, $k_1(p) = \lfloor p / 12 \rfloor$, and $r_{\max}(p) = k_1(p) - k_0(p) = \lfloor (p + 12)/24 \rfloor \ge 1$. For every $1 \le r \le r_{\max}(p)$, $M = k_0(p) - r + 1 \ge 0$, and arbitrary $m_{i,j} \in \mathbb{Z}_{(p)}$, the matrix $H^{(\zeta(3))}_{i,j} = z_{M+i+j} - m_{i,j}$ satisfies $p^3 H^{(\zeta(3))}_{i,j} \equiv \mathbf{1}_{i+j \ge r-1} a_{p \bmod 24} \cdot 4096^{i+j-(r-1)} \pmod{p \mathbb{Z}_{(p)}}$, hence
   ```math
   v_p(\det H^{(\zeta(3))}) = -3r \qquad \text{and} \qquad \det H^{(\zeta(3))} \ne 0.
   ```
2. *(B3 cubic-pole non-entering rank bound transfers)* For every prime $q > 3$ dividing no $24k + j$ ($1 \le j \le 23$) for $k \in (M, M + 2r - 2]$, $H^{(\zeta(3))} = z_M v_{4096} v_{4096}^T + A_0$ ($A_0 \in M_r(\mathbb{Z}_{(q)})$), so Theorem 3.1(3) yields $v_q(\det H^{(\zeta(3))}) \ge -e_q(z_M)$ (at most $-3$ for simple cubic primes, vs naive $-3r$).
3. *(Positivity failure and $M = 0$ linear-balance benchmark)*
   - *(3a) B4 positivity failure (Paper proof; Finite certificate):* $Q_{\zeta(3)}(0) = 2048 > 0$, $Q_{\zeta(3)}(\frac{1}{2}) = -\frac{9{,}403{,}717{,}869}{4{,}194{,}304} \approx -2242.02 < 0$, and $Q_{\zeta(3)}(1) = 8190 > 0$. Because the integral weight $w_{\zeta(3)}(u) \propto (\ln u)^2 Q_{\zeta(3)}(u^{1/24}) / (4096 - u)$ is strictly negative on a nonempty open interval inside $(0, 1)$ (numerically $t \in (0.186, 0.789)$, i.e. $u = t^{24} \in (3 \times 10^{-18}, 3.4 \times 10^{-3})$), for each **fixed** $M \ge 0$ Weierstrass approximation produces a real polynomial $P(u)$ with $\int_0^1 P(u)^2 u^M w_{\zeta(3)}(u)\,du < 0$, so $K^{(\zeta(3))}(M, r)$ is **indefinite for all $r \ge r_0(M)$** (note the quantifier dependence on $M$: $u^M$ suppresses the small-$u$ negative region, so this rules out any $M$-uniform positive-definite Loewner comparison, while along a coupled prime-centered ray $(M(p), r(p))$ indefiniteness at a given $p$ depends on whether $r \ge r_0(M)$).
   - *(3b) Symmetric $M = 0$ linear-balance benchmark (**Heuristic / $M = 0$ benchmark comparison**, not a paper proof of prime-centered $M > 0$ failure):* for the symmetric $M = 0$ Legendre benchmark, cubic poles give row-$0$ denominator growth $3\psi(24 r) \sim 72 r$ (with heuristic multi-progression $O(r^2)$ excess), whereas the base-$4096$ symmetric Legendre integral decays at rate only $2\log(64 + \sqrt{4095}) \approx 9.7040$, leaving a $+62.30\, r$ linear deficit on the $M = 0$ benchmark.

*Proof.* (1) Since $p \ge 13$, $p$ is coprime to $24$, so $j_0 = p \bmod 24 \in (\mathbb{Z}/24\mathbb{Z})^\times$ has $a_{j_0} = \pm 2^{e_{j_0}} \not\equiv 0 \pmod p$, and $k_0 = \lfloor p/24 \rfloor < \lfloor 2p/24 \rfloor = k_1$ (by Hermite's identity, $k_1 - k_0 = \lfloor (p+12)/24 \rfloor \le k_0 + 1$, so $M = k_0 - r + 1 \ge 0$). On $[0, k_1 - 1]$, $24k + j < 2p$, so $k = k_0$, $j = j_0$ is the unique multiple of $p$, entering as $a_{j_0}/p^3$. Thus $p^3 H^{(\zeta(3))} \bmod p$ is lower-right anti-triangular with unit anti-diagonal $a_{j_0} \bmod p$, giving $v_p(\det H^{(\zeta(3))}) = -3r$. (2) Immediate from Theorem 3.1(3). (3a) Exact rational evaluation of $Q_{\zeta(3)}(1/2)$ and Weierstrass density of polynomials in $C([0, 1])$ for each fixed $M \ge 0$. (3b) Direct PNT and calculus comparison for the $M = 0$ symmetric benchmark; its transfer to prime-centered $M > 0$ windows is heuristic. $\square$

---

## 8. External inputs and hypothesis verification

| Input | Statement used | Where used / Hypotheses checked |
| --- | --- | --- |
| Prime Number Theorem (Hadamard / de la Vallée Poussin 1896) | $\psi(x) = \log L_{\lfloor x \rfloor} = (1 + o(1)) x$; prime gaps $p_{k+1} - p_k = o(p_k)$; PNT in progressions mod $8$ | Cor. 2.3, Thm 3.4(4), Thm 4.5, Thm 5.1(2), Thm 7.1(3) ($M = 0$ benchmark), Thm 7.3(3b) ($M = 0$ benchmark). **Not** used in exact algebraic Theorems 1.1, 2.1, 3.1–3.4(1–3), 4.1–4.3, 5.1(1), 7.1(1–2), 7.2, 7.3(1–2, 3a). |
| Stirling's formula / Barnes $G$-asymptotic | $\log(n!) = n\log n - n + O(\log n)$ | Cor. 2.3, Thm 3.4(4), Prop. 4.2(2), Lemma 4.4. |
| Smith Normal Form over PIDs (classical) | Every matrix over the PID $\mathbb{Z}_{(q)}$ has diagonal SNF $U D V$ | Thm 3.1(2)–(3). (Thm 3.1(1) also has an elementary SNF-free proof.) |
| Shifted Jacobi 3-term diagonal coefficient (Szegő, *Orthogonal Polynomials*) | $\int_{-1}^1 u P_k^{(0,M)}(u)^2 (1+u)^M\,du / \int_{-1}^1 P_k^{(0,M)}(u)^2 (1+u)^M\,du = \frac{M^2}{(2k+M)(2k+M+2)}$ | Prop. 4.2(4) (also verified directly by exact rational integration on $84$ pairs $(M, k)$). |
| Broadhurst (1998, `math/9803067`) | Base-$2^{12}$ BBP identity for $672\zeta(3)$ | Thm 7.3 (certified $> 52$-digit rational enclosure cross-check against Markov/Apéry's alternating series $\zeta(3) = \frac{5}{2}\sum_{n\ge 1} \frac{(-1)^{n-1}}{n^3\binom{2n}{n}}$ in `scripts/phase26_hankel_ln2.py` confirms all $23$ coefficients). |
| `GF-47` (Phase 25 Track G) | Lemma 3.3 (all-$p$-adic band law), Thm 3.6 (geometric-reset countermodel), Thm 4.3 (band law for $e$) | Thm 3.2(3), Thm 5.1, Thm 7.2(1). |
| Context / literature comparison only (never used inside a proof) | Markov (1890), Danilov (1978), Apéry (1979), Beukers (1979), G. V. Chudnovsky (1979), Alladi–Robinson (1980), Rhin (1987), Rukhadze (1987), Hata (1990), Rhin–Viola (1996, 2001), Rivoal (2007), Marcovecchio (2009), Rosser–Schoenfeld (1962), `CC-03`, `CC-05`, `CC-08`, `CC-09`, `GF-28` | §4.5, §5, §7, §11. |

---

## 9. Prior art and attribution

- Shifted Legendre/Jacobi integrals for $\ln 2$ and irrationality measures trace to Danilov (1978), Beukers (1979), G. V. Chudnovsky (1979), Alladi–Robinson (1980), Rhin (1987), Rukhadze (1987), Hata (1990), Rhin–Viola (1996, 2001), Rivoal (2007, restricted-denominator Padé measures), and Marcovecchio (2009).
- The Hankel-determinant modification identity for rational weight division $(z - t)^{-1} d\mu(t)$ is a classical instance of Christoffel–Uvarov orthogonal-polynomial theory (Christoffel 1858; Uvarov 1969).
- The BBP series for $\pi$ is Bailey–Borwein–Plouffe (1997, kernel-verified in `CC-08`), the binary $\zeta(3)$ series is Broadhurst (1998), the accelerated alternating series for $\zeta(3)$ is Markov (1890) / Apéry (1979), and the all-$p$-adic band laws and $O(\log N)$-reset countermodels are repository Phase 25 `GF-47`.
- Subject to the repository's provisional-novelty rule (a literature search that finds nothing does not establish priority), the prime-centered BBP Hankel pole theorem (Thm 1.1), the exact single-insertion rank law $s(t) = \min(t, 2r-1-t) + \mathbf{1}_{\rho_{\mathrm{maj}}\ne 0}$ linked to `GF-47` drop events (Thm 3.2), the exact Cauchy–Block-Rank integer cancellation $D_{\mathrm{B3}}(p, r)\det C(M, r) \le \frac{L_p}{r\binom{p+r}{r}}$ (Thms 3.3–3.4), the exact collapse of the clean-window $r \times r$ BBP Hankel determinant to $I_{M, r-1} - \varepsilon P_{r-1}^{(0,M)}(3)$ (Thm 4.3), the `GF-47` reset-ratio limitation distinguishing activation ($\rho_*^{\mathrm{Hankel}} = 2.5897$) from exclusion ($\rho_{\mathrm{excl}}^{\mathrm{Hankel}} = \mu_2^{\mathrm{Hankel}} = 6.1788$, i.e. $1.44$ vs $5.18$ bits/index) (Thm 5.1), and the systematic $\pi$/$e$/$\zeta(3)$ Hankel classification (Thms 7.1–7.3) are new in this repository.

---

## 10. Standing objectives advanced

| Result | Objective (`docs/research-objectives.md`) |
| --- | --- |
| Theorems 1.1, 2.1, 3.1–3.4 | **Objective 3 / 4** (exact $p$-adic pole amplification, sharp rank-sensitive local denominator laws, exact algebraic cancellation of quadratic Hankel denominators). |
| Theorems 4.3, 4.5 | **Objective 3** (self-contained dyadic lower bound $|2^M\ln 2 - m| \ge 2^{-(5.1788 + o(1))M}$ and $\ge 0.3806\log_2 N$ binary transitions for $\ln 2$, nearly doubling `CC-05`'s Lean coefficient, though weaker than classical $\mu(\ln 2)$ records). |
| Theorem 4.3 + Theorem 5.1 + §6 Ledger | **Objective 4** (rigorous limitation theorems: proves why $r \times r$ prime-centered BBP Hankel determinants collapse identically to 1-D asymmetric Jacobi Padé forms with zero extra amplification, survive verbatim inside `GF-47` $\rho = 1.5$ reset countermodels with $D^+ = 1$, cannot exclude any clean reset-free block below $\rho_{\mathrm{excl}} \approx 6.18$ — $5.18$ vs $1.44$ bits/index — and fail to overcome the asymmetric $L_{M+r-1}$ penalty or linear-run barrier). |
| Theorems 7.1–7.3 | **Objective 3 / 4** (exact prime-centered Hankel valuations for $\pi$, $e$, $\zeta(3)$ together with proved positivity/rank obstructions and heuristic $M = 0$ denominator-balance benchmarks). |

---

## 11. Reproduction and exact finite verification

```sh
python -B scripts/phase26_hankel_ln2.py
```

Standard library only; exits `0` in ~1.1 s on Windows with **67,877 total assertions** (**67,593 exact `int`/`Fraction`** + **284 exact rational enclosure**):

- **B1 (`[exact]`):** `284` exact matrix determinants across all primes $p \le 23$ (including $p = 2$) and $1 \le r \le p$, testing zero, clean-doubling, cubic, and non-Hankel $p$-integral perturbations; verifies entrywise mod-$p$ anti-triangular law, $\det(p H) \equiv (-1)^{r(r-1)/2} \pmod p$, $v_p(\det H) = -r$, and $\det H \ne 0$.
- **B2 (`[exact]`):** `924` pairs $(a, r)$ verifying Lemma 2.2's two-sided interval-LCM divisibility; `51` matrices verifying $H^{(1)} = L H$, $H^{(2)} = L H L^T$, cofactor splits, and $\operatorname{den}(\det H) \mid D_{\mathrm{double}} \mid D_{\mathrm{row}}$ (`17` with strict saving $D_{\mathrm{double}} < D_{\mathrm{row}}$).
- **B3 (`[exact]`):** `877` single-insertion windows (`133` drop-event windows including `GF-47`'s $q = 17, m = 11$) and `839` no-multiple windows verifying exact $\mathbb{F}_q$-rank $s(t)$ and $v_q(\det H) \ge -s$; $p = 5$ centered at drop $2p = 10$ ($r = 2 \dots 5$, rank $= r - 1 < r$); higher-power non-entering check; `6,272` triples $(M, r, d)$ verifying the exact Cauchy–Block-Rank and $\delta(M, r, d)$ identities; `100` pairs $(p, r)$ ($p \le 23$, all $1 \le r \le p$) verifying the exact integer product identity, $D_{\mathrm{B3}} \mid D_{\mathrm{row}}$, and $\operatorname{den}(\det H) \mid D_{\mathrm{B3}}$ (`52` with strict improvement $D_{\mathrm{B3}} < D_{\mathrm{row}}$).
- **B4 (`[exact]` + `[encl]`):** `84` pairs $(M, k)$ verifying shifted Jacobi orthogonality, two explicit formulas, $P_k^{(0,M)}(3)$, and exact $\mathbb{E}[t]$; `70` pairs $(M, r)$ verifying exact $\det C$ and $v^T C^{-1} v = \sum (2k+M+1) P_k^{(0,M)}(3)^2$; `153` exact $\mathbb{Q}[X]$ Uvarov–Christoffel clean-window cases and $v_p(\Lambda_{M,r}) = -1$; `36 + 61` certified rational enclosures verifying Loewner inequalities, Hadamard–Jacobi linear bound, and $\frac{1}{n+2} < T_n < \frac{1}{n+1}$.
- **B5 (`[exact]` + `[encl]`):** reconstructs `GF-47` Theorem 3.6 blocks $[240, 360)$ (`22` primes) and $[360, 540)$ (`31` primes); verifies B1, B2, B3, and B4 Uvarov–Christoffel hold verbatim on `18` interior prime-centered windows; certifies via rational enclosure $|\tilde{\varepsilon}| \in (2^{-166}, 2^{-165})$ at $M = 240$ and $|\tilde{\varepsilon}| \in (2^{-251}, 2^{-250})$ at $M = 360$ (versus Hankel exclusion thresholds $\approx 2^{-1243}$ and $\approx 2^{-1864}$); verifies reset-crossing window $(p, r) = (359, 3)$ breaks B2/B3 (`30` primes dividing $M_1$ acquire pole order $\ge 2$).
- **B7 (`[exact]` + `[encl]`):** `30` $\pi$ BBP matrices across all four odd classes mod $8$, `124` single-insertion rank windows ($q \in \{7, \dots, 19\}$) plus $\beta = 0$ pole-cancellation certificates at $q = 3, k = 7$ and $q = 5, k = 23$, and exact positivity factorization of $P_\pi$; `53` $e$ factorial matrices ($v_p = -mr$, $m = 1 \dots 3$), explicit B3 non-collapse counterexample ($q = 7, M = 5, r = 5, t = 2$: rank $= 5 > 3$), and certified $R_1 R_3 - R_2^2 < 0$; `15` Broadhurst $\zeta(3)$ matrices ($v_p = -3r$), exact sign-change certificate $Q_{\zeta(3)}(1/2) = -9403717869/4194304 < 0$, and certified $> 52$-digit Broadhurst-vs-Apéry rational enclosure cross-check confirming all $23$ coefficients.
- **Isolated `[finite]` / `[float]` section:** numerical comparison tables at $p = 503$, $r = \operatorname{round}(\sqrt{p/\log p})$ ($p \le 2003$, annotated with the slow $o(1)$ correction), and $p = 1999$ B2 excess across $\alpha \in [0.02, 1]$, plus activation/exclusion thresholds and heuristic $M = 0$ benchmark evaluations.

---

## 12. Open questions

1. **Multi-prime / multi-shift Hankel matrices beyond single-block linear runs.** Single prime-centered clean windows collapse to 1-D asymmetric Jacobi Padé forms (Thm 4.3). Can a *block-coupled* matrix across **disjoint** clean runs (or non-consecutive BBP indices targeting periodic runs $m / (2^M(2^d - 1))$) escape both the asymmetric $L_p$ penalty and the single-run Kempner barrier?
2. **Prime-factor arithmetic refinement inside $H_c$.** Rukhadze (1987), Hata (1990), and Marcovecchio (2009) improve symmetric Legendre integrals by finding extra prime factors dividing the integral coefficients (lowering $\mu(\ln 2)$ from $4.6221$ to $3.5746$). Does a weighted polynomial variant of $H_c$ (replacing $t^M/(2-t)$ with a weighted shifted kernel) retain a one-shot prime-centered nonvanishing certificate while beating Alladi–Robinson's $4.6221$ for dyadic denominators?
3. **Full-denominator resets in `GF-47`.** Theorem 5.1 shows that B1+B3+B4 is vacuous below activation ratio $\rho_*^{\mathrm{Hankel}} = 2.5897$ and requires block ratio $\rho > \rho_{\mathrm{excl}}^{\mathrm{Hankel}} = \mu_2^{\mathrm{Hankel}} \approx 6.1788$ ($5.18$ bits/index) to contradict a clean reset-free block — far above the full-denominator information ceiling $\rho_{\mathrm{info}} = 1 + 1/\ln 2 \approx 2.4427$ ($1.44$ bits/index; even Marcovecchio's classical $\mu(\ln 2) \le 3.5746$ requires $\rho > 3.5746$, i.e. $2.57$ bits/index). Does any non-Hankel or multi-block arithmetic test rule out `GF-47`-style resets at ratios $\rho \in (1.5, 2.4427)$?
4. **Track H Lean 4 formalization.** Formalize Theorem 1.1 (`bbpHankel_det_padicVal`), Theorem 2.1 (`bbpHankel_den_dvd_rowClearing`), Theorem 3.4's exact Cauchy–Block-Rank integer identity, and Theorem 4.3's algebraic Uvarov–Christoffel identity in `NormalityChecker/`.

---

## References

- K. Alladi and M. L. Robinson, Legendre polynomials and irrationality, *J. Reine Angew. Math.* **318** (1980), 137–155.
- R. Apéry, Irrationalité de $\zeta(2)$ et $\zeta(3)$, *Astérisque* **61** (1979), 11–13.
- D. H. Bailey, P. B. Borwein and S. Plouffe, On the rapid computation of various polylogarithmic constants, *Math. Comp.* **66** (1997), 903–913.
- F. Beukers, A note on the irrationality of $\zeta(2)$ and $\zeta(3)$, *Bull. London Math. Soc.* **11** (1979), 268–272.
- D. J. Broadhurst, Polylogarithmic ladders, hypergeometric series and the ten millionth digits of $\zeta(3)$ and $\zeta(5)$, arXiv:math/9803067 (1998).
- E. B. Christoffel, Über die Gaußische Quadratur und eine Verallgemeinerung derselben, *J. Reine Angew. Math.* **55** (1858), 61–82.
- G. V. Chudnovsky, Formules d'Hermite pour les approximants de Padé de logarithmes et de fonctions binômes, et mesures d'irrationalité, *C. R. Acad. Sci. Paris* **288** (1979), 965–967.
- L. V. Danilov, Rational approximations of some functions at rational points, *Mat. Zametki* **24** (1978), 449–458.
- M. Hata, Legendre type polynomials and irrationality measures, *J. Reine Angew. Math.* **407** (1990), 99–125.
- A. Markov, Mémoire sur la transformation des séries peu convergentes en séries très convergentes, *Mém. Acad. Imp. Sci. St.-Pétersbourg* **37** (1890), no. 9.
- R. Marcovecchio, The Rhin–Viola method for $\log 2$, *Acta Arith.* **139** (2009), 147–184.
- G. Rhin, Approximants de Padé et mesures effectives d'irrationalité, *Séminaire de Théorie des Nombres, Paris 1985–86*, Birkhäuser (1987), 155–164.
- G. Rhin and C. Viola, On a permutation group related to $\zeta(2)$, *Acta Arith.* **77** (1996), 23–56; The group structure for $\zeta(3)$, *Acta Arith.* **97** (2001), 269–293.
- T. Rivoal, Convergents and irrationality measures of logarithms, *Rev. Mat. Iberoam.* **23** (2007), 931–952.
- J. B. Rosser and L. Schoenfeld, Approximate formulas for some functions of prime numbers, *Illinois J. Math.* **6** (1962), 64–94.
- E. A. Rukhadze, A lower bound for the approximation of $\ln 2$ by rational numbers, *Vestnik Moskov. Univ. Ser. I Mat. Mekh.* (1987), no. 6, 25–29.
- G. Szegő, *Orthogonal Polynomials*, 4th ed., Amer. Math. Soc. Colloq. Publ. **23**, 1975.
- V. B. Uvarov, The connection between systems of polynomials that are orthogonal with respect to different distribution functions, *USSR Comput. Math. Math. Phys.* **9** (1969), 25–36.
- Repository: Phase 22 [`classical-targets-and-recon.md`](../phase22/classical-targets-and-recon.md) (`GF-28`); Phase 23 [`classical-correlations-and-log2.md`](../phase23/classical-correlations-and-log2.md) (`GF-35`); Phase 24 [`classical-constants-and-joint-numerators.md`](../phase24/classical-constants-and-joint-numerators.md) (`GF-40`); Phase 25 [`classical-constants-frontier.md`](../phase25/classical-constants-frontier.md) (`GF-47`); `CC-03`, `CC-05`, `CC-08`, `CC-09`, `CC-11`.
