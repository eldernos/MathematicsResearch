# Independent Cross-Provider Referee Report — Phase 23, Track E

**Audited files (read-only):**
- `notes/phase23/classical-correlations-and-log2.md` (498 lines)
- `scripts/phase23_classical.py` (931 lines)

**Cross-checked references:**
- `docs/benchmarks/classical-constants.toml`
- `notes/phase22/classical-targets-and-recon.md`
- `NormalityChecker/Phase22Cores.lean`
- `NormalityChecker/SharpTranslation.lean`

**Execution check:** `python -B scripts/phase23_classical.py` exited `0` (`ALL CHECKS PASSED (4572608 checks) in 17.1 s`).

**Verdict:** **ACCEPT AFTER REVISION**

**Notice:** Cross-model review is not independent human peer review.

---

## Executive Summary

Track E is mathematically strong, honest in its evidence separation, and computationally well-engineered. Every core theorem—the Liouville mod-4 law (Prop. 1.1), the $7:3$ split mod 8 (Prop. 1.2), the $2^j$-divisibility density bound (Prop. 1.3), the 2-adic peeling theorem (Lemma 1.4, Thm. 1.5, Cor. 1.6), the exact 2-adic correlation factors $\rho(h)$ and conditional two-point asymptotics (Prop. 2.1, Thm. 2.2), the unconditional $\log^3 X$ second moment and exact $1/(9\pi^2)$ vs $1/(3\pi^2)$ leading constants for $T_n^+$ and $T_n$ (Thm. 3.1), the mod-4 mark correlation law (Prop. 4.1), the Weyl-sum characterization of $D^+(x;2) = 1$ with the exact $0.9997 \implies 0.9999$ threshold and degree-2 transition minorant (Props. 5.1–5.2), and the $\ln 2$ BBP band law and Glaisher–Wieferich numerator congruence (Thm. 5.3, Prop. 5.4)—is true and supported by a sound main argument. No benchmark status is prematurely promoted, and all 35 open benchmark constants in `docs/benchmarks/classical-constants.toml` are mapped bijectively.

No **Critical** errors were found. However, the audit identified **4 Major findings** (an overlapping-prime indexing bug in the main §5.3 display equation, an overstatement of single-prime equidistribution along band windows for primes where $2$ is not a primitive root, a missing uniform-in-$h$ upper bound needed to interchange $\lim_{X \to \infty}$ and $\sum_h$ at scale $\log^2 X$ in §3, and a factor-of-3 formula error for BC-24 in §6) together with **11 Minor findings** (statement/proof precision gaps, one downward rounding of a certified upper bound, and minor script documentation/dead-code issues). All findings have clean, local repairs.

---

## Findings by Severity

### Critical Findings

None.

---

### Major Findings

#### M1. Boundary-band double-counting bug in the §5.3 Weyl-sum product
- **Location:** `notes/phase23/classical-correlations-and-log2.md`, line 393 (and prose on line 396).
- **Issue:** Line 393 writes
  $$D^+(\ln 2; 2) < 1 \iff \limsup_N \left|\frac{1}{N} \sum_{n < N} e(R_n) \prod_{m < \sqrt{n}}\ \prod_{\substack{p \in (n/(m+1),\, n/m] \\ p \nmid A_m}} e\left(\frac{2^{n-m} A_m Q_m^{-1}}{p}\right)\right| < 1,$$
  where $R_n$ is defined on line 396 as "the CRT summand of $x_n$ supported on primes $\le \sqrt{n}$ and powers of 2."
  Whenever $n$ is not a perfect square, $m = \lfloor \sqrt{n} \rfloor$ satisfies $m < \sqrt{n}$ and is therefore included in the outer product. For this boundary band, the interval $(n/(m+1), n/m]$ extends *below* $\sqrt{n}$ and can contain primes $p \le \sqrt{n}$: for example,
  - $n = 10$: $\sqrt{10} \approx 3.162$, $m = 3 < \sqrt{10}$, interval $(2.5, 3.333]$ contains $p = 3 \le \sqrt{10}$ ($3^2 = 9 < 10$);
  - $n = 26$: $\sqrt{26} \approx 5.099$, $m = 5 < \sqrt{26}$, interval $(4.333, 5.2]$ contains $p = 5 \le \sqrt{26}$ ($5^2 = 25 < 26$).
  Such a prime $p \le \sqrt{n}$ is **double-counted** (it already appears in $R_n$ AND in the product) and violates the hypothesis $p^2 > n$ of Theorem 5.3 (indeed $v_p(Q_n)$ can be $\ge 2$, e.g. $5^2 \mid 25$ at $n = 26$). In addition, for $n = 2, 3$ the prime $p = 2$ enters $(n/2, n]$ unless oddness is specified (harmless for $\limsup_N$, but makes the summand wrong at $n = 2, 3$).
- **Repair:** Restrict the inner product to odd primes $p > \sqrt{n}$, e.g. write
  $$\prod_{1 \le m < \sqrt{n}}\ \prod_{\substack{p \in (\max(\sqrt{n},\, n/(m+1)),\, n/m] \\ p > 2,\ p \nmid A_m}} e\left(\frac{2^{n-m} A_m Q_m^{-1}}{p}\right)$$
  (or equivalently $\prod_{\substack{\sqrt{n} < p \le n \\ p \text{ odd},\ p \nmid A_{\lfloor n/p \rfloor}}} e\!\left(\frac{2^{n-m} A_m Q_m^{-1}}{p}\right)$ with $m = \lfloor n/p \rfloor$).

#### M2. Overstatement of single-prime equidistribution along band windows
- **Location:** `notes/phase23/classical-correlations-and-log2.md`, lines 374 and 396.
- **Issue:** Line 374 states:
  > "If 2 is a primitive root mod $p$, it takes every nonzero residue (script: 130 pairs with $m=1,2$). Each large-prime component of the BBP state is therefore exactly equidistributed along its band window."
  Line 396 repeats:
  > "The phases are explicit in the numerators $A_m$, $m < \sqrt{n}$, and each is individually equidistributed along its band window."
  This is false as stated for two reasons:
  1. For primes $p$ where $2$ is **not** a primitive root mod $p$ (which is over $62\%$ of primes even under GRH, and Artin's conjecture that infinitely many primes have $2$ as a primitive root is itself open), the $p$-component $2^{N-m} s_m \bmod p$ only traverses a coset of the subgroup $\langle 2 \rangle \subset \mathbb{F}_p^\times$ of size $t = \operatorname{ord}_p(2)$. For small-order primes (e.g. $p = 7$, $t = 3$, residues $\{1, 2, 4\}/7$; $p = 31$, $t = 5$, residues $\{1, 2, 4, 8, 16\}/31$; or any Mersenne prime $p = 2^q - 1$ where $t = q = \log_2(p+1)$), the component is **not** equidistributed in $\mathbb{F}_p^\times$ and its phase average along $[mp, (m+1)p)$ does not even vanish.
  2. Even when $2$ *is* a primitive root mod $p$ (and $p \nmid A_m$), the band window $[mp, (m+1)p)$ has length $p$, not $p-1$, so one nonzero residue occurs twice while the other $p-2$ occur once; that is equidistribution up to $O(1/p)$, not exact uniformity on $\mathbb{F}_p^\times$ (which holds on any subwindow of length $p - 1$).
- **Repair:** State accurately that on $[mp, (m+1)p)$ (when $p \nmid A_m$) the $p$-component is periodic with period $\operatorname{ord}_p(2)$ and visits every element of a coset of $\langle 2 \rangle \bmod p$ uniformly up to at most one extra step; in particular, whenever $2$ is a primitive root mod $p$, it covers $\mathbb{F}_p^\times$ uniformly up to $O(1/p)$ (and for almost all primes, $\operatorname{ord}_p(2)$ is large, giving single-prime Weyl-sum cancellation along the band window). Update line 396 accordingly.

#### M3. Missing uniform-in-$h$ upper bound for the $\log^2 X$ off-diagonal asymptotic in §3
- **Location:** `notes/phase23/classical-correlations-and-log2.md`, line 38 (summary table) and line 273 (§3 prose).
- **Issue:**
  1. Line 273 states: *"Under (H2) the off-diagonal is $(\kappa + o(1))\log^2 X$ with $\kappa = \frac{2}{3} \sum_h 2^{-h} c(h)$. The constant is $\kappa_\tau = 0.503389$ for $\tau$ (Ingham, unconditional) and $\kappa_+ = -0.066965$ for $a_+$"*. However, Ingham's 1927 theorem (and Hypothesis (H2)) only provides fixed-$h$ asymptotics. In the proof of Theorem 3.1 (line 271), the tail $h > H$ is bounded via Cauchy–Schwarz by $O(2^{-H} \log^3 X)$. Dividing by $\log^2 X$ leaves $O(2^{-H} \log X)$, which **diverges** as $X \to \infty$ for fixed $H$. Thus Ingham's theorem (resp. (H2)) alone does **not** justify interchanging $\lim_{X \to \infty}$ and $\sum_{h \ge 1}$ at scale $\log^2 X$.
  2. Similarly, line 38 in the summary table asserts *"the off-diagonal terms are $O(\log^2 X)$ and cannot cancel it"* as part of Theorem 3.1, whereas Theorem 3.1's proof (line 271) only proves that the off-diagonal is $o(\log^3 X)$.
- **Repair:** The $\log^2 X$ bound and limit interchange *are* true, provided one cites a **uniform-in-$h$** upper bound for $1 \le h \le X$, namely $\frac{1}{X} \sum_{n \le X} \tau(n)\tau(n+h) \ll \frac{h}{\varphi(h)} \log^2 X$ (e.g. Nair–Tenenbaum 1998 / Henriot 2012, already cited in §2.3, or an elementary sieve bound; the range $h > X$ is bounded via Cauchy–Schwarz by $O(2^{-X} \log^3 X) = o(1)$, and similarly for the shift index $k > X$). Either:
  - cite the uniform-in-$h$ bound explicitly on line 273 (and in Theorem 3.1 if keeping "$O(\log^2 X)$" on line 38), **or**
  - change line 38 from "$O(\log^2 X)$" to "$o(\log^3 X)$" and note explicitly on line 273 that upgrading the off-diagonal from $o(\log^3 X)$ to $(\kappa + o(1))\log^2 X$ additionally uses the uniform-in-$h$ upper bound $C_\tau(h; X) \ll \frac{h}{\varphi(h)} \log^2 X$ for $1 \le h \le X$.

#### M4. Wrong closed form for BC-24 ($L(1, \chi_{-3})$) in the §6 missing-estimate map
- **Location:** `notes/phase23/classical-correlations-and-log2.md`, line 428.
- **Issue:** Line 428 lists the Dirichlet $L$-values BC-24–BC-26 as *"$\pi/\sqrt{3}$, $\ln(1+\sqrt{2})/\sqrt{2}$, $\ln(2+\sqrt{3})/\sqrt{3}$"*. By Dirichlet's class number formula (and `docs/benchmarks/classical-constants.toml`, line 556),
  $$L(1, \chi_{-3}) = 1 - \frac{1}{2} + \frac{1}{4} - \frac{1}{5} + \cdots = \frac{\pi}{3\sqrt{3}} \approx 0.60460,$$
  not $\pi/\sqrt{3} \approx 1.81380$ (off by a factor of $3$).
- **Repair:** Replace `\pi/\sqrt3` with `\pi/(3\sqrt3)` on line 428.

---

### Minor Findings

#### m1. Missing hypothesis $p \le N$ in Theorem 5.3
- **Location:** `notes/phase23/classical-correlations-and-log2.md`, line 359 (and summary table line 44).
- **Issue:** Theorem 5.3 assumes only "$N \ge 2$ and $p$ odd prime with $p^2 > N$" and then writes *"put $m = \lfloor N/p \rfloor$, so $1 \le m < p$"*. If $p > N$, then $m = 0$, contradicting $1 \le m < p$. Both the Lean blueprint B8 (line 473: `(h1 : p ≤ N)`) and the script (`scripts/phase23_classical.py`, line 760: `if p > N: break`) include $p \le N$.
- **Repair:** Add $p \le N$ (i.e., $\sqrt{N} < p \le N$) to the statement of Theorem 5.3 on line 359 and line 44.

#### m2. Missing truncation in $e$ in the proofs of Propositions 1.2 and 1.3
- **Location:** `notes/phase23/classical-correlations-and-log2.md`, lines 79 and 102.
- **Issue:**
  - In Proposition 1.3 (line 102), *"Summing over $r \le X^{1/4}$ and $e$, and bounding $r > X^{1/4}$ trivially by $O(X^{3/4})$"* omits truncating $e$: if $2^e$ is large (e.g. $2^e \asymp X / r^2$), then $Y = X / (2^e r^2)$ is $O(1)$, so $\log Y$ is not $\asymp \log X$ and the uniform Hardy–Ramanujan denominator $\log Y$ is not bounded below by $c \log X$. Splitting at $2^e r^2 \le X^{1/2}$ (where $Y \ge X^{1/2}$ and $\log Y \ge \frac{1}{2} \log X$) versus $2^e r^2 > X^{1/2}$ (trivial bound $\sum_{2^e r^2 > X^{1/2}} X / (2^e r^2) \ll X^{3/4}$) makes the argument airtight.
  - Similarly, in Proposition 1.2 (line 79), for $s$ near $X^{1/4}$, $\log(X/s^2) \approx \frac{1}{2}\log X \neq (1+o(1))\log X$; the step is valid via dominated convergence (using $\pi(X/s^2)/(X/\log X) \ll s^{-2}$ on $s \le X^{1/4}$ and fixed-$s$ PNT, or splitting at $s \le \log X$), and the sum over even $e$ likewise requires truncating $2^e s^2 \le X^{1/2}$.
- **Repair:** State the joint truncation $2^e r^2 \le X^{1/2}$ (resp. $2^e s^2 \le X^{1/2}$ with dominated convergence for PNT) in lines 79 and 102.

#### m3. Scope and hypotheses of Corollary 1.6
- **Location:** `notes/phase23/classical-correlations-and-log2.md`, lines 131–136.
- **Issue:**
  1. Line 131 says *"The same statement holds, with the same proof, for every coefficient sequence $c$ such that $\{n : 2^j \nmid c(n)\}$ has density $0$ for each $j$."* Technically this requires $c(n) \in \mathbb{Z}$ with $\sum |c(n)| 2^{-n} < \infty$ so the series $x = \sum c(n) 2^{-n}$ and $B_j$ converge. Furthermore, for an *arbitrary* density-$0$ sequence, only the qualitative $K_2$-equivalence $y_j \in K_2$, $|D_N(x) - D_N(B_j)| \le 1 - D_N(y_j) + j/N \to 0$, and $D^\pm(x) = D^\pm(B_j)$ hold—not the quantitative rate $(\log\log N)^{j-1}/\log N$ of Theorem 1.5, nor the theta identity $y_1 = \sum 2^{-k^2}$ (for example, $\tau_{\rm odd}(n)$ is odd iff $n = k^2$ or $n = 2k^2$, so $y_1(\tau_{\rm odd}) = \sum 2^{-k^2} + \sum 2^{-2k^2}$).
  2. On line 135, for $\sigma(n)$, bounding $v_2(\sigma(n)) \ge \#\{p > 2 : p \parallel n\}$ works via splitting out the odd squarefull part (whose reciprocals have a convergent sum), whereas the slightly cleaner inequality $v_2(\sigma(n)) \ge \#\{p > 2 : v_p(n) \text{ odd}\} = \omega(s)$ (with $m = s r^2$, $s$ odd squarefree) uses the *exact* same decomposition and Hardy–Ramanujan count as Proposition 1.3 with zero extra steps.
- **Repair:** Add "$c(n) \in \mathbb{Z}$ with $\sum |c(n)| 2^{-n} < \infty$", clarify that the peeling equivalence $y_j \in K_2$ and $D^\pm(x) = D^\pm(B_j)$ (with the quantitative rate whenever $Z_j(X)$ obeys the same bound) transfers, and optionally tighten line 135 to $v_2(\sigma(n)) \ge \#\{p > 2 : v_p(n) \text{ odd}\}$.

#### m4. Endpoint/supremum nuances in Lemma 1.4 and Proposition 5.1(1)
- **Location:** `notes/phase23/classical-correlations-and-log2.md`, lines 114, 347, and 351.
- **Issue:**
  - In Lemma 1.4 (line 114), $\{2^n y\} \in [0, M 2^{-L}]$ is a closed interval, whereas $D_N$ is defined over half-open intervals $[a, c) \subseteq [0, 1]$. Taking $J = [0, M 2^{-L} + \varepsilon)$ (valid since $M 2^{-L} < 1$) and letting $\varepsilon \to 0^+$ yields the exact inequality cleanly even if $\{2^n y\} = M 2^{-L}$ occurs.
  - In Proposition 5.1(1) (lines 347, 351), $\varepsilon \in [0, 1]$ should be stated (the proof uses $\cos(\pi \varepsilon)$ decreasing on $[0, \pi]$), and since $D_N$ is a `sSup` over half-open intervals, a supremum-approaching interval with $|A_N(J)/N - |J|| \ge 1 - \varepsilon - \delta'$ ($\delta' \to 0^+$) avoids assuming the supremum is attained by a half-open interval.
- **Repair:** Add $\varepsilon \in [0, 1]$ in Prop. 5.1(1) and note the $\varepsilon \to 0^+$ / $\delta' \to 0^+$ limit in the proofs of Lemma 1.4 and Prop. 5.1(1).

#### m5. Spurious factor $(1 + h/X)$ and implicit $k$-truncation in Theorem 3.1 proof
- **Location:** `notes/phase23/classical-correlations-and-log2.md`, line 271.
- **Issue:** Line 271 writes $|C_+(h; X)| \le (1 + h/X) \frac{1}{X} \sum_{m \le X+h} \tau(m)^2 \ll (1 + h/X) \log^3(X+h)$. By Cauchy–Schwarz, the factor $(1 + h/X)$ is **not** present before $\frac{1}{X} \sum_{m \le X+h} \tau(m)^2$ (it *arises* from $\frac{1}{X} \cdot (X+h)\log^3(X+h)$); including it in the middle makes the middle expression $\asymp (1 + h/X)^2 \log^3(X+h)$, which contradicts the $\ll (1 + h/X)\log^3(X+h)$ on the right when $h > X$. Also, the shift $k$ in $2 \sum_{k \ge 1} 4^{-k} \sum_{h \ge 1} 2^{-h} \frac{1}{X} \sum_{n=1}^X a_+(n+k) a_+(n+k+h)$ should be truncated at $k \le H$ alongside $h \le H$ (for $k \le H, h \le H$ the boundary discrepancy is $O_H(X^{o(1)}/X) = o(1)$; for $k > H$ Cauchy–Schwarz gives $O(4^{-H} \log^3 X)$).
- **Repair:** Delete the first $(1 + h/X)$ on line 271 (`\le \frac1X\sum_{m\le X+h}\tau(m)^2 \ll (1+h/X)\log^3(X+h)`) and truncate both $k, h$ at $H$.

#### m6. Downward rounding of certified upper bound in §4.2
- **Location:** `notes/phase23/classical-correlations-and-log2.md`, line 322.
- **Issue:** The script outputs `r=7: ... total <= 0.74033`, while line 322 reports this rigorous upper bound as `0.740` (rounded *down*, strictly smaller than `0.74033`, whereas `0.05973` at $r=2$ was properly rounded *up* to `0.0598`).
- **Repair:** Change `0.740` to `0.741` (or `0.7404`) on line 322 so the displayed number remains a valid upper bound.

#### m7. $x_n$ vs $\{2^n \ln 2\}$ in §5.4 transition-to-Weyl-sum deduction
- **Location:** `notes/phase23/classical-correlations-and-log2.md`, line 402.
- **Issue:** Line 402 says *"Each one puts some $x_n$ in $[1/4, 3/4)$, which gives $\mathrm{Re}\, S_N(1) \le 1 - (1 + o(1)) \frac{\log N}{N \log \mu}$."* A binary digit transition puts $\{2^n \ln 2\}$ (not $x_n$) in $[1/4, 3/4)$; since $x_n = \{2^n \ln 2\} - r_n$ can cross $1/4$, the statement should refer to $\{2^n \ln 2\}$ directly (which is also the exact argument of $S_N(1)$ defined on line 343!).
- **Repair:** Replace `$x_{n}$` with `$\{2^n\ln2\}$` on line 402.

#### m8. Minor wording precision in §6 missing-estimate map
- **Location:** `notes/phase23/classical-correlations-and-log2.md`, lines 418, 422, 425.
- **Issue:**
  - Line 418 notes why BC-37 ($E$, `evidence = "external"`) is excluded from the 35 open constants, and could also briefly note BC-50 ($\alpha(2,3)\alpha(2,5)$, `full_normality = "open"`, `evidence = "paper"`, `discrepancy_status = "strict_upper_bound"`) is excluded because $D^+ \le 4/11 < 1$ is already proved.
  - Line 422 writes *"a positive lower density of $n$ with $\varepsilon_n / 2^{n+1}$ in a fixed subinterval"* for $\sqrt{2}$: the subinterval must be bounded away from $0$ and $\sqrt{2}$ (e.g. $[\sqrt{2}/4, 3\sqrt{2}/4)$, corresponding to $\{2^n\sqrt{2}\} \in [1/4, 3/4)$), since concentration inside $[0, \delta)$ still permits $D^+ = 1$.
  - Line 425 groups $C_1 = [0; 1, 2, 3, \dots] = I_1(2)/I_0(2)$ (BC-21) with $e, 1/e, e^2$ and writes "$2^n \sum_{k \le K} 1/k!$" in the missing-estimate column, which literally applies to $e$ rather than $C_1$ (whose approximants are ratios of Bessel factorial series / continued-fraction convergents $p_K/q_K$ with $q_K \sim c K!$).
- **Repair:** Tighten the phrasing in lines 418, 422, and 425 accordingly.

#### m9. Flawed tail-bound justification in `frac_digits` docstring
- **Location:** `scripts/phase23_classical.py`, lines 136–138.
- **Issue:** The docstring of `frac_digits` justifies the guard-bit margin `< 2^16` via `|coef[n]| <= tau(n) <= 2^15 for the indices used`. This is mathematically invalid as written because (i) the omitted tail sums over all $n > M$ to $\infty$, not just bounded indices, and (ii) for `c_4B2` ($4 \lfloor a_+(n)/4 \rfloor$), the coefficient can exceed $\tau(n)$ in magnitude (e.g. at $n = 4$, $a_+(4) = -1$, so $|4\lfloor -1/4\rfloor| = 4 > 3 = \tau(4)$). The actual certification is **still valid**: using the universal bound $|c(n)| \le \tau(n) + 4 \le 2\sqrt{n} + 4$ for all $n \ge 1$, the omitted tail in units of $2^{-M}$ at $M = 16544$ is bounded by $\sum_{k \ge 1} (2\sqrt{M+k} + 4) 2^{-k} < 262 < 2^9 \ll 2^{16}$.
- **Repair:** Update the docstring comment on lines 136–138 to use $|c(n)| \le 2\sqrt{n} + 4$ (and optionally assert $2\sqrt{M+2} + 4 < 2^{15}$).

#### m10. Off-by-one label in $\ln 2$ transition printout
- **Location:** `scripts/phase23_classical.py`, lines 863 and 869–876.
- **Issue:** Line 863 prints `binary transitions of ln 2 (#j < N with d_j != d_(j+1))` (which describes $N$ adjacent pairs), whereas the loop (line 870: `if n >= 1 and bits[n-1] != bits[n]`) counts transitions among `bits[0..N-1]`, i.e., $N - 1$ pairs ($1 \le j < N$ with $d_j \ne d_{j+1}$). The displayed counts (`529, 2107, 8209, 32824`) match the loop and the note table.
- **Repair:** Change `#j < N` on line 863 to `#1 <= j < N` (or `#0 <= j < N-1`).

#### m11. Unused / dead variables in script
- **Location:** `scripts/phase23_classical.py`, lines 578 & 591 (`diag` computed then deleted without use), line 668 (`keys = set(cnt)` unused), line 727 (`tv_r2 = tv / 2` unused).
- **Repair:** Remove the dead statements.

---

## Section-by-Section Independent Verification Log

| Section / Result | Independent Check | Status |
| --- | --- | --- |
| **Prop. 1.1** ($a_+$ parity, mod-4 Liouville law, $\sum \chi_4(a_+) = L(\lfloor\sqrt{X}\rfloor)$) | Re-derived: $a_+(k^2) = (1-2v)\prod(2\beta_p+1) \equiv (-1)^{v+\sum\beta_p} = \lambda(k) \pmod 4$. Landau PNT/RH equivalences accurate. Script verified to $2^{20}$, $L(1024) = -20$. | Verified |
| **Prop. 1.2** ($a_+ \equiv 2 \pmod 4$, $7:3$ split mod 8) | Re-derived: $p \mid s$ exclusion contributes $O(\sqrt{X})$ (since $p^3 \mid n$), $\alpha \ge 5$ contributes $O(\sqrt{X})$, sum $\frac{\pi^2}{8}\cdot\frac{4}{3} = \frac{\pi^2}{6}$; signed sum $\frac{\pi^2}{12}\cdot\frac{4}{5} = \frac{\pi^2}{15}$; halves give $\frac{7\pi^2}{60}, \frac{\pi^2}{20}$. All finite numbers match script. | Verified (see m2) |
| **Prop. 1.3** ($N_j(X) \asymp_j X(\log\log X)^{j-2}/\log X$) | Re-derived via $m = sr^2$, $v_2(\tau(m)) \ge \omega(s)$, Hardy–Ramanujan upper bound, odd squarefree $\omega(n)=j-1$ + Landau lower bound. | Verified (see m2) |
| **Lemma 1.4, Thm. 1.5, Cor. 1.6** (2-adic peeling) | Verified Lemma 1.4, SY-04 (`sharp_translation` in `SharpTranslation.lean`), P22 Prop. 1.3(1), $j=1$ theta identity $y_1 = \frac{1}{2}(\Theta_3(1/2)-1)$, rate bounds, $B_1(\tau) - B_1(a_+) = E(4)$, mean/mean-square of $B_j$, and transfer to $\tau, \tau_{\rm odd}, \sigma$. All table values match script. | Verified (see m3, m4) |
| **Prop. 2.1, Thm. 2.2, §2.3–2.5** (2-adic local factors, $\rho(h)$, $r$-point correlations) | Independently re-derived $\mathbb{E}_2[(1-v)(1-v')] = 2 - 3\cdot 2^{-k}$, $\mathbb{E}_2[(1+v)(1+v')] = 6 - 3\cdot 2^{-k}$, $\rho(h) = \frac{2^{k+1}-3}{3(2^{k+1}-1)}$, $\rho(0,1,2) = -1/11$, $\rho(0,2,4) = 1/24$, pointwise non-positivity for odd $h$, vanishing when $\{h_j \bmod 4\} = \mathbb{Z}/4\mathbb{Z}$, and (H2) truncation proof. Audited `local_E` and `poly_geom_sum` in script: exact and terminating. | Verified |
| **Thm. 3.1** (raw-tail second moments of $T_n, T_n^+$) | Re-derived unconditional $[\frac{1}{10}, 1]$ sandwich and exact $\frac{1}{9\pi^2}$ vs $\frac{1}{3\pi^2}$ leading constants via Ingham + diagonal $\sum 4^{-k} = \frac{1}{3}$. Independently recomputed $\kappa_\tau = 0.50338881$, $\kappa_+ = -0.06696536$. Backward fixed-point recursion in `section_T()` verified accurate to $O(2^{-63})$. | Verified with **M3**, m5 |
| **§4.1–4.3** (divisor lattice singular series & mod-4 mark correlations) | Re-derived generic $\sigma_p = (1-\frac{1}{p})^{r-1}(1+\frac{r-1}{p}) \in [1-(r-1)^2/p^2, 1]$ (AM-GM + Bernoulli), tail bound $1-(r-1)^2/P$, Prop. 4.1 Fourier product, exact odd-$p$ TV formula $r q_p (1 - (1-q_p)^{r-1})$, and tail $\frac{r(r-1)}{3\cdot 1000^3}$. Audited outward-rounded enclosures in `_euler_tail` and `section_M()`. | Verified (see m6) |
| **Props. 5.1–5.2** ($D^+(x;2) = 1 \iff \limsup |S_N(1)| = 1$, threshold $0.9997$, degree-2 minorant) | Re-derived both directions of Prop. 5.1, verified exact rational bound $(1-10^{-4})(1-(22\cdot 10^{-4}/7)^2/2) - 10^{-4} = 0.9997999506\ldots > 0.9997 \implies D^+ \le 0.9999$, and verified the minorant identity, bounds, and 3-line optimality proof (mean $\le 1/4$). | Verified (see m4) |
| **Thm. 5.3, Prop. 5.4, §5.3–5.4** ($\ln 2$ BBP band law, Glaisher–Wieferich, quantitative gap) | Re-derived Thm. 5.3, CRT component formula, Prop. 5.4 (verified signs on $p = 3, 5, 7$), $p \nmid Q_{p-1}$, and $\ln 2$ digit certification in `section_L()`. Verified unconditional $\log Q_n = (1+o(1))n$ follows from Thm. 5.3 + PNT. All numbers match script. | Verified with **M1**, **M2**, m1, m7, m10 |
| **§6** (missing-estimate map vs 50-constant roster) | Independently parsed `docs/benchmarks/classical-constants.toml`: 50 constants total, 35 with `full_normality = "open"` and `evidence = "open"`, exact bijection with §6 table and `CLUSTER_MAP`. Checked BBP status of $\ln 3 = 2\ln 2 - \sum \frac{1}{k 4^k}$ and $\ln 10 = 3\ln 2 + \sum \frac{(-1)^{k-1}}{k 4^k}$. Caught BC-24 error. | Verified with **M4**, m8 |
| **§7** (Lean 4 blueprint B1–B8) | Cross-checked all 8 signatures against `Phase22Cores.lean` and Lean 4 `Int.ediv`/`Int.emod` semantics (`/` on `ℤ` is Euclidean, matching floor division for divisor `2`). Note B8 includes `(h1 : p ≤ N)`. | Verified |

---

## Summary of Required Revisions Before Acceptance

1. **Fix M1** (`notes/phase23/classical-correlations-and-log2.md`, line 393): exclude $p \le \sqrt{n}$ and $p = 2$ from the inner product in §5.3 so boundary-band primes are not double-counted with $R_n$.
2. **Fix M2** (`notes/phase23/classical-correlations-and-log2.md`, lines 374 & 396): qualify single-prime equidistribution along band windows to cosets of $\langle 2 \rangle \subset \mathbb{F}_p^\times$ (exact up to $O(1/p)$ on $\mathbb{F}_p^\times$ when $2$ is a primitive root mod $p$).
3. **Fix M3** (`notes/phase23/classical-correlations-and-log2.md`, lines 38 & 273): cite the uniform-in-$h$ upper bound $C_\tau(h; X) \ll \frac{h}{\varphi(h)} \log^2 X$ ($1 \le h \le X$) needed to establish the $O(\log^2 X)$ bound and $(\kappa + o(1)) \log^2 X$ off-diagonal asymptotic, or weaken line 38 to $o(\log^3 X)$.
4. **Fix M4** (`notes/phase23/classical-correlations-and-log2.md`, line 428): correct $\pi/\sqrt{3}$ to $\pi/(3\sqrt{3})$ for BC-24.
5. **Address Minor findings m1–m11** (especially m1 adding $p \le N$ to Thm. 5.3, m5 removing the spurious $(1+h/X)$ factor in Thm. 3.1's proof, m6 rounding `0.74033` up to `0.741`, and m9 fixing the `frac_digits` tail-bound comment).

---

## Post-Repair Verification

**Re-audited files (read-only):**
- `notes/phase23/classical-correlations-and-log2.md` (553 lines)
- `scripts/phase23_classical.py` (999 lines)

**Execution check:** `python -B scripts/phase23_classical.py` exited `0` (`ALL CHECKS PASSED (4580653 checks) in 11.5 s`). Every quoted count, ratio, enclosure, bound, and table entry in `notes/phase23/classical-correlations-and-log2.md` matches the script output verbatim (including the updated `4,580,653` assertion count, `1,038` Lemma 3.2 pairs with max ratio `0.4777`, `2,999` $Q_N$ factorizations, `333` band-window pairs split `133` primitive-root / `200` non-primitive-root, and window averages `0.4926` at $p = 7$ and `0.5467` at $p = 31$).

### Major Findings Closure (M1–M4)

- **M1 — Closed.** Section 5.3 (lines 439–451) now defines the single index set $P_n = \{\text{odd prime } p : \sqrt{n} < p \le n,\ p \nmid A_{m_p}\}$ with $m_p = \lfloor n/p \rfloor < \sqrt{n}$, so $Q_n = (\prod_{p \in P_n} p) Q_n'$ with $Q_n'$ supported solely on $2$ and primes $q \le \sqrt{n}$ (explicitly verified in the script for all $2 \le N \le 3000$). Boundary-band primes $q \le \sqrt{n}$ (e.g., $q = 3$ at $n = 10$, $q = 5$ at $n = 26$) are no longer double-counted, the sum starts at $2 \le n < N$, and the $O(\log N / N)$ transition from $x_n$ to $\{2^n \ln 2\}$ via $|S_N(1) - \frac{1}{N}\sum_{n < N} e(x_n)| \le \frac{2\pi}{N}\sum_{n < N} r_n \to 0$ is explicitly proved.
- **M2 — Closed.** Section 5.2 (lines 418–423) and §5.3 (line 451) now accurately describe the band-window trajectory on $[mp, (m+1)p)$: the $p$-component visits the coset $c\langle 2 \rangle \subseteq \mathbb{F}_p^\times$ of size $t = \operatorname{ord}_p(2)$ with each element occurring $(p-1)/t$ times except $c$, which occurs once more. Primitive-root primes ($t = p-1$) yield window average $\frac{1}{p}(-1 + e(c/p))$ of modulus $\le 2/p$ (equidistribution on $\mathbb{F}_p^\times$ up to $O(1/p)$); non-primitive-root behavior is explicitly documented ($p = 7, 31$, Mersenne primes), and both the Gauss-period bound $((k-1)\sqrt{p}+1)/k < \sqrt{p}$ (verified directly via character expansion) and Erdős–Murty (1999) are properly labeled external.
- **M3 — Closed.**
  - **Lemma 3.2** (lines 283–297) verified line by line: $\tau(m) \le 2\#\{d \mid m : d \le \sqrt{m}\}$, $n + h \le 2X = Y^2$ for $1 \le n, h \le X$, solvability of $d \mid n, e \mid n+h$ implies $g = \gcd(d, e) \mid h$ with $\le Xg/(de) + 1$ solutions $n \le X$; writing $d = gd', e = ge'$ and dropping $\gcd(d', e') = 1$ yields the main term $\le 4X \sigma_{-1}(h)(1 + \log Y)^2 = 4X \sigma_{-1}(h)(1 + \frac{1}{2}\log(2X))^2$, while summing the $+1$ over all pairs $1 \le d, e \le Y$ contributes at most $4\lfloor Y \rfloor^2 \le 4Y^2 = 8X$; finally $\sigma(p^a)\varphi(p^a) = p^{a-1}(p^{a+1} - 1) < p^{2a}$ gives $\sigma_{-1}(h) \le h/\varphi(h)$.
  - **Theorem 3.1** (lines 275–317) verified line by line: splitting at $k + h \le X$ (bounded via Lemma 3.2 at $X' = X + k \in [X, 2X]$ by $C\,\sigma_{-1}(h)\log^2 X$) versus $k + h > X$ (bounded via Cauchy–Schwarz by $\ll (k+h)^4$, contributing $O(\sum_{s > X} s^5 2^{-s}) = o(1)$) proves $\mathrm{Off}_X(c) = O(\log^2 X)$ unconditionally, dominates the diagonal by $\ll 4^{-k} k^4$ and the $k + h \le X$ off-diagonal terms by $C\,2^{-2k-h}\sigma_{-1}(h)$ for Tannery's theorem, yielding $\kappa_\tau = \frac{4}{\pi^2}\sum_{d \ge 1} \frac{1}{d(2^d - 1)}$ unconditionally from Ingham + Lemma 3.2 and $\kappa_+$ conditionally on (H2). Summary table lines 38–39 match.
- **M4 — Closed.** Section 6 (line 483) now reads $\pi/(3\sqrt{3})$ for BC-24 ($L(1, \chi_{-3})$), matching `docs/benchmarks/classical-constants.toml`.

### Minor Findings Closure (m1–m11)

- **m1:** $\sqrt{N} < p \le N$ added to Theorem 5.3 (lines 44 and 403).
- **m2:** Joint truncation $2^e s^2 \le X^{1/2}$ (with dominated convergence for PNT) and $2^e r^2 \le X^{1/2}$ cleanly stated in Propositions 1.2 and 1.3 (lines 79–86, 107).
- **m3:** Corollary 1.6 (lines 136–146) adds $c(n) \in \mathbb{Z}$, $\sum |c(n)| 2^{-n} < \infty$, separates the qualitative $K_2$-equivalence from the quantitative rate, clarifies $y_1(\tau_{\rm odd})$, and tightens $\sigma(n)$ via $v_2(\sigma(n)) \ge \#\{p > 2 : v_p(n) \text{ odd}\}$.
- **m4:** Half-open $\varepsilon \to 0^+$ limit added to Lemma 1.4 (line 119); $\varepsilon \in [0, 1]$ and $\delta' \to 0^+$ supremum limit added to Proposition 5.1(1) (lines 391, 395).
- **m5:** Spurious $(1 + h/X)$ factor removed and both $k, h$ jointly truncated via $k + h \le X$ in Theorem 3.1 (line 309).
- **m6:** Certified upper bound at $r = 7$ rounded up to `0.741` (matching `<= 0.74033`, line 366).
- **m7:** Line 457 now refers to $\{2^n \ln 2\} \in [1/4, 3/4)$ directly.
- **m8:** Section 6 now notes BC-50's exclusion (line 473), bounds $\{2^n \sqrt{2}\}$ in a closed subinterval of $(0, 1)$ away from $0$ and $1$ (line 477), and separates $C_1$ convergents $p_K/q_K$ ($K! \le q_K \le (K+1)!$) from $e, 1/e, e^2$ (line 480).
- **m9:** `frac_digits` docstring (lines 136–143) now uses the universal bound $|c(n)| \le \tau(n) + 4 \le 2\sqrt{n} + 4$ for all $n \ge 1$ with an explicit runtime assertion `2 * isqrt(2 * M) + 7 < 2^15`.
- **m10:** Transition printout label corrected to `#{1 <= j < N : d_j != d_(j+1)}` (line 931).
- **m11:** Dead variables removed from `section_T` and `section_M`.

### Final Verdict

**ACCEPT.** All Major findings (M1–M4) and Minor findings (m1–m11) are cleanly and rigorously closed, with no regressions introduced and full computational verification (`4,580,653` checks passing, exit code `0`).

**Notice:** Cross-model review is not independent human peer review.
