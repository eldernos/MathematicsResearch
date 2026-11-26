# Referee review: Phase 22 Track D (D1–D2), normal reciprocals, sign classification and the cyclotomic family

**Reviewer:** Claude Opus 5.5 (cross-provider audit of a Gemini 4 Neon draft).
**Audited files:** `notes/phase22/normal-reciprocals-and-signs.md` (792 lines) and `scripts/phase22_reciprocals.py` (882 lines), both read in full.
**Scope warning:** This is a cross-model review. It is **not** independent human peer review, and it does not change any evidence label by itself.

---

## 0. Summary

| Result | Verdict |
|---|---|
| Theorem 1 (exact periods $m_kD_{k-1}$ and $2m_k$, Hull–Dobell lifting, LTE) | **Correct.** Every case checked: odd $p$, $2\parallel D$, $4\mid D$, and $b=2,m=1$. |
| Theorem 2 (sharpened Weyl bound, divisor-sum Erdős–Turán, grid bound, Koksma lower bound) | **Correct.** The constant drops from 3 to 1, and the drop is tight in practice: $\lvert W_{15}\rvert=0.310$ against a main term of $1/3$. |
| Theorem 3(1) (balanced rate) | **Correct as a bound.** Calling it "optimal" is not justified (Major M2). |
| Theorem 3(2) (universal barrier, admissible family) | **Correct.** The extension to the relaxed Hull–Dobell family is unproved (Major M1). |
| Theorem 4 (complete sign classification) | **Correct.** The −1 transition-shell argument (Prop. 4.4) has no gap at the shell boundaries. |
| Theorem 5 (oriented digit laws) | **Correct** up to $o(1)$ mass. One wording point (Minor m16). |
| Proposition 5.1 and Lemma 5.2 (closed form of $P_k$) | **Correct.** I re-verified independently for $k\le60$. Two small proof and statement gaps (m2, m3). |
| Theorem 6(1) (simply normal in base 2 with $y\in K_2$) | **Correct.** The hostile check passed (§3.6). |
| Theorem 6(2) (prescribed $D^+=\alpha$ together with base-2 simple normality) | **Very likely true, but the proof is only a sketch** (Major M3). |
| §6 Lean blueprints | One blueprint is vacuous and one is mislabelled (Major M4). |

**Critical findings: none. Major: 4. Minor: 16.**

---

## 1. Reproduction of the verification script

```sh
python -B scripts/phase22_reciprocals.py
```

- Exit code **0**. Wall time 0.83 s; the script reports 0.71 s, which matches §7.
- Output ends with `All 72027 checks passed in 0.71 s`, matching the 72,027 checks claimed in §7.
- **Every displayed number matches the output.** I compared each value in the note's tables and in §7 items 1–5 against the printed output. This covers the $T$-sequences for all 15 cases, 590/196 Hull–Dobell triples, the counterexamples $(3,1,4)\to2$ and $(3,1,8)\to4$, 14,040 partial-band tuples, 11 moduli, the comparison table (1.5055/1.0824 … 8.7251e-08/7.3533e-12, 11865.6×), the grid $D(\mu_K)$ and $W_1$ rows, $\lvert W_{45}(m_4)\rvert=0.93071$, Koksma 0.00658 ≤ 0.01970, the log-tower values 72941.5/100.14/728.4, the 72 signed runs and 448 plus-sign triples, all of [4a]–[4d], the $k=1..25$ closed form, [5b] in bases 2, 3, 5 and 10, [5c] (0.8906/0.7500 → 0.8829/0.5909, 0+ = 0.5187, 1− = 0.3332, $f_{00}$ = 0.5772, $f_{11}$ = 0.3954, $J=500$: 0.05935 and 0.000999), and all five rows of [5d]. The only rounding is "11,866×" in the note against 11,865.6× printed.
- **Where the checks come from.** I instrumented `CHECKS` by section:

  | Section | Checks |
  |---|---|
  | 1 (D1.1) | 2,693 |
  | 2 (D1.2) | 14,241 |
  | 3 (D2.1) | 2,456 |
  | 4 (D2.2, Theorems 4–5) | **109** |
  | 5 (D2.3) | **52,528** |

  Most of the 52,528 in section 5 are per-coefficient asserts inside `poly_div_exact` (line 677). The divisor there is monic, so these asserts are trivially true. The headline "72,027" therefore overstates how much is actually verified. Theorems 4–5 rest on 109 checks with tolerances of 0.025–0.03 (Minor m11).

### Independent checks (my own code, standard library, run with `python -I`)

1. **Theorem 1(1)** holds on 1,782 triples with $2\le b\le12$, $1\le m\le8$, $D\le400$ and $\operatorname{rad}^*(D)\mid b^m-1$. **Theorem 1(2)** holds on 924 triples with $D\mid b^m-1$. There are no exceptions.
2. **Proposition 5.1** holds for every $k=1,\dots,60$. I built it directly from the power series of $1/P_k$, not by polynomial division, and checked:
   - period $L_k$;
   - no internal zeros and exactly $2p$ trailing zeros;
   - positive count $2(k+2)(2k+1)$ and negative count $2k(2k+1)$;
   - $\max\lvert S_i\rvert=2k+2$ and $\max\lvert c_s\rvert\le2$;
   - $\sum_{d\ge1}\lvert a_{k,d}\rvert<4(k+2)^2$;
   - on every trailing zero band $i=L-d$, the tail begins with exactly $+q^d$. In fact $\tau_{L-d}^{(k)}(q)=q^d/P_k(q)$ identically, because $c$ has period $L$.
3. **Sharpened Weyl bound (Theorem 2(1)) on partial-band prefixes.** The script only tests $N=m_4$. I tested $b=2$, $m=(2,4,48,43200)$, $h\in\{3,5,9,15\}$ and $N\in\{2m_4-1,\,3m_4-1,\,3m_4,\,3.5m_4,\,4m_4-1,\,m_4+7T_3\}$. The bound holds everywhere. The worst ratio of $\lvert W_h\rvert$ to the bound is 0.805. At $h=15$, $N=3m_4-1$, I get $\lvert W\rvert=0.3102$ against the new bound 0.3855 and Phase 21's bound 1.0522. The improvement from 3 to 1 is genuine, and $g/D_{K-2}$ is essentially attained through the partial band.
4. **Lemma 2.3 threshold.** At $D=e^{e^2}$, $P=\ln D/(\ln\ln D)^3=0.924<1$ (Minor m1).

---

## 2. Findings

### Critical

None. I found no counterexample and no false main conclusion.

### Major

**M1. Theorem 3(2): the barrier for the relaxed Hull–Dobell family is unproved.** (Line 59; lines 367–373.)
The statement says that relaxing (A1) to $\operatorname{rad}^*(D_{k-1})\mid b^{m_k}-1$ "yields the same growth lower bound and universal barrier."

The growth bound does carry over. The barrier proof (lines 336–365) does not. It uses Lemma D2.1 with band multiplier $i+1$, which needs $b^{m_K}\equiv1\pmod{D_{K-1}}$. It also needs complete $T_{K-1}$-cycles inside each band.

Under the relaxed hypothesis, the band multiplier is $S_i(b^{m_K})$. Only its class modulo $b^{m_{K-1}}-1$ matters, because $D_{K-2}R_{K-1}$ has denominator $b^{m_{K-1}}-1$. That class need not equal $i+1$: it fails whenever some prime power of $b^{m_{K-1}}-1$ does not divide $b^{m_K}-1$. Then $a D_{K-2}\eta_s^{(K-1)}$ gets multiplied by a large residue rather than a small $a\le I_K$, and the step $\lvert\widehat C_{K-1}-1\rvert<1/3$ fails. Lines 367–373 are a heuristic ("no sub-polynomial Korobov bound is available"), not a proof. The note also never shows that $y$ is normal under the relaxed hypothesis.

*Fix:* delete the last sentence of Theorem 3(2) or move it to a labelled remark or conjecture. Alternatively, prove the barrier for the relaxed family with a different choice of $N_K$.

**M2. Theorem 3(1) and §3 call the balanced rate "optimal" without proof.** (Line 48 title "optimal rate in terms of $N$"; line 50 "Achieved optimal rate"; line 100 status row "balanced optimal rate"; line 278 heading; line 328 "strictly optimal in $N$"; line 332 "cannot improve".)
The achieved upper bound is $1/\exp^{(r)}((\ln^{(r+1)}N)^A)$. The barrier is $1/\exp^{(r)}((\ln^{(r)}N)^{\varepsilon})$. These differ by one iterated logarithm, so neither optimality inside the admissible family nor optimality of $\omega_k=D_{k-1}$ is established. The bullets on sub-balanced and super-balanced regimes (lines 330–332) are heuristic comparisons.

*Fix:* rename the result to "balanced rate", state the gap of one iterated logarithm as open, and label lines 328–332 as heuristic.

**M3. Theorem 6(2): the written proof is a sketch.** (Statement line 94; proof lines 670–693.)
I believe the statement is true; my outline of a complete argument is below. But the text does not prove it:

- *"Applies verbatim"* (line 693) is wrong. Proposition 4.4 is built on ±1 shells. Its strata are binary band bits with $T_u=2m_u$, every zero band has depth $d=1$, and the melting fraction is $\beta_u(I)=\log_bI/m_u$. In the cyclotomic setting:
  - the strata are pairs $(u,d)$ with zero-band depth $d\in[1,4k_u+2]$;
  - the δ₀ points have size about $\lvert\prod S\rvert\,b^{r_u-dm_u}$;
  - the melting fraction is therefore $\beta_{u,d}(I)=\min(1,\max(0,(\log_bI-(d-1)m_u)/m_u))$, not $\beta_u(I)$;
  - Regimes 1 and 2 must carry the cumulative multiplier $\prod S$ (with $\lvert\prod S\rvert\le M_s$) into both the gcd bound and the bound $\|hSb^tR\|\ge1/D$;
  - the Erdős–Turán cutoff $H$ is never chosen. $H=H_s$ with $H_s\to\infty$ and $H_s=o(2^s)$ works, since $hM_s/D_{n_s}\le H/(2^sM_s)$.
- *Simple normality "along all $N$"* (line 693, "$f_0(N;y)=\tfrac12+O(1/s)$") is asserted without derivation. Line 691 tracks only the complete-period bias. A full proof needs three more steps:
  1. **Prefixes inside a partly traversed $L_k$-block.** The first bands of every block are positive ($S_0=1$, $S_1=3$, …), so the contraction factor $1/(k+1)$ does not apply on prefixes. The correct estimate is $\lvert B_N\rvert\le\lvert B_{k-1}\rvert+\rho_k$, where $B_k=(2B_{k-1}+1)/(2k+3)$ is the complete-period recursion; that recursion is exactly script line 836.
  2. **Bias during melting.** In each stratum $(u,d)$, the sign $\prod_{v>u}\operatorname{sgn}S_{i_v}$ is independent of $(r_u,d)$. So melting removes the same fraction of $0^+$ and $1^-$ mass in that stratum. Each stratum bias is nonnegative and the stratum biases sum to $B_{\text{end}}=O(1/s)$.
  3. **Edge sets.** On the melting shell, the positive tail $\eta_r^{(n)}$ can turn a $1^-$ point into a $0^+$ point when $\eta_r^{(n)}>a\lvert x_t\rvert$. This happens only on a set of proportion $O(k\,m_u/m_n)$.
- *Endpoint $\alpha=1$* (line 672). The case $D^-=0$, $D^+=1$ together with base-2 simple normality is covered only by the unwritten phrase "alternating −1 resets with $P_j$ runs of growing length". Theorem 6(1) does not cover it, because there $D^-=1$. The general construction with $t_s/s\to\infty$, so that $f_s(t_s)\to0$, does work and should be written out.

*Fix:* write out the three items above. Until then, label Theorem 6(2) "Paper proof (sketch)" in the status table (line 102).

**M4. §6 Lean blueprints: one is vacuous and one is mislabelled.** (Lines 742–761, 764.)

- `cyclotomic_band_identity` (lines 745–752) asserts `∃ z tail, LHS = A.coeff (i % L) * b^r * R + tail + z` and puts no constraint on `tail`. It is trivially true: take `tail := LHS - …` and `z := 0`. A proof would carry no information about Lemma 5.2.
  *Fix:* require `tail = b^r * R * τ(b^{-m})` with τ the series tail, or at least $\lvert\text{tail}\rvert\le 3(4/3)b^{r-m}$ on nonzero bands and $\text{tail}>0$ on zero bands. Also add `Nat.Coprime b R.den`.
- `cyclotomic_Pk_sign_counts` (lines 755–761) is labelled "Proposition 5.1 (exact positive, negative, and zero band counts)". Its statement is the arithmetic identity $2(k+2)(2k+1)+2k(2k+1)+(4k+2)=L$. It does not mention $A_k$ or any sign. It is also the only declaration without `sorry`, so it is the one most likely to be reported later as kernel-verified.
  *Fix:* state the counts as `((Finset.range L).filter (fun i => 0 < (A k).coeff i)).card = 2*(k+2)*(2*k+1)` and so on, or rename it to `pk_band_count_total`. I have not checked whether `ring` closes a goal that still has `let` binders; it may need `intro` or `simp only` first.

### Minor

- **m1. Lemma 2.3 threshold** (line 216). At $D=e^{e^2}$, $P=0.92<1$, so the claim that $D\ge e^{e^2}$ gives $P\ge1$ is false. Replace it with "for all sufficiently large $D$". It is asymptotic anyway.
- **m2. Proof of $\lvert S_i^{(k)}\rvert\le2k+2$** (line 598). From $\max\lvert s_n\rvert\le k+1$ one only gets $\lvert t_n\rvert=\lvert2s_{n-1}+g_n\rvert\le2k+3$. One more line is needed: when $\lvert s_{n-1}\rvert=k+1$, either $g_n=0$ or $g_n$ has the opposite sign. Equality $2k+2$ is verified for $k\le60$. Only $\lvert S\rvert\ll b^J$ is used later, so nothing downstream is affected.
- **m3. Lemma 5.2(1)** (lines 613, 619). The claim $\operatorname{den}(R')=\operatorname{den}(R)P_k(b^m)$ is false for general $R$, because the numerator of $R$ may share factors with $P_k(b^m)$. It is true when the numerator is a power of $b$, which holds in every application. Add that hypothesis. Also state that $P_k(b^m)\equiv P_k(1)=1\pmod{\operatorname{den}R}$; this is the reason the denominators are coprime. The divisibility $\operatorname{ord}\mid L_km$ is unaffected.
- **m4. Theorem 3(2), case $r\ge3$** (line 365). "$u_K\ge e^{u_{K-2}}-o(1)$" should read "$-O(1)$", since the constant $\ln((\ln b)/2)$ can be negative. The contradiction still follows.
- **m5. §5 introduction** (line 548). "Mixing $0^+$ and $1^-$ into exact ½/½ balance" should say the balance is asymptotic. State the mechanism plainly: all $4k+2$ zero-band tails are $0^+$ (since $\tau_{L-d}=q^d/P_k(q)$); nonzero bands are biased positive ($\mathbb E[\operatorname{sgn}\mid\ne0]=1/(k+1)$); balance comes from $\prod_v 1/(v+1)\to0$ over later levels; and the bias decays like $B_J\sim1/J$.
- **m6. Irrationality in Theorem 6(1)** (line 89) is asserted but never argued in §5.3. It follows in one line: an eventually periodic digit string cannot have $f_{0^L}\to\tfrac12$ for $L$ longer than its period.
- **m7. Line 274.** The comparison uses $D_3=45(2^{48}-1)$ from the non-balanced Phase 21 sequence $(2,4,48,43200)$ as if it were a balanced $D_{K-2}$. The balanced sequence from $(2,4)$ has $m_3=36$. The comparison also drops the $c_b(H)/m_K$ term. State both.
- **m8. Internal track labels in headings** (lines 108, 178, 278, 377, 546; §7 items 1–5). Labels such as "(D1.1 & D2.1)" and "(D2.2)" collide with cited Phase 21 labels in the same text: Lemma D2.1, Lemma D2.2 (line 244), Proposition D2.3 (line 39) and D2.5 (line 425). Remove the process numbering. I found no "the brief" or similar process wording in the note.
- **m9. Theorem 1 statement** (lines 25–26). "With zero exceptions across all $b\ge2$, $m\ge1$, $D\ge1$" reads like an empirical claim inside a theorem. Delete it.
- **m10. Theorem 4(1) proof** (line 521) cites Theorem 2, which assumes $\varepsilon\equiv-1$. Cite Proposition 4.4 with $r=0$, or Phase 21 Proposition D2.5 (converse), instead.
- **m11. "72,027 exact and certified checks"** (line 774). About 44,000 of the checks are trivial monic-division asserts. Section 4 has 109 checks. Values are float measurements of orbits truncated to 40 bits, not certified intervals. Give the per-section counts and drop "certified".
- **m12. [4d] melting "verified"** (line 779). The script's only test is `d_obs <= 0.8833` (script line 642). The observed $D$ differs from the asymptotic $\alpha$ by 0.04–0.07. Call it an illustration.
- **m13. Script hygiene.**
  - Comments that read like working notes: lines 155–157, 567, 623–624 ("No, use m3=24!", "Wait:"), 790–794.
  - Stale values: line 291 says "D in 1..120" but the loop is `range(1, 101)`; line 382 has `192`, later overwritten by $\tau(D_3)=1920$; line 532 lists "m = (4,16,96,768)" but the code uses `(4,24,192,1920,15360)`.
  - Dead variable `m_init` at line 565; redundant ternary at line 451.
  - The example $m_k=2^{k-1}k!$ in Theorem 4(2) is not the sequence the script uses.
- **m14. Lean wording.** `shifted_grid_arc_excess_le` covers only non-wrapping intervals $[a,c)$, while its name says "arc". "`orderOf_mul_pow_add_one` … pure elementary arithmetic (omega/nlinarith)" (line 764) overstates things: `orderOf` in `ZMod` needs `orderOf_eq_iff` or similar.
- **m15. Theorem 6(2) growth condition** (line 683). $\prod_{j\le n}(4k_j+3)(2k_j+3)^2$ is undefined at the $(1-q)$ factors. Define a degree and height for every $Q_n$.
- **m16. Theorem 5 wording** (line 70). "Every concentration … strictly from above" holds only up to $o(1)$ mass. When no −1 factor precedes a +1 run (for example $\varepsilon\equiv+1$, so $R_0=1$), the all-even stratum, of weight $2^{-r_K}$, lies at $1^-$. The asymptotic statements are unaffected. Add "outside a set of asymptotic density 0".

---

## 3. Audit notes, theorem by theorem

### 3.1 Theorem 1 (D1.1, D2.1)

- **Lemma 1.1 (LTE).** The binomial expansion is correct for $p=2$: the middle sum is empty and the last term is $2^a$ with $a\ge2$. It is correct for $p\ge3$: $a(p-1)\ge2$. The induction keeps $4\mid q^{p^i}-1$, and the cofactor with $p\nmid r$ has valuation 0.
- **Theorem 1(1).** The equivalence $(b^m-1)\mid(b^M-1)\iff m\mid M$ is correct; the case $b=2,m=1$ is handled. The prime-power cases are complete:
  - odd $p$: LTE;
  - $2\parallel D$: parity of $\sum q^j$;
  - $4\mid D$: LTE with $4\mid q-1$.
- **Bijection of $S_i(b^m)\bmod D$.** Correct; this is the Hull–Dobell theorem. The 2-adic sharpness examples lie outside the hypothesis, as stated. Necessity (line 373) is also correct: if $q\not\equiv1\pmod p$, the sums $S_i$ miss the class $-1/(q-1)\bmod p$; if $4\mid D$ and $q\equiv3\pmod4$, then $S_i\bmod4$ alternates $1,0$.
- **Theorem 1(2).** All three remainder cases are correct.
- **Theorem 1(3).** $T_k=2m_k$ when $\varepsilon_k=+1$ follows from part 2 with $D=D_{k-1}\mid b^{m_k}-1$. $T_k\ge m_k$ is correct.

### 3.2 Theorem 2 (D1.2)

- **Lemma 2.1.** The identity $(d'-1)(r_0-m)\le0$ is exact.
- **Theorem 2(1).** The bound uses Phase 21's band identity and Lemma D2.2 (exact vanishing of $\widehat C_{K-1}(ha)$ unless $D_{K-2}/g\mid a$) together with Lemma 2.1. The constant is genuinely 1, not 3; independent check 3 confirms it with a partial band.
- **Lemma 2.2, Erdős–Turán assembly, Theorem 2(2).** Correct. The $\ln D$ factor is absorbed into $\exp(o(\ln D/\ln\ln D))$.
- **Lemma 2.4.**
  - Part (1): $W_1(U_D,\lambda)=1/(4D)$ is correct.
  - Part (2): the integration by parts is correct ($\int_0^1(\mathbf 1_{x<t}-t)\,2\pi ih\,e(ht)\,dt=-e(hx)$), and centring gives $\lvert W_h\rvert\le\pi hD_N$.
- **Theorem 2(3).**
  - The grid bound holds with no tail loss and a correct perturbation step: $L=\lceil\log_b64N\rceil$.
  - Lower bound: $D_{K-2}b^{jm_{K-1}+s}R_{K-1}\equiv D_{K-2}\eta_s$, so $\lvert\widehat C_{K-1}(D_{K-2})-1\rvert\le c_b(D_{K-2})/m_{K-1}\to0$ because $\log_bD_{K-2}=o(m_{K-1})$. Sharpness of the exponent −1 at $N=m_K$ follows.

### 3.3 Theorem 3

- **Part (1).** The asymptotics check out:
  - $a_{k+1}=(2+o(1))m_{k-1}$;
  - $\ln^{(r)}D_{K-2}=(2\ln b+o(1))m_{K-2r}$ for $r\ge2$;
  - $\ln^{(r+1)}m_{K+1}=(2\ln b+o(1))m_{K-2r-1}$;
  - the comparison $m_j\gg m_{j-1}^A$.

  The script's tower values reproduce exactly: $m_3=36$, $m_4=72900$, $\log_2D_4=72941.5$. Only the word "optimal" is a problem (M2).
- **Part (2).** The choice of $I_K$ and $N_K<T_K\le m_{K+1}$ is correct. The bounds $2L_a<m_{K-1}/4+2$, $\lvert\widehat C-1\rvert<1/3$ and $\lvert W\rvert>1/2$ follow. The two-step iteration contradicts $m_K\ge b^{m_{K-2}}-1$ for both $r=1$ and $r\ge2$. The admissible-family barrier is **correct**. The relaxed-family sentence is not proved (M1).
- **Consistency.** The barrier does not contradict Phase 21 §5.6. It also agrees with Theorem 3(1): at $N_K$ the lower bound is about $D_{K-2}^{-1}$ while $\ln N_K\asymp m_{K-1}$.

### 3.4 Theorem 4 and Propositions 4.2–4.4

- **Prop. 4.2(1)–(2).** Correct. In particular, $b^{m_K+r}R_K\equiv+\eta_r^+$ on odd bands, the transport cost is at most $4/((b-1)m_K)$, and the unrolling in (3) is correct. With $K_0=0$, $\mu_0=\delta_0$ exactly.
- **Prop. 4.3.** Correct, including $\theta_K\in[\tfrac12,1]$ and the weight $1/(2\omega_{K-1})$ of the incomplete cycle.
- **Prop. 4.4 (the requested check of the boundary at $m_K$).**
  - Strata and densities: because $2m_u\mid m_{u+1}$, the bits $\lfloor t/m_u\rfloor\bmod2$ are independent and uniform. That gives density $2^{-r}$ for $E_2$ and $2^{-(K-u)}$ for $E^{(u)}$.
  - (4.1) and (4.2) are exact.
  - $E_2$ is a union of complete $R_{K_0}$-periods, since its residues modulo $m_{K_0+1}$ are unconstrained.
  - Regime 1: the bound $2c_b(ha)/m_{K_0+1}$ comes from the geometric collapse $2m_u/m_{u+1}=1/\omega_u$. Choosing $H\le m_{K_0+1}/m_{K_0}$ makes the $(1+\ln H)$ loss harmless.
  - Regime 2: $\|hy_t\|\ge1/D_{K_0}$ holds for every $t$, because $b^tA_{K_0}$ is a unit and $h<D_{K_0}$. The Kronecker bound is $2D/(3I)+1/I\le2/D$ when $I>D^2$.
  - Step 2: $r_u$ is exactly uniform on $E^{(u)}$; the size window $(\tfrac14b^{r_u-m_u},4b^{r_u-m_u})$ is correct; the bound $\lvert\widehat\kappa_I(h)\rvert\le2b^{-\Delta_u}$ is correct.
  - **Boundary.** At $N=m_K$ ($I=1$), $\alpha_K=1-2^{-r}$, which equals the value $1-\theta_{K-1}(m_K)2^{-r_{K-2}}$ from the preceding +1 shell, since $\theta=\tfrac12$ because $2m_{K-1}\mid m_K$. At $N=m_{K+1}$, $I=\omega_KD_{K-1}\ge b^{m_{K-1}}-1$, so every $\beta_u=1$ and $\alpha=0$. This matches the start of the next shell, which has $\alpha=0$ if it is −1 and $\alpha=1-\theta$ starting from 0 if it is +1. Regimes 1 and 2 are complementary and cover every $I$. The multipliers $a=i+1$ are applied to the exact rational $x_t$, so wrap-around for $I>D_{K-1}$ causes no problem.

  **I found no gap.**
- **Theorem 4(3).** Limit sets, $D^-=0$ and $D^+=1-2^{-R_{\max}}$ follow via Lemma 4.1(2)–(3). The proof of Lemma 4.1(2) is correct, giving $2\eta+w/\eta$ minimised at $2\sqrt{2w}$.

### 3.5 Theorem 5

The $0^+$ orientation holds in four places:

- on odd bands: $+\eta^+$;
- on +1 even bands: (4.2) applied at level $K$, where the level-$K$ correction $-\eta_r^+$ is an "upper tail" handled by the edge set $r_K\ge m_K-2m_u-6$;
- on −1 shells: $a x_t>0$ and $\eta^{(K)}>0$;
- in the step from $y$ to $R_K$.

The digit formulas follow, and simple normality is equivalent to normality within this family. The only caveat is m16.

### 3.6 Theorem 6: the hostile check

**(i) Integrality and $x\in K_b$.**
- $P_k=\bigl(\sum_{s<p}(-q)^s\bigr)\bigl(\sum_{t<r}(-q)^t\bigr)\in1+q\mathbb Z[q]$ has degree $2p=4k+2$ and coefficient $\ell^1$-norm below $pr<4(k+2)^2$.
- Support up to $N$: the number of tuples is at most $2\prod_{j\le J}(4j+3)=e^{O(J\ln J)}$, and $J\le(\log_bN)^{1/3}$. So the support is $N^{o(1)}$, the coefficients are $N^{o(1)}$, and $x\in K_b$ by Phase 20 Lemma 0(a). The growing number of terms in $P_j$ is absorbed by the $b^{(j+1)^3}$ factor.
- I checked $\sum_j\lvert P_j(b^{-m_j})-1\rvert<\tfrac14$ (about $0.008$ for $j=1$ with $q=b^{-8}$).

**(ii) Structure of $A_k$.**
- I re-derived the closed form of $G_k$: $g_n=(-1)^m$ on $[mp,mr+1]$ for $m<k$, the centre block $[kp,kr]$, and $g_{(k+1)p}=0$. The sequence $S_{\text{after}}(m)=m+2$ or $-(m+1)$ also checks out.
- $t_n\notin\{0,2\}$ on $[0,p^2)$, using (5.1).
- The four ranges of $S_i$ are correct; in particular $pr+p^2=L-2p$.
- Sign counts: the involution $n\leftrightarrow p^2-1-n$ has one fixed point, where $t=1$, and $t=1$ occurs exactly $p$ times. This gives $p(p+1)/2$ positives and $p(p-1)/2$ negatives on $[0,p^2)$, hence $p(p+3)$ and $p(p-1)$ in total.
- $\lvert c_s\rvert\le2$ follows from the disjoint supports.

**Answer to the question in the brief.** All $4k+2$ zero bands are oriented $0^+$, because $\tau_{L-d}^{(k)}(q)=q^d/P_k(q)>0$; I verified this for every $d$ and every $k\le60$. The nonzero bands are **not** balanced: there are more positive bands than negative ones, with $\mathbb E[\operatorname{sgn}]=1/(k+1)$. The ½/½ split for $y$ comes from composing levels. A zero-band point created at level $u$ has sign $\prod_{v>u}\operatorname{sgn}S^{(v)}_{i_v}$, whose conditional mean is $(u+1)!/(J+1)!\to0$. The last level contributes a pure $0^+$ fraction of only $1/(2J+3)$. This is what Step 2 proves, and it is correct.
- The mixed-radix coordinates are independent: $m_j=b^{j^3}L_{j-1}m_{j-1}$.
- $r_u$ is independent of $(i_u,\dots,i_J)$.
- The edge event $\{q_v=b^{v^3}-1\}$ is independent of every $i$.
- $\lvert E_u\rvert\ll\lvert\Lambda_u\rvert$.

Step 3 handles every prefix correctly:
- zero bands are trailing, so any prefix has at most a fraction $1/(2J+3)$ of them;
- on a nonzero band, the multiplier $S$ with $\lvert S\rvert\le2J+2$ keeps points inside $(-b^{-L},b^{-L})$ and multiplies the inherited bias by $\operatorname{sgn}S$, so the prefix bias never grows;
- the incomplete cycle has weight $b^{-J^3}$.

**Theorem 6(1) is correct.** The [5c] experiment reproduces the predicted complete-period recursion $B\mapsto(2B+1)/(2k+3)$: $f_0=13/22=0.5909$, matched exactly.

**(iii) Theorem 6(2).**
- The choice of $t_s$ gives $1-\alpha\le f_s(t_s)<1-\alpha+1/(2s+3)$, so $1-f_s(t_s)\le\alpha$ and $D^+=\alpha$ follows by Lemma 4.1(3). This works for every real $\alpha$, rational or not, because $t_s$ is defined by a threshold.
- The λ-component stays uniform: $\gcd(\lvert S\rvert,D_{n_s})/D_{n_s}\le1/(2^sM_s)$, with the compounding of $\prod S$ handled by $M_s$.
- $D^-=0$ on the second reset shell.

All of this is sound. The simple normality claim along **all** $N$ is very likely true, by the argument outlined under M3, but the note does not prove it (M3).

### 3.7 Scope hygiene

- The status table uses the evidence labels from AGENTS.md correctly ("Paper proof", "Open"). It says no new Lean result is kernel-checked, and §7 separates finite measurements from the proofs. Required changes: the label for 6(2) (M3) and the wording of the check count (m11).
- No "the brief" or similar process wording appears in the note.
- **Benchmarks.** None of these results changes the status of any benchmark constant in `docs/benchmarks/`. The constructions are explicit synthetic products, and the note correctly leaves $1/E_b$ open (§8, item 4).

---

## 4. Verdicts

- **D1 (Theorems 1–3): accept after revision.** The mathematics of Theorems 1, 2, 3(1) and the admissible-family part of 3(2) is correct, and the script reproduces every displayed number. Required before acceptance: M1 (drop or prove the relaxed-family barrier) and M2 (drop "optimal"). Minor items m1, m4, m7, m9 and m11 are recommended.
- **D2 (Theorems 4–6): major revision for Theorem 6(2) only.**
  - Theorems 4 and 5 (including Proposition 4.4 across the ±1 shell boundaries) and Theorem 6(1) (including the hostile check of orientation and balance) are correct. Accept them with minor revisions: m2, m3, m5, m6, m10 and m16.
  - Theorem 6(2) needs the proof outlined in M3 written out, or the label "Paper proof (sketch)" until it is.
  - The §6 Lean blueprints must be repaired (M4) before any of them is formalised or counted as evidence.

*This is a cross-model review (Claude Opus 5.5 auditing a Gemini 4 Neon draft) and is not independent human peer review.*

---

## Post-Repair Verification

**Reviewer:** Claude Opus 5.5 (cross-provider re-audit of the Gemini 4 Neon repairs).
**Files re-read in full:** `notes/phase22/normal-reciprocals-and-signs.md`, now 925 lines; `scripts/phase22_reciprocals.py`, now 874 lines; and the Track D part of `NormalityChecker/RadixPowerTower.lean`, which the note cites as new kernel evidence.
**Scope warning:** This is a cross-model review. It is **not** independent human peer review.

### P1. Reproduction

- `python -B scripts/phase22_reciprocals.py` exits **0**. It reports `Total: 21443 checks passed in 1.49 s` (1.60 s wall time). §7 says 1.38 s; the difference is run-to-run timing noise.
- **Per-section counts match the table in §7 (lines 897–904) exactly:**

  | Section | Checks |
  |---|---|
  | 1 | 2,693 |
  | 2 | 14,326 |
  | 3 | 2,456 |
  | 4 | 92 |
  | 5 | 1,876 |
  | **Total** | **21,443** |

  Removing the old count of 72,027, which was inflated by trivial asserts, settles m11.
- **Every displayed number in the note agrees with the output.** I checked:
  - the table at line 276 and §7 item 2: 5.5841e-06 → 1.4130e-08 (395.2×) at $D_3^{\mathrm{bal}}=45(2^{36}-1)=3{,}092{,}376{,}453{,}075$, and 8.7251e-08 → 7.3533e-12 (11,865.6×);
  - the two values of $\tau$. I recomputed both from the factorisations: $1152=6\cdot3\cdot2^6$ and $1920$;
  - the 7×7 partial-band Weyl grid: worst ratio 0.8047 at $N=129{,}599$, $h=15$, with $\lvert W\rvert=0.3102$, new bound 0.3855 and Phase 21 bound 1.0522;
  - the Koksma line: $0.93071$, $0.00658\le0.01970$;
  - the new pure +1 sequence $m_k=2^kk!=(2,8,48,384,3840)$, giving $D=0.90161$ and $0.84827$ with $f_0=31/32$;
  - [4b] and [4c]: the sweep stays within 0.0081 of the prediction, inside the stated 0.015;
  - [4d]: $D$ decreases monotonically and stays within 0.067 of the asymptotic value, inside the stated 0.08;
  - [5a] through [5d], including $13/22$ and $B_{500}=0.000999$.

### P2. Independent checks after the repairs

1. **Lean.** In WSL (Lean v4.36.0, in the existing `~/phase20-build` tree), I ran `lake env lean` directly on the worktree file `NormalityChecker/RadixPowerTower.lean`. It elaborates with exit 0. The build-tree copy is byte-identical to the worktree file. `#print axioms` shows that `orderOf_mul_pow_sub_one`, `orderOf_mul_pow_add_one`, `orderOf_mul_pow_sub_one_of_orderOf` and `mul_pow_sub_one_dvd_pow_sub_one_iff` depend only on `[propext, Classical.choice, Quot.sound]`. The file contains no `sorry`. The signatures match the claims in §6: hypotheses $2\le b$, $1\le D$, $1\le m$ and $D\mid b^m-1$, with conclusions $mD$ and $2m$.
2. **New range claim.** $-2k\le S_i^{(k)}\le2k+2$, with both ends attained, holds for every $k\le60$ (my series construction).
3. **Bias closed form against recursion (5.5).** Exact `Fraction` arithmetic with $s=5$ and $j=1,\dots,8$ gives the following. The recursion $B^{(j)}=(2B^{(j-1)}+1)/(2k_j+3)$ equals $\sum_u\rho_u\prod_{v>u}(1-\rho_v)\,(s+u)!/(s+j)!$ for every $j$. It does **not** equal the note's printed $(s+u-1)!/(s+j-1)!$ for any $j\ge2$ (residual R1).

### P3. Major repairs

- **M1: repaired.** The relaxed Hull–Dobell claim is gone from the statement of Theorem 3(2), lines 55–59. Line 61 states it as open, §3.2 is now headed "Remark" (lines 369–375), and it appears as Open Problem 2 (line 921). The remark now names the exact point where the proof breaks: $S_i(b^{m_K})\bmod(b^{m_{K-1}}-1)\ne i+1$.
- **M2: repaired.** "Balanced-multiplier rate" is used in the Theorem 3 title (line 48), in part 1 (line 50), in the §3 heading (line 280) and in the status row (line 102). Line 61 states the gap of one iterated logarithm. Lines 330–334 are labelled "Heuristic comparison … not a proof of optimality". Open Problem 1 (line 920) asks the question.
- **M3: repaired.** I checked the new four-step proof in §5.4 (lines 679–805) line by line.
  - **Construction and $x\in K_b$** (lines 690–709). Every $Q_n$ has an explicit degree, term count and $\ell^1$ norm. The condition $m_n\ge b^{n^3}\widetilde T_{n-1}C_n^n(d_n+1)$ gives a support size and coefficient bound of $C_n\le m_n^{1/n}=N^{o(1)}$; the boundary case $N+w\ge m_{n+1}$ is handled. Choosing every $m_n$ as a multiple of $\widetilde T_{n-1}$ makes Theorem 1(1) and Lemma 5.2(1) apply at each level, and numerators are powers of $b$. **Correct.**
  - **Mixed-radix independence** (line 713). $m^{(v)}=Q_v\widetilde T^{(v-1)}$, $\widetilde T^{(v)}=L_vm^{(v)}$ and $\widetilde T^{(0)}=T_{n_0}$, so $(t_0,i_v,q_v)$ is a mixed-radix decomposition of $[0,\widetilde T^{(j)})$. The coordinates are therefore independent and exactly uniform. The densities of $E_2^{(j)}$ and $E_{u,d}^{(j)}$ are correct. **Correct.**
  - **$W_1$ bound on $E_2$** (lines 722–726). By Proposition 4.2(1), pushing a $D_{n_s}$-grid forward by $S_{\mathrm{tot}}$ with $\lvert S_{\mathrm{tot}}\rvert\le M_s$ gives discrepancy at most $1/(2^sM_s)$. If $q_v\le Q_v-2$, then $r_v<m^{(v)}-\widetilde T^{(v-1)}$. I re-derived the tail bound $6M_sb^{-T_{n_0}}$, using $\lvert\tau_i\rvert\le3q$ on nonzero bands. Summed over the round it is at most $b^{-2^s}$ because $T_{n_0}\ge D_{n_s}\ge2^sM_s^2$. **Correct.**
  - **Zero-band strata (5.3).** The two-sided bound $\tfrac38b^{r_u-dm}\le\lvert\Lambda\rvert\le\tfrac83M_sb^{r_u-dm}\le\tfrac12b^{-s-2}$ uses $L_s^*$. The bound on $E_{u,d}$ uses $\widetilde T^{(v-1)}\ge L_um^{(u)}>(4k_u+4)m^{(u)}+L_s^*$. The sign $\sigma_{u,j}$ is independent of $(r_u,d)$. **Correct**, apart from the factorial typo in (5.4) (R1).
  - **Bias recursion (5.5) and $0\le B^{(j)}\le3/(2s+3)$.** **Correct**; this is the true complete-period recursion, confirmed in P2.3.
  - **Step 2 (prefixes inside a shell)** (lines 746–754). Zero-band prefixes have proportion $\theta_j\le\rho_j$, and nonzero bands only flip the sign of the inherited bias. This gives $\lvert f_0-f_1\rvert\le B^{(j-1)}+\theta_j$, hence $\lvert f_0-\tfrac12\rvert\le2/(2s+3)+o(1)$. This is exactly the prefix argument M3 asked for. **Correct.**
  - **Step 3A (two-regime Fourier and Kronecker argument)** (lines 758–775). The cutoff $H_s\le2^{\lfloor s/2\rfloor}$ is now explicit, and $H_sM_s<D_{n_s}$. $D_{n_0}<b^{2m_{n_0}}$ holds because $m_{n_0}\ge T_{n_s}\gg\log_bD_{n_s}$. Then:
    - the tail is at most $1/(4D_{n_0}^4)$;
    - in Regime 1, Lemma D2.2 at the −1 level $n_0$ together with Lemma 2.1 gives at most $H_sM_s/(2^sM_s^2)\le2^{-s/2}$;
    - in Regime 2, $\|hS_{\mathrm{tot}}y_t\|\ge1/D_{n_0}$ because $\lvert hS_{\mathrm{tot}}\rvert<D_{n_0}$, and the Kronecker sum is at most $2/D_{n_0}$;
    - Erdős–Turán then gives $(1+\ln H_s)2^{-s/2}\to0$.

    **Correct.**
  - **Step 3B (melting fractions shifted by depth)** (lines 777–803). $\beta_{u,d}(I)=\operatorname{clip}((\log_bI-(d-1)m^{(u)})/m^{(u)})$ is the correct fraction for points of size about $b^{r_u-dm}$. The correlation between $\lvert\prod S\rvert$ and the sign is absorbed because $\Delta_u$ contains $\lceil\log_b16M_s\rceil$. The melted zone is controlled by the Kronecker sum, $\lvert\widehat\kappa\rvert\le2b^{-\Delta_u}$. The endpoints are right: $\gamma_K(m_K)=\alpha_s$, and $\gamma_K(m_{K+1})=0$ because $I\ge D_{K-1}\ge b^{(4k_{t_s}+2)m^{(t_s)}}$. The base-2 bias satisfies $0\le f_0-f_1\le B^{(t_s)}$ because every stratum bias is nonnegative. **Correct.**
  - **Edge set** (line 786). On the $1^-$ points, $\eta_r^{(K)}<\lvert x_t\rvert$ whenever $r<m_K-(4k_u+2)m^{(u)}-6$; this follows from $8b^{-6}<\tfrac14$. The excluded fraction is $O(b^{-K^3})$. **Correct.**
  - **Step 4, limit sets and irrationality** (line 805). $D^+=\lim\alpha_s=\alpha$, the limit set is $[0,\alpha]$ because $\gamma$ moves in steps of at most $1/(2s+3)$, and $D^-=0$. Irrationality follows because $D^-=0<D^+$ while every rational has convergent $D_N$. This argument holds for both $\alpha\in(0,1)$ and $\alpha=1$. For $\alpha=1$ (line 686), $t_s=s^2$ gives $\sum_{k=s}^{s+s^2-1}\frac1{2k+3}=\tfrac12\ln s+O(1)$, so $f_s(t_s)=O(s^{-1/2})$ and $\alpha_s\uparrow1$. **Correct.** Residual R2 is a typo in a range.

  **Verdict on Theorem 6(2):** the proof is now complete at the level of detail of the rest of the note. The label "Paper proof" (line 104) is justified.
- **M4: repaired.**
  - **`RadixPowerTower.lean` attributions** (lines 100 and 814). All five declarations named in §6 exist with the stated hypotheses and are kernel-checked; I verified this myself (P2.1). The scope is right: only the case $D\mid b^m-1$ of Theorem 1(1) is claimed, and the wider $\operatorname{rad}^*$ case is a separate blueprint, `orderOf_mul_pow_sub_one_radStar` (lines 825–830).
  - **`cyclotomic_band_identity`** (lines 851–868) is now nonvacuous. The tail is pinned to the explicit rational function `cyclotomicTail`, and $c_j=A_j-A_{j-1}$ reduced cyclically is correct because `hdeg` forces $A_{L-1}=0$. I checked that the statement is true: it is exactly Lemma 5.2(2), with `hcop` and `orderOf ∣ m` giving $\operatorname{den}R\mid b^m-1$.
  - **`cyclotomic_Pk_sign_counts`** (lines 870–880) now states the actual positive count, negative count and trailing-zero characterisation of $A$ in terms of `hPA`.

### P4. Minor repairs

| Item | Status | Evidence |
|---|---|---|
| m1 | Resolved | Line 218: threshold $D\ge e^{e^5}$; I checked $P=e^5/125=1.19>1$. |
| m2 | Resolved | Line 604: complete argument for $s_n\in[-k,k+1]$ and $t_n\in[-2k,2k+2]$; I verified it for $k\le60$. |
| m3 | Resolved | Line 621: coprimality hypothesis and $P_k(b^m)\equiv1\pmod{\operatorname{den}R}$. |
| m4 | Resolved | Line 367: "$-O(1)$". |
| m5 | Resolved | Lines 550–554: mechanism stated, balance described as asymptotic. |
| m6 | Resolved | Line 677: irrationality argued. |
| m7 | Resolved | Line 276: balanced $D_3^{\mathrm{bal}}$ added; omission of the $c_b$ term stated. |
| m8 | Resolved | Headings at lines 110, 180, 280, 379 and 548, and the §7 items, carry no track labels. No "the brief" wording. |
| m9 | Resolved in the note | Residual R6 concerns the Lean docstrings. |
| m10 | Resolved | Line 523. |
| m11 | Resolved | Lines 895–904 and 914. |
| m12 | Resolved | Line 911 and script lines 618–635: an honest "illustration" with real monotonicity and 0.08 checks. |
| m13 | Resolved | No working-note comments, no stale values, no dead variables. The Theorem 4(2) example $m_k=2^kk!$ matches the script. |
| m14 | Resolved | `shifted_grid_interval_excess_le`; the omega/nlinarith remark is removed. |
| m15 | Resolved | Line 695: $(d_n,\#Q_n,\|Q_n\|_1)$ defined for every $n$. |
| m16 | Resolved | Line 72 and line 535. |

### P5. Residual issues (all minor, none blocking)

- **R1. Factorial index off by one** (line 738 in (5.4), the definition of $B^{(j)}$ at line 740, and line 800). Since $k_v=s+v-1$, $\prod_{v=u+1}^j\frac1{k_v+1}=\frac{(s+u)!}{(s+j)!}$, not $\frac{(s+u-1)!}{(s+j-1)!}$. P2.3 confirms that the printed closed form does not satisfy (5.5) for $j\ge2$; the corrected one does. Every bound in the proof comes from (5.5), so no conclusion changes. *Fix:* replace the expression at all three places.
- **R2. Wrong range in Step 4** (line 805). "$D_N\to0$ … uniformly across $[m_{n_{s+1}+1},m_{n_{s+2}}]$" should be the single second-reset shell $[m_{n_{s+1}+1},m_{n_{s+1}+2}]$. The cyclotomic shells of round $s+1$ are covered by Step 2, not by Theorem 2.
- **R3. Overstatement in the $\alpha=0$ case** (line 681). "Simply normal in every base including $b=2$" is not implied: normality in base $b$ gives normality in the bases $b^j$, not simple normality in base 2 when $b$ is not a power of 2. *Fix:* "normal, hence simply normal, in base $b$, so in base 2 when $b=2$." The theorem itself (line 96) claims base-2 simple normality only for $b=2$, so it is unaffected.
- **R4. Constant slip** (line 785). From $I\le b\cdot b^{\lfloor\log_bI\rfloor}$ one gets $I\lvert x_t\rvert\le\tfrac b4b^{-\sqrt{m^{(u)}}}$, not $\le b^{-\sqrt{m^{(u)}}}$. This is harmless: add 1 to $\Delta_u$.
- **R5. Notation clash** (line 711 against lines 690–707). $Q_v$ means both the ratio $m^{(v)}/\widetilde T^{(v-1)}$ and the polynomial factor $Q_n$. Separately, $L_j$ is indexed by position within the round at line 693 but globally in $\widetilde T_n=L_nm_n$ at line 701. Rename the ratio, for example to $\kappa_v$.
- **R6. Lean integration and hygiene.**
  - `NormalityChecker/RadixPowerTower.lean` is untracked, and neither `NormalityChecker.lean` nor `Audit.lean` imports it. A default `lake build`, and the README theorem-index script, will not check or list these declarations. I verified the kernel claim by elaborating the file directly.
  - *Fix:* add `public import NormalityChecker.RadixPowerTower` to the root, run `lake build` and refresh the theorem index (AGENTS.md).
  - Its Track D docstrings still say "with ZERO exceptions" and carry the labels "Track D1–D2" and "Track G1 Correction A". m8 and m9 already fixed these in the note.
  - Status row at line 100: say "order identities", since the $S_i$-bijection part of Theorem 1(1) is not formalised.

### P6. Final verdicts

- **D1 (Theorems 1–3): ACCEPT.** M1 and M2 are fully repaired. The order identities of Theorem 1 for $D\mid b^m-1$ and for the plus sign are now independently confirmed as kernel-verified. The mathematics of Theorems 2 and 3 was already correct and is unchanged. Only R6 (Lean import and docstring hygiene) remains, and it does not block acceptance.
- **D2 (Theorems 4–6): ACCEPT.** The new four-step proof of Theorem 6(2) is complete and correct. It covers mixed-radix independence, the $W_1$ bound on $E_2$, the bias recursion, prefix control inside each shell, the two-regime Fourier and Kronecker argument with an explicit cutoff $H_s$, melting fractions shifted by depth, the edge set for $\eta^{(K)}$, and irrationality for both $\alpha\in(0,1)$ and $\alpha=1$. The §6 blueprints are now nonvacuous and correctly stated. The residual items R1–R5 are typos or wording issues that change no conclusion. They should be fixed before merge, but they do not block acceptance.
- **Benchmarks.** No status changes for `docs/benchmarks/`; these are synthetic constructions, and $1/E_b$ remains open (Open Problem 6, line 925).

*This post-repair verification is a cross-model review (Claude Opus 5.5 auditing a Gemini 4 Neon draft and its repairs). It is not independent human peer review, and on its own it does not establish any evidence label.*
