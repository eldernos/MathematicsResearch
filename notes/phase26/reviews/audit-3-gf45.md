# Phase 26 Stage 0.2 — Independent Deep Analytic Audit III (`GF-45`)

**Audited targets** (worktree at `c06c97d`, branch `research/phase-26-arithmetic-amplification`):
- [`notes/phase25/partitions-and-reciprocals.md`](../../phase25/partitions-and-reciprocals.md) (290 lines, blob `db54a4e`, identical to `HEAD`)
- [`scripts/phase25_partitions_reciprocals.py`](../../../scripts/phase25_partitions_reciprocals.py) (353 lines, blob `4a5b344`, identical to `HEAD`)
- [`docs/registry/GF.toml`](../../../docs/registry/GF.toml), entry `GF-45` (line 816 onward). Both the committed `HEAD` text and the uncommitted working-tree revision were read; see Minor m3.
- Read for context only: [`notes/phase25/reviews/track-e-review.md`](../../phase25/reviews/track-e-review.md). Every step below was reconstructed independently before that review was compared.
- Checked at statement level: GF-34 Theorems 1 and 5 ([`convergent-reciprocals-and-schedules.md`](../../phase23/convergent-reciprocals-and-schedules.md)), GF-32 Lemma 5.3 ([`binary-partition-and-carry-complexity.md`](../../phase23/binary-partition-and-carry-complexity.md), line 407), and GF-38 C1.4 ([`partitions-and-reciprocal-spectra.md`](../../phase24/partitions-and-reciprocal-spectra.md)).

> **Cross-model review is not independent human peer review.** This report is a machine audit by one AI model of work drafted by other AI models. It does not replace refereeing by human specialists in uniform distribution and digit expansions. Its conclusions cannot change any benchmark status on their own.

---

## Verdict: **VALIDATED. GF-45 passes the gate for Proposed Paper XV, subject to the listed non-blocking repairs**

| Severity | Count |
|---|---:|
| **Critical** | 0 |
| **Major** | 0 |
| **Minor** | 9 |

I reconstructed the all-radix theorem $\mathcal A_{\rm conv}(b)=[0,1]$ (Theorem E1.2 with its endpoints) independently. I found no mathematical gap in any of the following:

- the cut-and-fold identities;
- coprime-period preservation, which depends on no property of the radix;
- independence in the convolution;
- the Fourier recursion near the repelling fixed point $z=1$;
- the transform $W=1/(1-z)$;
- convergence along every prefix, including transitions between operations;
- discrepancy convergence despite the atom at $0$;
- irrationality, the inclusion $M_b\subset K_b$, the endpoints, and computability.

E1 (the dyadic route), E2.1–E2.3, E3 and E4 also survived reconstruction. The certificate script exits 0 on Windows. Seven independent adversarial test suites, run in bases $3,6,7,10,12$, found no counterexample to any claimed identity, invariant or bound.

All nine Minor findings concern statement accuracy, the registry fields or manuscript-level explicitness. None is a hole in a proof. Section 7 lists which repairs should precede drafting of Paper XV.

---

## 1. Independent reconstruction of Theorem E1.2 (every radix $b\ge2$)

### 1.1 Exact cut-and-fold identities (note lines 101–116)

Let $C,F>0$ satisfy $CF=1$, with eventual base-$b$ periods $P_C,P_F$, $\gcd(P_C,P_F)=1$, and common preperiod bound $a$. Choose $P_C\mid m$, $P_F\mid d$, $\gcd(m,d)=1$ and $m>d+a$, and put $q=m+d$. Then

```math
F\,\frac{1-b^{-q}}{1-b^{-m}}=F+\frac{F(b^{-m}-b^{-q})}{1-b^{-m}}=F+\frac{w}{b^m-1},\qquad w=F(1-b^{-d}).
```

The update multiplies the pair by mutually inverse factors, so $C'F'=1$ holds exactly. Three integrality facts follow:

- $b^{a+d}w=b^a(b^d-1)F\in\mathbb Z$, because $P_F\mid d$.
- $b^a(b^q-1)C'=b^{a+d}(b^m-1)C\in\mathbb Z$, because $P_C\mid m$. So $C'$ has preperiod at most $a$ and period dividing $q$.
- In $F'=F+w/(b^m-1)$ the prime-to-$b$ denominators combine by $\operatorname{lcm}$, not by product. So $F'$ has preperiod at most $a+d$ and period dividing $\operatorname{lcm}(m,P_F)=mP_F$. The lcm equals the product because $\gcd(m,P_F)=1$.

**Verified.** Neither the script nor my tests found any discrepancy in these identities.

### 1.2 Coprime periods at every stage and in every radix (lines 108, 116)

$\gcd(q,m)=\gcd(d,m)=1$. Also $\gcd(q,P_F)=\gcd(m,P_F)=1$ because $P_F\mid d$. Hence $\gcd(q,mP_F)=1$, and so the actual new periods, which divide $q$ and $mP_F$, are coprime.

Next take $L\ge2$ coprime to $P_C$, $d=(LP_F)^k$ and $m=P_C(1+jLP_F)$. Then $\gcd(m,d)=1$, using only $\gcd(P_C,L)=\gcd(P_C,P_F)=1$. Since the spacing of admissible $m$ divided by $d$ tends to $0$, $\rho=d/m\to r$ as $k\to\infty$.

The argument uses only lcm/gcd arithmetic on exponents. It never needs $2\in\langle b\rangle\pmod D$, so the Bugeaud–Corvaja–Zannier gcd obstruction (GF-38 C1.4) does not arise. Test A confirms that the actual periods attain the bounds exactly in bases 3, 6, 7 and 10:

- step 1: periods $80=q$ and $73=m$;
- step 2: periods $883=q$ and $64240=mP_F$;
- step 3: periods $65123=q$ and $56{,}723{,}920=mP_F$.

In every case the gcd is 1.

### 1.3 Cycle comparison and independence (lines 118–133)

**Cut side.** At $n=iq+r$, earlier summands are integral once $d+r\ge a$. On $a\le r<m-H$ the point tracks $b^rC$. On $m+a\le r<q-H$ it tracks $0$. In both cases the error is $O(Cb^{-H})$. The resulting law is $\frac1{1+\rho}\sigma+\frac{\rho}{1+\rho}\delta_0$.

**Folded side.** For $i\ge1$ the point at time $n=im+s$ tracks

- $b^{im+s}F+b^sF$ on $a\le s<d-H$;
- $b^{im+s}F$ on $d+a\le s<m-H$;

and block $0$ tracks the old orbit. The independence claim rests on a bijection. Take $i$ over $P_F$ consecutive values and $s$ over a run whose length is a multiple of $P_F$. Then the map

```math
(i,s)\longmapsto\bigl((im+s)\bmod P_F,\ s\bmod P_F\bigr)
```

covers $\mathbb Z_{P_F}^2$ uniformly, because $\gcd(m,P_F)=1$. So the pairs are exactly uniform on cycle × cycle, and the law is $(1-\rho)\mu+\rho\,\mu*\mu$. The script's `pair_counts` check and my Test A, which uses nontrivial $P_F$ in bases 3, 6, 7 and 10, confirm exact uniformity.

The exceptional mass is $O((a+H+P)/m)$. This tends to $0$ because $m$ is chosen after $P_C,P_F$ are fixed (see m4).

### 1.4 The comparison on every prefix (lines 125, 133)

For any $N\ge m$, the discarded fraction on the folded side is at most

```math
\frac{a+P_F}{N}+\Bigl(1+\frac Nm\Bigr)\frac{d+a+H}{N}\ \le\ 2\rho+O\Bigl(\frac{a+H+P_F}{m}\Bigr).
```

On the cut side the zero pieces occupy at most $(N-m)/N\le d/q$ of the prefix for $m\le N<q$, and at most $2\rho$ for all $N\ge q$. So each prefix law is within $O(\rho)+o(1)$ of the old cycle, and the constant in $O(\rho)$ is absolute. **Verified.**

Test B checks every $N\in[803,3539)$ of an actual second operation with $\rho=0.0996$, including every mid-block $N$. The largest deviations are:

| Quantity | $b=3$ | $b=6$ | $b=10$ | $b=7$ |
|---|---:|---:|---:|---:|
| $\lvert D_N(y)-D_{\rm old}\rvert$ (folded) | 0.0077 | 0.0046 | 0.0024 | 0.0046 |
| $\lvert D_N(x)-D_{\rm old}\rvert$ (cut) | 0.0129 | 0.0087 | 0.0044 | 0.0087 |
| $\lvert M_N(x)-M_{\rm old}\rvert$ | 0.0021 | 0.0009 | 0.0005 | 0.0007 |

All of these are far below $2\rho=0.199$.

### 1.5 Mean contraction for $x$ (lines 137–144)

Circle distance is subadditive, so the convolution at most doubles the mean. Combining the two comparisons gives

```math
B_{j+1}\le\frac{1+\rho_A}{1+\rho_B}B_j+O(h_j^2)=\bigl(1-(1-\alpha)h_j+O(h_j^2)\bigr)B_j+O(h_j^2).
```

Since $\sum h_j=\infty$ and $\sum h_j^2<\infty$, $B_j\to0$. The intermediate means $\le(1+\rho_A)B_j+h_j^2$ also tend to $0$. **Verified.**

### 1.6 Fourier dynamics and the repelling fixed point $z=1$ (lines 146–159)

The map factors exactly as $1-T(z)=(1-c)(1-z)(1+hz_A)$; the script checks this identity on rationals. At $z=1$ the multiplier is

```math
(1-c)(1+h)=1+(1-\alpha)h_j+O(h_j^2)>1,
```

so $z=1$ is weakly repelling, and a slight blow-up of $1/(1-z)$ near it is a genuine risk. The note controls this risk correctly.

**Precision is relative.** Each comparison error is chosen at most $h_j^2|1-z|^2/100$, after $z$ is known. This is feasible: in any cycle whose reduced prime-to-$b$ denominator $D$ does not divide $k$, every point has $kt\notin\mathbb Z$, so $1-\Re z\ge8/D^2\ge8/(PD^2)$. This is decidable.

**Activation.** The denominator of the new $y$ is required to exceed $j$. Write $y=A/(b^aB)$. The cut cancels at most $A(b^m-1)$ from $b^q-1$, so the remaining denominator grows at least like $b^d/A$. Hence $\tilde z_A\ne1$ for all $k\le j$.

**Preservation.** $|1+h\tilde z_A|\ge1-h$, so the fold keeps $z\ne1$.

Test E stresses the recursion with adversarial errors of the maximal allowed size, pointed toward $1$:

- From $|1-z|=10^{-8}$ or $10^{-12}$ the iteration never reaches $1$. Over $10^6$ rounds $|1-z|$ grows by the predicted factor of about $(j/9)^{1-\alpha}$.
- With absolute errors of size $h_j^2/100$ instead, the iteration is absorbed at $z=1$ from $|1-z|=10^{-3}$ and from $10^{-5}$.

So the relative precision rule is necessary, and the note imposes it.

### 1.7 The transform $W=1/(1-z)$ (lines 161–168)

I re-derived $W_{\rm next}=(1-(1-\alpha)h_j)W+h_j+O(h_j^2(1+|W|))$. The key step uses $z_AW=W-(1-c)$, which gives

```math
\frac{(1+\rho_A)W}{1+hz_A}=(1-h+\rho_A)W+h+O\bigl(hc+h^2|W|\bigr).
```

The $O(h_j^2)$ remainder from replacing $1/(1-T(z))$ by $1/(1-z_{\rm next})$ is uniform in $k$. Both denominators are $\ge|1-z|/3$ once $j\ge j_0$, where $j_0$ does not depend on $k$, and each frequency $k$ enters the recursion from round $k+1$.

Taking absolute values bounds $|W|$. Subtracting the fixed point $1/(1-\alpha)$ leaves a contraction with summable error, so $z\to\alpha$ for every $k\ge1$. Test E reproduces the predicted contraction ratio of $|W-W^*|$, about $(9/(R+8))^{1-\alpha}$ after $R=10^6$ rounds, from the starts $0.3+0.4i$, $-1$ and $i$, for $\alpha\in\{0,1/\sqrt2,0.95\}$.

### 1.8 The real limit along every prefix, including block transitions (line 170)

Successive ratios exceed 2, and each factor moves a coordinate by $O(b^{-m_i})$. Both infinite products are therefore bounded above and away from $0$, and $|x-x^{(i)}|\le Cb^{-m_{i+1}}$.

Take $m_i\le N<m_{i+1}$ and drop the final $\lceil\sqrt N\rceil$ times. The remaining orbit points track $x^{(i)}$ to within $O(b^{-\sqrt N})$, and §1.4 applies to $x^{(i)}$ for every $N\ge m_i$. Since $q_i<\tfrac43m_i<m_{i+1}$, the whole first $q$-block of operation $i$ lies inside its own window. No prefix escapes the comparison, and the old cycle laws converge (to $\mu_\alpha$ for $y$; their means tend to $0$ for $x$). So $\nu_N(y)\Rightarrow\mu_\alpha$ and $M_N(x)\to0$ along all $N$.

Test C uses the exact rational after three operations, with $m=(73,803,64240)$, as a proxy for the limit and scans $N$ across both transitions. The largest values of $|D_N(y)-D(\text{old cycle})|$ in each operation window are:

| Window | $\rho$ | $b=3$ | $b=6$ | $b=10$ |
|---|---:|---:|---:|---:|
| Operation 1 | 0.096 | 0.102 | 0.060 | 0.045 |
| Operation 2 | 0.0996 | 0.0077 | 0.0050 | 0.0027 |
| Operation 3 | 0.0137 | 0.0012 | 0.0008 | 0.0004 |

There are no spikes at the transitions. The largest window-1 value, at $N\approx800$, lies inside $O(\rho)+O((a+H)/m)$ at the tiny scale $m=73$, and the test did not drop the final $\sqrt N$ points.

### 1.9 Discrepancy despite the atom (line 172)

$D(\mu_\alpha)=\sup_I\alpha|\mathbf 1_{0\in I}-|I||=\alpha$; this supremum is not attained. The lower bound uses the continuity arc $(-\varepsilon,\varepsilon)$. The upper bound uses a partition into arcs of length $\le\varepsilon$ whose endpoints avoid $0$, within-arc matching, and the comparison $|D(\nu_1)-D(\nu_2)|\le2h+s$, which I re-proved with the $h+\varepsilon$ enlargement. This argument is valid for half-open arcs whatever the side from which the orbit approaches $0$.

Test D confirms the convention matters. Take discrete measures with atom mass $\alpha$ placed above $0$, below $1$, or split. Their arc discrepancy $D\to\alpha$ in every case. The star discrepancy $D^*$, by contrast, takes the values $\alpha$, $\alpha$ and $\alpha/2$, and $\nu([0,0.01))$ ranges from $0.003$ to $0.703$.

So only extreme (arc) discrepancy and continuity sets give limits here. The note uses exactly these. It correctly claims only *lower* frequencies for the words $0^L$ and $(b-1)^L$, and exact frequency $(1-\alpha)b^{-L}$ for cylinders whose closure misses $0$.

### 1.10 Irrationality, membership, scope and computability

- **Irrationality.** The Lebesgue component excludes eventual periodicity of $y$, so $x=1/y$ is irrational.
- **Membership.** $M_N(x)\to0$ gives $x\in M_b$. Markov's inequality on the complement of a short arc gives $M_b\subset K_b$.
- **Scope.** The witness depends on the radix $b$. Nothing in the proof, or in the working-tree registry text, asserts a single witness across radices.
- **Computability.** For computable $\alpha$ every choice can be decided with rational arithmetic: the ratios are found to precision $h_j^2$, the coupling errors have explicit geometric and counting bounds, $D\nmid k$ is decidable, and $|1-z|\ge8/D^2$. The geometric tails give a modulus of convergence for $x$. For non-computable $\alpha$ only existence follows.

### 1.11 Endpoints (line 174; E1 line 93)

- **$\alpha=0$.** Take $\rho_A\in(h_j^2/2,h_j^2)$. It stays positive, so harmonic activation still works. Both recursions are unchanged, giving $B_j\to0$ and $W\to1$, so $y$ is normal in base $b$. GF-34 Theorem 5 supplies the same endpoint independently, with a rate; its statement matches this use.
- **$\alpha=1$.** Apply GF-34 Theorem 1 with $r=A/D=1$. The hypothesis $2\in\langle b\rangle\pmod1$ is vacuous and $P=1$. The theorem gives an irrational $x\in M_b$ whose reciprocal has orbit law $\to\delta_0$, so $D_N\to1$. The alternative route, the E1 contraction with radix $b$ from integers, is also self-contained:
  - Both band identities hold verbatim in radix $b$: $b^{l+r}u^+=b^r(b^l-1)u+b^ru/(b^l+1)$.
  - The $v$-cycle stays $\{0\}$.
  - Irrationality follows from $b^{-l_{j+1}}\operatorname{den}(v_j)<1/j^2$.

### 1.12 Effectivity

No rate is claimed ("without requiring a convergence rate"), and none is available from this schedule. Two effects compound:

1. The periods multiply. Test A shows $P_{F'}=mP_F$ is attained, so $m_{i+1}\ge P_C$ forces at least doubly exponential growth of the scales.
2. From the near-$\delta_0$ seed, harmonic $k$ needs about $(1-\alpha)/|1-z_{\rm act}|$ raised to the power $1/(1-\alpha)$ rounds to leave the neighbourhood of $z=1$.

Convergence $D_N\to\alpha$ is therefore real but ineffective in $N$, and astronomically slow. See m6.

---

## 2. Theorem E1 (dyadic route, lines 21–95)

I re-checked the following:

- The CRT choice of $p$, with $q\equiv1\pmod e$ so that $\gcd(P_{v'},e)=1$ persists.
- The exact identity $u'-u=w/(2^p-1)$ and the integrality of $2^{a+d}w$.
- That the contraction reproduces the cycle exactly: $2^nv^+\equiv2^{n+1}v$ for $n\ge l+a$. Because the period is coprime to $e$, every residue progression sees the same law.
- The bands of $u^+$, with denominator dividing $2^{2l}-1$, and the halving of the mean.
- The steering invariant $D_{j+1}\le D_j+3t_j<\alpha$. Combined with $L_{j+1}\le(1-\theta_j)L_j+2^{-j}t_j$, this rules out $\sum t_j=\infty$ (otherwise $D_j\to1$), so $t_j\to0$ and $\alpha-D_j<16t_j\to0$.
- The irrationality argument through $2^{-l}\operatorname{den}(v)<1/j^2$.
- The de Bruijn seed.

**Verified.** The earlier m1 repair ($2a+H$ strips) is present at line 63.

## 3. E2.1–E2.3 (incomplete-orbit cancellation, lines 176–214)

**E2.1.** I re-derived the valuation inequalities $v_p(\operatorname{ord}_{Q'}b)\le t$, $E\ge kc+t$ and $g\le v_p(b^2-1)+t$, including $p=2$ with $b\equiv3\pmod4$ and $t\in\{0,\ge1\}$. I also re-derived the CRT grid of spacing $Q'p^{g}$, which unit multiples preserve. Then $R-R_k\le C_bb^{-m_{k+1}}$ gives $D^-(R;b)=0$ under the stated hypothesis.

**E2.2.** The first $\min(N,L-h)$ points lie in $[0,b^{-h-1}]$. The start with numerator 1 occurs at time $-S_k\bmod T_k$.

**E2.3.** The grid Fourier coefficients vanish unless $J\mid i-j$. The mean square equals $1/N$ exactly for $N\le J$ and is at most $1/N+1/J$ in general. For fixed $a$, $J\to\infty$. The compactness step uses the arc partition.

**Verified.** Test F repeats the checks in non-dyadic radices: $b=6$ ($p=5$), $10$ ($p=3$), $7$ ($p=2$, so $b\equiv3\pmod4$), $7$ ($p=3$) and $12$ ($p=11$). It covers harmonics $a\in\{1,-3,p\}$ and evaluates the complex mean square directly. All assertions pass. The `Conditional` paragraph is labelled correctly.

## 4. E3 and E4 (transition lower bounds, lines 216–269)

**Separation lemma.** Because $\gcd(A,b)=1$ and $A>b-1$, the number $(b-1)b^{n+s}/A$ is not an integer. The factor $b^{-s}$ cancels exactly in the error term. A constant run of length $h$ then forces $h\le\log_bA+O(1)\le s+O(1)$. The exact multiplication rule $\|by\|=b\|y\|$ for $\|y\|<1/(2b)$ gives an escape from $F_b$ within $s+O(1)$ steps.

**E3.** The gap is $g=m^k-s=(m-2)s+1$; I checked it algebraically. Since $s_k=ms_{k-1}+1$, runs are at most $\frac m{m-2}n+O(1)$. Geometric windows give $\gg\log N$ transitions and escapes. GF-32 Lemma 5.3, whose statement matches its use, then gives $1-D_N\gg(\log N)/N$. The signed recurrence $b^{M-s}(AX-b^s)=1+O_b(b^{-M})$ holds because $m\ge3$.

**E4.** The pentagonal truncation through $s=i(3i+1)/2$ has numerator $\equiv(-1)^i\pmod b$, and the next exponent is $s+2i+1$, which I re-computed. This gives runs at most $\frac38n^2+O(n)$ and $\gg\log\log N$ transitions. For the rational $R_k^{(E)}$, the Lipschitz transfer at $N=k$ loses only $P_b/(b-1)^2$. Transitions for $R_k^{(E)}$ are explicitly *not* claimed in the note (see m2).

**Verified.** Test G uses certified digit intervals:

- Over $n<500$, $\max\,[\text{run after }n-\frac{mn}{m-2}]$ is at most 3 for $X_{b,m}$ with $b\in\{3,6,10\}$ and $m\in\{3,4\}$.
- Over $n<60$, $\max\,[\text{run}-\frac38n^2]$ equals 1 for $P_b$ with $b\in\{3,6,10\}$.
- Transition counts in 2000 digits are 1326, 1660 and 1816 for $P_3$, $P_6$ and $P_{10}$. These are finite measurements only and establish no density.

---

## 5. Computational verification

**Repository certificate.** `python -B scripts/phase25_partitions_reciprocals.py` exits 0 on Windows (Python 3.13.13, about 5 s). It prints exactly the counts quoted in note line 279: 15 pads, 936 band positions, 15 coprime updates, 16 product denominators, 152 separation instances and 16 Euler windows, plus the finite measurements 131, 138, 146 and 111. The script contains no floating-point operations (checked by grep).

The note states which E4 windows have a positive bound. I confirmed it:

| Window $(b,k)$ | $\tfrac25\,\text{lower}/k-1/k$ |
|---|---:|
| $(2,64)$ | 0.0049 |
| $(2,128)$ | 0.0236 |
| $(3,64)$ | 0.0045 |
| $(3,128)$ | 0.0132 |
| $(5,128)$ | $\approx-10^{-5}$ |

All other windows are negative, so those assertions are vacuous (see m8). I did not rerun the script on Hail, per this task's instructions.

**Independent adversarial suites.** These are scratch files outside the repository, run with `python -B`. Floats appear only in diagnostics, never in assertions about exact identities.

| Suite | Content | Result |
|---|---|---|
| A | Three cut-and-fold operations in $b=3,6,7,10$: exact identities, actual periods and preperiods, coprimality, exact pair uniformity, Fourier deviation of the actual cycle from the ideal mixtures | All assertions pass; the periods attain the bounds exactly |
| B | Every $N\in[803,3539)$ (mid-block included) for the second operation | Maximum deviation $\le0.013\ll2\rho$ |
| C | Scan across operation boundaries, with $N$ windows at $m_3/2$, $m_3$, $q_3$ and $2m_3$ | No transition spikes beyond $O(\rho)$ |
| D | Atom above, below or split | Arc discrepancy $\to\alpha$; $D^*$ and $\nu([0,\delta))$ do not converge to the $\mu_\alpha$ values |
| E | Fourier/$W$ recursion with maximal adversarial relative errors; absolute-error control | Converges at the predicted rate and never reaches $z=1$; absolute errors are absorbed at $z=1$ |
| F | E2.1–E2.3 in $b=6,7,10,12$ | All pass |
| G | E3/E4 run and escape bounds from certified digits | All pass with constants $\le3$ |

---

## 6. Classified findings

### Critical
None.

### Major
None.

### Minor

1. **m1 — The registry `inputs` field does not follow the schema.** ([`GF.toml`](../../../docs/registry/GF.toml), `GF-45` `inputs`; [`SCHEMA.md`](../../../docs/registry/SCHEMA.md) line 33)
   - *Issue:* The schema defines `inputs` as the external theorems used on paper, with their sources. The entry instead lists internal results and "elementary Weyl/Erdős–Turán estimates". Erdős–Turán is not used: E2.3 uses compactness plus the arc partition. The entry omits Euler's pentagonal number theorem (Andrews, *The Theory of Partitions*, Ch. 1), which the note's evidence table labels `External input`. It also omits Stone–Weierstrass on $\mathbb T$, Portmanteau for continuity sets, and weak\* compactness. The internal GF-32 Lemma 5.3 appears only under `related`.
   - *Fix:* List the classical external inputs with sources. Remove "Weyl/Erdős–Turán". Leave the internal results in `related` or the prose.

2. **m2 — Registry statement (3) is ambiguous for $R_k^{(E)}$.**
   - *Issue:* "P_b = 1/E_b and its partial products R_k^{(E)} satisfy ≫ log log N transitions and 1 − D_k(R_k^{(E)}; b) ≫ …" can be read as claiming digit transitions for $R_k^{(E)}$. Note line 267 deliberately proves only a distance and discrepancy transfer at $N=k$: equality of digits would require cylinder-boundary margins.
   - *Fix:* Rewrite as "P_b has ≫ log log N transitions and 1 − D_N(P_b; b) ≫ (log log N)/N; on the actual initial orbit of R_k^{(E)}, 1 − D_k ≫ (log log k)/k".

3. **m3 — Scope wording differs between `HEAD` and the working tree.**
   - *Issue:* At `c06c97d` the committed statement says every α "is realized by an **explicit** irrational x". That overclaims for non-computable α. The uncommitted working-tree revision corrects it: "there exists … x(b, α) … computably whenever α is computable; parameter-dependent existence …; not … simultaneously across multiple radices". Note line 3 still says "1/√2 occurs exactly in every radix", which can be misread as one witness for all radices.
   - *Fix:* Commit the working-tree registry text. Change note line 3 to "1/√2 ∈ 𝒜_conv(b) for every b (with a b-dependent witness)".

4. **m4 — The cut-and-fold comparison should be a standalone lemma in Paper XV.** (lines 118–133, 53)
   - *Issue:* The cut-side cycle and prefix estimates for E1.2 are imported by cross-reference ("the padding proof with radix b, p = m, and e = 1") from the binary E1 text with residue progressions. The asymptotic regime is left implicit: $P_C/m\to0$ makes the per-fragment trimming term $O(P)$ negligible. It is guaranteed because $m$ is chosen after $P_C,P_F$ are fixed, with $k\to\infty$.
   - *Fix:* In the manuscript, state one Cut-and-Fold Comparison Lemma for radix $b$. Give explicit displacement $O(Fb^{-H})$ and exceptional mass $O((a+H+P)/m)$ for the cycle, and $\le2\rho+O((a+H+P)/m)$ for every $N\ge m$. State the order of choices: $H$, then $m$, with $P/m\to0$.

5. **m5 — The computability constants are only implicit.** (lines 159, 172)
   - *Issue:* "The rational error bounds above" relies on $O$-constants. The decision procedure ($z\ne1\iff D\nmid k$) and the sharper lower bound $1-\Re z\ge8/D^2$ (valid when $D\nmid k$) are correct but scattered.
   - *Fix:* Give one explicit algorithmic paragraph listing each selection with a computable bound, and state the modulus $|x-x^{(i)}|\le Cb^{-m_{i+1}}$ explicitly.

6. **m6 — The construction is ineffective; this should be said.** (§1.12)
   - *Issue:* No rate is claimed, correctly. A reader could still overestimate the construction. Period multiplication forces at least doubly exponential scales, and escape from the neighbourhood of $z=1$ can take many rounds. No finite digit statistics of a witness can ever corroborate the limit.
   - *Fix:* Add a remark that the theorem is qualitative, that rates are known only at $\alpha=0$ (GF-34 Theorem 5), and that a quantitative spectrum (prescribed $\alpha$ with an explicit rate) remains open.

7. **m7 — Editorial slips.**
   - Line 170: "At binary or general radix scale" should read "At radix-$b$ scale $s_i=m_i$ (operation $i$)".
   - Line 93: "all-base normal reciprocal construction" should read "base-by-base normal reciprocal construction"; GF-34 Theorem 5 is per base, not absolute normality.
   - Line 174: "its Theorem 1" should read "GF-34 Theorem 1 with $r=1$".

8. **m8 — A certificate claim is not enforced by the script.** (script lines 333–344; note line 279)
   - *Issue:* The note states the E4 bound is strictly positive on the four windows $(2,64)$, $(2,128)$, $(3,64)$, $(3,128)$. I confirmed this, but the script never asserts it. The phrase "remaining 12 smaller windows" is also inaccurate: the $b=5,10$ windows at $k=64,128$ are not smaller.
   - *Fix:* Add `assert rhs > 0` for those four windows. Reword as "the remaining 12 windows (all b = 5, 10 windows and k = 16, 32 for b = 2, 3)".

9. **m9 — The BF-10 benchmark summary places GF-45 inside the product family.** ([`arithmetic-families.toml`](../../../docs/benchmarks/arithmetic-families.toml) line 189)
   - *Issue:* BF-10 is the family $1/\prod(1+\varepsilon_kb^{-m_k})$. GF-45's witnesses are built from ratios $(1-b^{-m})/(1-b^{-q})$ and lie outside that family. The summary does not claim otherwise, and no status changed. A reader could still infer that the family itself attains every α, which note Open 1 lists as open.
   - *Fix:* Add the clause "GF-45 witnesses lie outside the BF-10 product family; attainment within the family at intermediate α remains open".

---

## 7. Gate decision for Proposed Paper XV

**GF-45 PASSES the analytic gate for Proposed Paper XV.** No Critical or Major gap remains. The theorem $\mathcal A_{\rm conv}(b)=[0,1]$ holds for every integer $b\ge2$, with exact limit law $\alpha\delta_0+(1-\alpha)\lambda$ along all prefixes, a witness $x(b,\alpha)\in M_b\subset K_b$ for each pair $(b,\alpha)$, computability for computable $\alpha$, and the endpoints. I accept it as a `Paper proof`; that label is not kernel verification.

The supporting results E2.1–E2.3, E3 and E4 hold as stated. E4 carries `External input` (Euler's pentagonal theorem).

| Timing | Repairs |
|---|---|
| Before drafting Paper XV (registry and statement hygiene) | m1, m2, m3 |
| In the manuscript | m4 (standalone comparison lemma), m5 (explicit computability), m6 (ineffectivity remark) |
| Editorial; may follow | m7, m8, m9 |

None of these repairs changes a theorem or a benchmark status.

## 8. Residual scope

This audit did not cover the following:

- the Hail rerun claimed in note line 279;
- the internal proofs of GF-34 Theorems 1 and 5, GF-32 Lemma 5.3 and GF-38 C4.2/C4.4 (checked at statement level only);
- the literature and priority review, which the note marks as provisional;
- formal verification, since no Lean statement exists for GF-45.

All finite tests are finite measurements or finite certificates. None establishes a limit.

**Cross-model review is not independent human peer review.** This verdict is an automated cross-model audit and must be confirmed by human referees before Paper XV is presented as refereed work.
