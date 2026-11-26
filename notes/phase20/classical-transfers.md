# Classical transfers: residue-class Lambert sums, the Euler-product logarithm and normal syntheses

Phase 20, Tracks E1–E3. Notation follows [dense-and-partitions.md](dense-and-partitions.md): $D_N(x)=D_N(x;b)$ is the extreme discrepancy of $\{b^nx\}$, $n<N$; $K_b=\{z:D_N(z)\to1\}$; for a weight $w$ on $\mathbb Z_{\ge1}$,

```math
\mathcal L_w(b)=\sum_{m\ge1}\frac{w(m)}{b^m-1}=\sum_{n\ge1}(1*w)(n)\,b^{-n},\qquad (1*w)(n)=\sum_{d\mid n}w(d).
```

We write $L_\chi(b)=\mathcal L_\chi(b)$ and drop $b$ when $b=2$.

**Summary of conclusions.**

| Result | Status |
| --- | --- |
| E1. Exact mod 8 and mod 24 character identities for the class sums $A_{r,q}$ | Paper proof; mod 8 identities and finite transfer in Lean (`CharacterLambertTransfer`) |
| E1. Binary: $A_1,A_3,A_5,A_7,E_{\rm odd}$ have pairwise $D_N$-differences $\ll\log\log N/\sqrt{\log N}$, hence identical $D^-$, $D^+$ and limit sets | Paper proof from Phase 17 and the Lean transfer lemmas |
| E1. General $q$ and subgroups $H$ with $(\mathbb Z/q)^\times/H$ elementary abelian of order $2^k$: class differences lie in $K_b$ in **every** base; $2^kA_{gH}\equiv E_q$ mod $K_b$; equality of discrepancy asymptotics in base 2 | Paper proof (§1.4) |
| E1. Anything about $E_{\rm odd}$, $E_{\rm even}$ or the full Erdős–Borwein constant $E$ individually | **Nothing new** (§1.6) |
| E2. $\ln2=\sum_m\mu(m)F(2^{-m})$ with error at most $\frac{16}9 2^{-M}$; its chronological prefixes are **exactly** the Taylor prefixes, so it inherits the Phase 19 period barrier verbatim | Paper proof (§2) |
| E3. Explicit normal numbers $\alpha_{b,c}+Z$ with $Z$ from modular/theta sources and explicit transfer rates | Paper proof; transcendence of the sums is not claimed (§3) |
| E3. New unconditional digit results for $\ln2$, $\pi$, $e$, $\sqrt2$, $\varphi$ or $E$ | **None** (§3.3) |

## 1. E1 — deterministic differences of residue-class Lambert sums

### 1.1 The characters modulo 8

The group $(\mathbb Z/8)^\times=\{1,3,5,7\}$ is elementary abelian of order 4. Its characters are real:

| $r \bmod 8$ | 1 | 3 | 5 | 7 |
| --- | --- | --- | --- | --- |
| $\chi_0$ | 1 | 1 | 1 | 1 |
| $\chi_4=\chi_{-4}$ | 1 | −1 | 1 | −1 |
| $\chi_8=(2/\cdot)$ | 1 | −1 | −1 | 1 |
| $\chi_{-8}=(-2/\cdot)$ | 1 | 1 | −1 | −1 |

All vanish on even integers, and $\chi_{-8}=\chi_4\chi_8$. Put $A_r=\sum_{m\equiv r\,(8)}1/(2^m-1)$ and $E_{\rm odd}=\sum_{m\ {\rm odd}}1/(2^m-1)=L_{\chi_0}$.

### 1.2 Exact identities

**Theorem E1.1.** For odd $m$ and $r$, $\mathbf 1[m\equiv r\ (8)]=\frac14\sum_{\chi}\chi(r)\chi(m)$. Hence

```math
4A_r-E_{\rm odd}=\chi_4(r)L_{\chi_4}+\chi_8(r)L_{\chi_8}+\chi_{-8}(r)L_{\chi_{-8}},
\qquad A_r-A_s=\tfrac14\sum_{\chi\ne\chi_0}(\chi(r)-\chi(s))L_\chi .
```

Explicitly:

- $4A_1-E_{\rm odd}=L_{\chi_4}+L_{\chi_8}+L_{\chi_{-8}}$ and $4A_3-E_{\rm odd}=-L_{\chi_4}-L_{\chi_8}+L_{\chi_{-8}}$;
- $4A_5-E_{\rm odd}=L_{\chi_4}-L_{\chi_8}-L_{\chi_{-8}}$ and $4A_7-E_{\rm odd}=-L_{\chi_4}+L_{\chi_8}-L_{\chi_{-8}}$;
- $A_1-A_3=\frac12(L_{\chi_4}+L_{\chi_8})$, $A_1-A_5=\frac12(L_{\chi_8}+L_{\chi_{-8}})$ and $A_1-A_7=\frac12(L_{\chi_4}+L_{\chi_{-8}})$;
- $A_3-A_5=\frac12(L_{\chi_{-8}}-L_{\chi_4})$, $A_3-A_7=\frac12(L_{\chi_{-8}}-L_{\chi_8})$ and $A_5-A_7=\frac12(L_{\chi_4}-L_{\chi_8})$.

All coefficients lie in $\frac14\mathbb Z$. The half-integer combinations are nevertheless **integer-weight** Lambert series, for example $A_1-A_3=\mathcal L_{\mathbf 1_1-\mathbf 1_3}$. Absolute convergence justifies the rearrangement. The mod 8 identities are kernel-checked as `CharacterLambertTransfer.mod8_character_identities`. The script also checks them coefficientwise, $4(1*\mathbf 1_r)-(1*\mathbf 1_{\rm odd})=\sum_\chi\chi(r)(1*\chi)$, through $n=3000$.

### 1.3 Binary transfer with rate

**Theorem E1.2.** For $r,s\in\{1,3,5,7\}$ and $N\ge3$,

```math
|D_N(A_r)-D_N(E_{\rm odd})|\le\frac2N+\sum_{\chi\ne\chi_0}\big(1-D_N(L_\chi)\big)\ll\frac{\log\log N}{\sqrt{\log N}},
\qquad |D_N(A_r)-D_N(A_s)|\ll\frac{\log\log N}{\sqrt{\log N}} .
```

Consequently $A_1,A_3,A_5,A_7,E_{\rm odd}$ have the same $D^-$, the same $D^+$ and the same set of limit points of $(D_N)$. One of them is binary normal iff all five are, and one has $D^+<1$ iff all five do.

*Proof.* Combine three facts:

- $|D_N(4y)-D_N(y)|\le2/N$ in base 2 (Lean `radixDiscrepancy_mul_pow_sub_le`);
- the sharp translation bound $|D_N(x+z)-D_N(x)|\le1-D_N(z)$, with the triangle inequality and integer Lipschitz property of $d_N(x,y)=1-D_N(x-y)$ (Lean `discDist_sum_intMul_le`, `radix_pow_linear_transfer`);
- Phase 17: $1-D_N(L_\chi)\asymp_\chi\log\log N/\sqrt{\log N}$ for every real nonprincipal $\chi$, which covers $\chi_4,\chi_8,\chi_{-8}$.

The first inequality is `mod8_odd_discrepancy_diff`. The second follows by the triangle inequality, as in `mod8_class_discrepancy_diff`. ∎

The Lean module proves the finite inequalities and the asymptotic equivalence `mod8_asymptotic_equivalence`, conditional on $D_N(L_\chi)\to1$. That hypothesis, and the rate, are the Phase 17 paper theorem.

### 1.4 General moduli: what really matters is reality of the characters

Let $q\ge1$, $G=(\mathbb Z/q)^\times$, and let $H\le G$ with $G/H$ elementary abelian of order $2^k$. Put

```math
A_{gH}(b)=\sum_{m\bmod q\,\in gH}\frac1{b^m-1},\qquad E_q(b)=\sum_{(m,q)=1}\frac1{b^m-1}.
```

The characters of $G$ trivial on $H$ are exactly the $2^k$ characters of $G/H$. They are $\pm1$-valued, hence real, and $\mathbf 1_{gH}=2^{-k}\sum_{\chi|_H=1}\chi(g)\chi$.

**Theorem E1.3.** For every radix $b\ge2$ and $g,g'\in G$:

1. $A_{gH}(b)-A_{g'H}(b)\in K_b$;
2. $2^kA_{gH}(b)-E_q(b)\in K_b$.

In both cases $1-D_N\ll_{b,q}\log\log N/\sqrt{\log N}$. Hence in every base $|D_N(A_{gH}(b))-D_N(A_{g'H}(b))|\ll\log\log N/\sqrt{\log N}$. In base 2, and more generally whenever $2^k$ is a power of $b$,

```math
|D_N(A_{gH})-D_N(E_q)|\le\frac{k}{N}+\sum_{\chi\ne\chi_0,\ \chi|_H=1}\big(1-D_N(L_\chi)\big).
```

*Proof.* Both differences are integer-weight Lambert series $\mathcal L_\psi(b)$:

```math
\psi=\mathbf 1_{gH}-\mathbf 1_{g'H}=2^{-k}\sum_{\chi\ne\chi_0}(\chi(g)-\chi(g'))\chi,\qquad
\psi'=2^k\mathbf 1_{gH}-\mathbf 1_{(m,q)=1}=\sum_{\chi\ne\chi_0}\chi(g)\chi .
```

So $1*\psi$ and $1*\psi'$ are bounded by fixed multiples of $\sum_{\chi\ne\chi_0}1*\chi$, sums over real nonprincipal $\chi$ of nonnegative multiplicative functions. Each $1*\chi$ has mass $O(X)$ and support $\ll X/\sqrt{\log X}$ (proof of Theorem D3.1(2)). The support of $1*\psi$ lies in the finite union of these supports. Track B1 (Lean `CoefficientTransfer.linear_mass_sparse_tendsto_one`, quantitative form `finite_sparse_mass_transfer`) gives membership and the rate. The base-2 inequality is `radix_pow_linear_transfer` with $b^k=2^k$. ∎

**Remarks.**

- **Which $q$ have every class covered.** Taking $H=\{1\}$ requires $G$ itself to be elementary abelian, which happens exactly for $q\mid24$, i.e. $q\in\{1,2,3,4,6,8,12,24\}$, with $\varphi(q)\in\{1,1,2,2,2,4,4,8\}$. The script checks $8A_{r,24}=\sum_\chi\chi(r)L_\chi$ for all eight classes, with characters $\chi_{-3}^a\chi_{-4}^b\chi_8^c$.
- **Dyadicity is not the mechanism.** Item 1 holds in odd bases too, because the differences are integer-weight series with sparse divisor support. The power of two matters only for converting $D_N(2^kA)$ into $D_N(A)$, which needs $2^k\in b^{\mathbb Z}$. In base 6, for example, $D_N(2y)$ and $D_N(y)$ can have different limits: the 2-cycle $\{1/7,6/7\}$ has discrepancy $5/7$ while its double $\{2/7,5/7\}$ has $1/2$.
- **Nonreal characters.** These would give a class difference whose divisor sum is typically supported on a set of positive density (for a character of odd order, $1*\chi$ is nonzero on all squarefree integers coprime to $q$). The method then says nothing, and membership is not decided here.
- **Quadratic residues.** For an odd prime $p$, $A_{\rm QR}-A_{\rm QNR}=L_{(\cdot/p)}(b)\in K_b$ and $2A_{\rm QR}\equiv2A_{\rm QNR}\equiv E_p\pmod{K_b}$ in every base. In base 2, $A_{\rm QR}$, $A_{\rm QNR}$ and $E_p$ share all discrepancy asymptotics.
- **Base 3 finite check.** $A_{1,3}(3)-A_{2,3}(3)=L_{\chi_{-3}}(3)$. At $N=4000$: $|D_N(A_{1,3})-D_N(A_{2,3})|=0.052$, compared with $1-D_N(L_{\chi_{-3}}(3))=0.562$.

### 1.5 Lean status and recommended extensions

The working tree already contains (sibling module `NormalityChecker/CharacterLambertTransfer.lean`, uncommitted at the time of writing):

```lean
theorem radixDiscrepancy_mul_pow_sub_le (b : ℕ) (x : ℝ) (k : ℕ) {N : ℕ} (hN : 0 < N) :
    |radixDiscrepancy b ((b : ℝ) ^ k * x) N - radixDiscrepancy b x N| ≤ (k : ℝ) / (N : ℝ)
theorem discDist_sum_intMul_le (b : ℕ) {N : ℕ} (hN : 0 < N) {ι : Type*} (s : Finset ι)
    (c : ι → ℤ) (z : ι → ℝ) :
    discDist b N (∑ i ∈ s, (c i : ℝ) * z i) 0 ≤
      ∑ i ∈ s, |(c i : ℝ)| * (1 - radixDiscrepancy b (z i) N)
theorem radix_pow_linear_transfer (b : ℕ) {N : ℕ} (hN : 0 < N) (k : ℕ) (x y : ℝ)
    {ι : Type*} (s : Finset ι) (c : ι → ℤ) (z : ι → ℝ)
    (hrel : (b : ℝ) ^ k * x - y = ∑ i ∈ s, (c i : ℝ) * z i) :
    |radixDiscrepancy b x N - radixDiscrepancy b y N| ≤
      (k : ℝ) / (N : ℝ) + ∑ i ∈ s, |(c i : ℝ)| * (1 - radixDiscrepancy b (z i) N)
theorem mod8_character_identities : ...
theorem mod8_odd_discrepancy_diff ... ; theorem mod8_class_discrepancy_diff ...
theorem mod8_asymptotic_equivalence ...
```

Recommended additions, in order of usefulness. These are schematic signatures; fix names and hypotheses against the module before formalizing.

```lean
/-- General radix Lambert series with integer weights. -/
noncomputable def radixLambert (b : ℕ) (w : ℕ → ℤ) : ℝ :=
  ∑' m : ℕ, (w (m + 1) : ℝ) / ((b : ℝ) ^ (m + 1) - 1)

/-- Pointwise orthogonality for an elementary abelian 2-quotient, stated with an explicit
finite family of ±1-valued periodic weights (decidable by `decide` for fixed q). -/
theorem coset_lambert_identity {q k : ℕ} (χ : Fin (2 ^ k) → ℕ → ℤ) (coset : Finset ℕ) (g : ℕ)
    (horth : ∀ m, Nat.Coprime m q →
      (2 ^ k : ℤ) * (if m % q ∈ coset then 1 else 0) = ∑ i, χ i g * χ i m)
    (hvan : ∀ i m, ¬ Nat.Coprime m q → χ i m = 0) :
    (2 ^ k : ℝ) * binaryLambert (fun m => if m % q ∈ coset then 1 else 0) =
      ∑ i, (χ i g : ℝ) * binaryLambert (χ i)

/-- mod 24 identities, all eight classes. -/
theorem mod24_character_identities (r : ℕ) (hr : Nat.Coprime r 24) :
    8 * binaryLambert (classInd 24 r) =
      ∑ i : Fin 8, chi24 i r * binaryLambert (chi24 i)

/-- Any-base kernel membership of a class difference, from Track B1. The only analytic
input is the support density of the divisor sum. -/
theorem radixLambert_mem_kernel {b : ℕ} (hb : 2 ≤ b) {w : ℕ → ℤ} {C : ℝ}
    (hmass : ∀ X, absMass (oneStar w) X ≤ C * X)
    (hsparse : Tendsto (fun N => (supportCount (oneStar w) N : ℝ) / N) atTop (𝓝 0)) :
    Tendsto (fun N => radixDiscrepancy b (radixLambert b w) N) atTop (𝓝 1)

/-- Elementary sieve input: the divisor sum of a real nonprincipal character has
upper density zero support, via `∏_{p ∈ P, χ p = -1} (1 - 1/p + 1/p^2) → 0`. -/
theorem oneStar_char_support_density_zero (χ : ℕ → ℤ) (hreal : ...) (hnonprincipal : ...) :
    Tendsto (fun N => (supportCount (oneStar χ) N : ℝ) / N) atTop (𝓝 0)
```

The last item needs divergence of $\sum_{\chi(p)=-1}1/p$, that is, Dirichlet's theorem for one class. For the binary statements one can instead keep the Phase 17 rate as a hypothesis, as `mod8_asymptotic_equivalence` does.

### 1.6 What E1 does and does not say about the Erdős–Borwein constant

Write $\mathcal E(q)=\sum_{m\ge1}q^m/(1-q^m)$. Then $E=\mathcal E(1/2)=\sum_n\tau(n)2^{-n}$, $E_{\rm even}=\sum_m1/(4^m-1)=\mathcal E(1/4)$, and $E_{\rm odd}=E-E_{\rm even}=\sum_n\tau_{\rm odd}(n)2^{-n}$.

- **Proved:** the five numbers $A_1,A_3,A_5,A_7,E_{\rm odd}$ form a single class in $\mathbb R/K_2$ after scaling by powers of 2. Their discrepancy behaviours coincide.
- **Not proved:** any statement about the discrepancy of $E_{\rm odd}$ itself, of $E_{\rm even}$, or of $E$.
  - $E_{\rm odd}$, $E_{\rm even}$ and $E$ all have dense divisor-function coefficients ($\tau_{\rm odd}$, or $\tau$ placed on the even positions), so neither Track B1 nor Phase 17 applies.
  - $E_{\rm even}$ is not related to $E_{\rm odd}$ by a binary shift or a kernel translation that we can exhibit.
  - The Phase 17 finite-statistic thresholds for $E$ still require divisor correlations that are not available.

  E1 transfers whatever is true for one member of the class to the others. It decides nothing.

## 2. E2 — the logarithmic Euler product

### 2.1 Identities

```math
F(q)=-\log\prod_{k\ge1}(1-q^k)=\sum_{n\ge1}\sigma_{-1}(n)q^n=\sum_{j\ge1}\frac1j\,\frac{q^j}{1-q^j},\qquad \sigma_{-1}(n)=\frac{\sigma(n)}n .
```

Since $F(q)=\sum_k-\log(1-q^k)$ and $\sum_{m\mid n}\mu(m)=[n=1]$, Möbius inversion gives

```math
-\log(1-q)=\sum_{m\ge1}\mu(m)F(q^m),\qquad \ln2=\sum_{m\ge1}\mu(m)F(2^{-m}),\qquad 2=\prod_{m\ge1}P(2^{-m})^{\mu(m)},
```

with $P(q)=e^{F(q)}$ the partition generating function. Also $E_2(q)=1-24qF'(q)$, which links E2 to D3.

**Truncation error.** Since $\sigma_{-1}(n)\le1+\log n\le n$, $F(q)\le q/(1-q)^2$. Hence for $M\ge1$

```math
\Big|\ln2-\sum_{m\le M}\mu(m)F(2^{-m})\Big|\le\sum_{m>M}\frac{2^{-m}}{(1-2^{-m})^2}\le\frac{2^{-M}}{(1-2^{-M-1})^2}\le\frac{16}{9}\,2^{-M}.
```

The error has order $2^{-M}$. Its sign and leading term depend on $\mu(M+1),\mu(M+2),\dots$, so there is no clean two-sided asymptotic. The script measures $5.3\cdot10^{-4}$, $6.1\cdot10^{-7}$ and $7.9\cdot10^{-13}$ at $M=10,20,40$. After a binary shift by $N$, accuracy requires $M\ge N+\omega(1)$.

### 2.2 The Möbius collapse

**Theorem E2.1.** Reindex the absolutely convergent double series $\sum_m\mu(m)\sum_n\sigma_{-1}(n)2^{-mn}$ by $K=mn$. It becomes **exactly the Taylor series** $\sum_K2^{-K}/K$. Consequently:

1. For every $N$, the chronological prefix (all pairs with $mn\le N$) equals $P_N^{\rm Taylor}=\sum_{K\le N}2^{-K}/K$.
2. The row truncation $\sum_{m\le M}\mu(m)F(2^{-m})$ with $M\ge N$ has the same chronological prefix through exponent $N$.
3. Every odd prime $p\in(N/2,N]$ occurs only in the pair $(m,n)=(1,p)$, with coefficient $\sigma_{-1}(p)=1+1/p$. So it divides the odd part $q_N$ of the reduced denominator of $2^NP_N$.
4. Hence the Phase 19 bound applies verbatim:

```math
\liminf_{N\to\infty}\frac{\log\operatorname{ord}_{q_N}(2)}{\log N\,\log\log N}\ge\frac1{2\log2},
```

even after deleting one prime axis. Full-period and fixed-complement grid sampling on polynomial windows is therefore ruled out exactly as for the Taylor prefixes.

*Proof.* $\sigma_{-1}=1*\mathrm{id}^{-1}$, so $\mu*\sigma_{-1}=\mu*1*\mathrm{id}^{-1}=\mathrm{id}^{-1}$. Items 1–2 follow by collecting the pairs with $mn=K$. A pair $(m,n)$ with $p\mid n$ and $m\ge2$ has $mn\ge2p>N$. Item 4 is the counting lemma of [Phase 19, taylor-periods](../phase19/taylor-periods.md) applied to the same prefixes. ∎

The script checks $\mu*\sigma_{-1}=1/K$ exactly for $K\le1500$, the prefix equality and the prime divisibility for $N=60,120,240$.

**Verdict.** The Euler-product synthesis does not overcome the chronological-prefix period barrier. At the level of rational prefixes it is the same object. The barrier is not merely inherited in a similar form: it is literally the same barrier. Even a single row $F(2^{-1})$ has prefix denominators $\operatorname{lcm}(1,\dots,N)$. The product form $2=\prod P(2^{-m})^{\mu(m)}$ gives no digit information either, since the factors $P(2^{-m})$ have dense coefficients (D2).

## 3. E3 — concrete normal syntheses and the classical verdict

### 3.1 The synthesis principle

**Proposition E3.1.** If $\alpha$ is normal in base $b$ and $Z\in K_b$, then $\alpha+Z$ is normal and, for every $N$,

```math
|D_N(\alpha+Z)-D_N(\alpha)|\le1-D_N(Z).
```

This is the sharp translation theorem (Lean `SharpTranslation.sharp_translation`). Normality is $D_N\to0$ by Wall's theorem.

### 3.2 Explicit catalogue

Take for $\alpha$ the Stoneham number $\alpha_{b,c}=\sum_{k\ge1}c^{-k}b^{-c^k}$, with $b,c\ge2$ coprime. It is normal in base $b$ (Bailey–Crandall, Experimental Math. 11 (2002)) and transcendental: its partial sums have denominators supported on the primes of $bc$ and errors $\approx q^{-c}$, so Ridout's theorem applies. Each $Z$ below lies in $K_b$ (dense-and-partitions §3.1, Phase 18, Phase 19), with the stated bound for $1-D_N(Z)$:

| $Z$ | Source of the arithmetic | $1-D_N(Z)\ll$ |
| --- | --- | --- |
| $E_b=\prod(1-b^{-k})$ | Euler pentagonal theorem | $\log N/\sqrt N$ |
| $E_b^3$ | Jacobi | $\log N/\sqrt N$ |
| $\Theta_3(1/b)$ | squares | $\log N/\sqrt N$ |
| $\Theta_3(1/b)^2$, $\Theta_Q(1/b)$ ($Q$ binary, positive definite) | two-square / binary-form representation numbers | $\log\log N/\sqrt{\log N}$ |
| $L_\chi(b)$, $\chi$ real nonprincipal | divisor sums of $\chi$ | $\log\log N/\sqrt{\log N}$ |
| missing-digit $W$ of index dimension $\sigma$ | Phase 19 | $(\log N/N)^{1-\sigma}$ (exact order) |

Finite sums of these, with integer or radix-primary rational coefficients, add their bounds. So $x=\alpha_{b,c}+E_b+\Theta_3(1/b)^2+L_{\chi_8}(b)$, for example, is normal with $|D_N(x)-D_N(\alpha_{b,c})|\ll\log\log N/\sqrt{\log N}$.

**Scope.** These are explicit normal numbers mixing Stoneham and modular or theta data, with explicit transfer rates. Their **transcendence is not claimed**. A sum of two transcendental numbers can be algebraic, and no algebraic-independence statement linking $\alpha_{b,c}$ with $E_b$ or $\Theta_3(1/b)$ is known to us. Normality gives irrationality only. Finite check in base 2 at $N=4000$:

| Number | $D_{4000}$ |
| --- | --- |
| $\alpha_{2,3}$ | 0.0076 |
| $\alpha_{2,3}+E_2$ | 0.0135 |
| $\alpha_{2,3}+\Theta_3(1/2)$ | 0.0174 |
| $\alpha_{2,3}+L_{\chi_4}$ | 0.0150 |

Each satisfies the inequality of Proposition E3.1 exactly, up to the $2^{-40}$ truncation.

### 3.3 Plain verdict for the classical constants

No new unconditional digit-distribution conclusion is obtained for $\ln2$, $\pi$, $e$, $\sqrt2$, $\varphi$ or the full Erdős–Borwein constant $E$.

- **$\ln2$.** E2 is the Taylor series in disguise (Theorem E2.1). The Phase 19 horizontal rows and the period barrier are unchanged.
- **$\pi$, $e$, algebraic irrationals.** Nothing in Tracks D or E touches them. The Phase 18 functional obstruction stands: no finite differential-algebraic identity from lacunary rays can produce their generating functions.
- **$E$.** The new E1 theorem identifies the discrepancy asymptotics of $A_1,A_3,A_5,A_7$ and $E_{\rm odd}$ (and, in general, of residue classes with real characters). It says nothing about $E_{\rm odd}$ itself, about $E_{\rm even}=\mathcal E(1/4)$, or about $E=E_{\rm odd}+E_{\rm even}$.
- **Modular constants** ($P_b$, $\Theta^3$, $\Theta^4$, $E_{2k}(1/b)$, $\Delta(1/b)$). Transcendence is known (Nesterenko; Duverney–Nishioka–Nishioka–Shiokawa). Digit distribution is open. The only new facts are kernel memberships for the sparse rungs and exact transfers modulo $K_b$ (dense-and-partitions §§3–4).

## 4. Verification

`python -B scripts/phase20_dense_classical.py` exits 0. For E1–E3 it checks:

- the mod 8 identities and their character table, and all eight mod 24 identities, coefficientwise through $n=3000$;
- nonnegativity of each $1*\chi$, with finite support densities $0.34$–$0.45$ through 3000 (the asymptotic decay $\asymp1/\sqrt{\log X}$ is far too slow to be visible in this range);
- the finite inequality of Theorem E1.2 at $N=1000,2000,4000$. It holds with large slack: $\max_r|D_N(A_r)-D_N(E_{\rm odd})|=0.068$, while the right side is $2.03$, which exceeds 1. At these $N$ the slow Phase 17 rate makes the bound vacuous; the asymptotic statement is the content;
- the E2 collapse, truncation bounds and prime divisibility;
- the E3 translation inequalities.

Finite discrepancies of the class sums at $N=4000$: $A_1:0.037$, $A_3:0.093$, $A_5:0.084$, $A_7:0.089$, $E_{\rm odd}:0.105$. The Phase 17 rate predicts that their pairwise differences tend to zero only very slowly.

## 5. Open questions

1. Decide $D^+(E_{\rm odd})<1$ (equivalently, by E1, for any $A_r$), or relate $E_{\rm even}$ to $E_{\rm odd}$ modulo $K_2$.
2. For a modulus with a nonreal character (e.g. $q=5$), is $A_{1,5}(b)-A_{2,5}(b)\in K_b$? The divisor-support method fails, and nonmembership is not proved.
3. Does any infinite identity other than the Möbius/Taylor collapse supply rational approximants of $\ln2$ whose reduced denominators avoid a positive proportion of the primes in $(N/2,N]$ at the required accuracy $2^{-N-\omega(1)}$?
