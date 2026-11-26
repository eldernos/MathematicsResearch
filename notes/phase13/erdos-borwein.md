# Binary words and Fourier sums for the Erdős–Borwein constant

Let $E=\sum_{m\ge1}(2^m-1)^{-1}$, let $\tau(m)$ count the positive divisors of $m$, and write $e(t)=\exp(2\pi i t)$. Here and below `log` is natural. A shift $n\ge0$ reads the word starting at fractional digit $n+1$. The word of length $k$ and value $v$ occurs precisely when the fractional part of $2^n E$ belongs to $[v2^{-k},(v+1)2^{-k})$.

**What the sources establish.** Captain Sude's elementary Lean release gives an unconditional lower count $N\exp[-70000(\log\log N)^3]$ for every fixed word at all sufficiently large cutoffs. Mira Cult's November 2026 claim concerns short windows. For fixed $7/12<a\le1$ and fixed nonempty $w$, every sufficiently late window of $N^a\le H\le N$ digits after digit $N$ contains at least $c_{a,w}H$ copies wholly inside it. Its crucial input is a weighted local estimate on primes conditioned on an actual divisor term. Below we check the reductions, the range of the cited prime theorem and the role of the weights. A subsequent independent paper audit verifies the multistage weighted estimate by binomial upper and lower bounds and checks the uniform error through the prime-incidence argument. The analytic density theorem is attributed to Mira Cult. [Weighted local-limit review](reviews/erdos-local-limit.md) Binary normality of $E$ remains open. [Elementary release][elementary] · [Mira's theorem][mira] · [Weighted comparison][weighted]

**Two transfers.** An unconditional deduction from Shiu's theorem below reduces the full divisor Fourier statistic on every window of length between $N^\delta$ and $N$ for fixed $\delta>0$ to $O(\sqrt{T\log T})$ offsets around $T=\log\log N$. A separate Lean proof converts occurrences of a single specified word into an explicit deficit from the trivial Fourier bound on the same window. The elementary release supplies an unconditional, vanishing proportional deficit on prefixes. Mira's paper supplies a fixed positive proportional deficit on its short windows by the reviewed analytic estimates. Neither deduction establishes cancellation of order $o(H)$. [Lean transfer](../../NormalityChecker/ErdosBorweinFourier.lean) · [Shiu, Theorem 1][shiu] · [Henriot, p. 1][henriot]

## Source and tools registry

| Source and version | Exact input or conclusion | Scope |
| --- | --- | --- |
| P. Erdős (1948), pp. 63–66 | For positive integer $b>1$, the divisor series at $1/b$ is irrational. CRT forces arbitrarily long strings of zeros with nontermination. | Positive-base proof in the original. The gap later discussed by Vandehey concerns the extension to negative bases. [Original scan][erdos] · [Vandehey][van] |
| D. H. Bailey and R. E. Crandall (2002), Conjecture 5.3 and Theorem 5.5 | Binary normality is equivalent to equidistribution of the fractional parts of $(2^d-1)\sum_{k\le d}(2^k-1)^{-1}$. | Published equivalence. §5 uses “2-density” for a dense doubling orbit. [Paper][bc] |
| R. Crandall (2012), §7, and J. M. Campbell, arXiv:2605.24160v1 (22 May 2026), Theorem 1 | Crandall asks whether `11` appears infinitely often. Campbell proves that it does and asks about all words in §4. | Campbell takes $\delta=1/4$ in the AGP prime estimate, makes $\tau(n+2)=6$, forces $2^{j+1}\mid\tau(n+j)$ at other early sites, and bounds the positive tail. Thus $\{2^{n-1}E\}\in[3/4,1)$ for unbounded $n$. The theorem gives no lower frequency. [Crandall][crandall] · [Campbell][campbell] |
| W. R. Alford, A. Granville and C. Pomerance (1994), p. 705, in J. Vandehey's Proposition 2.1 | For fixed $0<\delta<5/12$, a lower bound $X/(2\varphi(q)\log X)$ in reduced classes for $q\le X^\delta$ outside multiples of a bounded list of exceptional integers $>\log X$. | Supplies primes on a **growing progression** after avoiding exceptional divisors. [AGP][agp] · [Precise formulation][van] |
| Captain Sude, 7 September, `erdos-borwein-disjunctivity`, tag `v1.0.0` at `bd98789a177470cc4b3e33e6769e859f6144c906` | `lean/ErdosBorwein/Main.lean` proves `binaryDisjunctive_lambertE (hAGP : AGP) (hSupply : PrimeIntervalSupply)` and `every_binary_block` with the same arguments. | `PrimeInputs.lean` fixes $\delta=1/4$ for AGP as above and asks for at least $L/(3\log L)$ primes strictly between $L$ and $2L$ eventually. The paper's Theorem 1 gives $N\exp[-C_w(\log\log N)^3]$. This first Lean release checks qualitative disjunctivity under the two arguments. Axiom output alone cannot detect theorem arguments. [Theorem type][capmain] · [Hypotheses][capinputs] · [Paper][cappaper] |
| Captain Sude, 8 September, `erdos-borwein-disjunctivity-elementary`, `d51e93e91ff43efef6918efdd4258bbd43bad7aa` | Inside the ZIP, `lean/ErdosBorwein/ElementaryMain.lean` proves `binaryDisjunctive_lambertE_unconditional`. `ElementaryQuantitative.lean` proves `quantitative_occurrences_lambertE (ell v) (hv : v < 2^ell)` with coefficient 70000 and a word-dependent threshold. | A closed `primeIntervalSupply`, squarefree cofactors and a variable reading position replace the earlier assumptions. `FiniteCounting.lean` counts all starts $0\le n<N$, including words which can finish after digit $N$. For wholly contained words subtract at most $k-1$. Both Captain Sude TeX sources have an empty author line. “Captain Sude” is the Git commit author and account attribution. [Elementary release and archive][elementary] |
| Mira-acc, September and October public research gists | The first survey records no assembled Lambert-series proof. S06 in `gistfile1.txt` of *Normality research #2*, revision `41b5a780f79f7bdd275cd96e7e310b000a897d35`, is titled *Logarithmic divisor encoders and Lambert-series digits* and credited “Research note prepared for Mira.” For fixed words it gives $N\exp[-C_w(\log\log N)^2\log\log\log N]$. For $0<c<1/16$, $4\sqrt c<\eta<1$, it claims $N\exp[-(\log N)^\eta]$ uniformly up to length $c(\log_2\log N)^2$. | Conventional CRT/AGP estimates with distinct quantifiers. L01/L03 are separate from November's claim. The archived S06 TeX extracted with one final LF has SHA-256 `aac3c4a183331e03af9ffd61789850f08a0e9a69d12a5e1d285f672e20c0e5aa`. [First survey][gist1] · [October source][gist2] |
| Mira Cult, `Mira-Cult/math`, claim 0002, 23 November | First public commit `a74afd540a6401026e7789a3734ce1492f823065`, commit author `mira-emmy`. The theorem is the research-folder README from `149831943806a656c9efaa14cacbd9c915b2a2ba`. The paper credits GPT-6.2 Astra with developing and drafting the proof under Mira's guidance. | The verification file records two internal nonauthor checks. Public files include the proof and seven analytic notes. Their cited research-source revision `3d6095d99e07b71fc112d538c845d2cf6c6da80d` was unavailable from the public math repo (commit API 422). On 24 November both the public and authenticated repo lookups for `Mira-Cult/rh`, the raw protocol path and the cited issue lookup returned 404. The public gists describe the RH program. Its operator normality is unrelated to binary digit normality. [Initial release][original] · [Verification][miraverify] · [Public research archive][archive] · [Referenced RH project][rh] |
| Captain Sude, `generalized-Lambert-disjunctivity-and-nonnormality`, `fe33be210446c6c0b127ca7757fc8f1182c5b541` | `PowerLambert.powerLambert_full_theorem` treats $\sum_{m\ge1}(b^{m^r}-1)^{-1}$ for $b,r\ge2$. Every word has a positive limiting frequency and the value is nonnormal. | A concrete counterexample to the inference from positive word frequencies to normality. The present $E$ has $r=1$, outside the hypotheses. [Statement and source][power] |

## Four different occurrence claims

For a fixed word let $A(x)$ count its starting positions through $x$. Ordinary lower density is $\liminf A(N)/N$. Lower logarithmic density is the liminf of $\sum_{n\le N,\ n\in A}1/n\,/\log N$, indexing starts from 1. Ordinary positive lower density implies positive lower logarithmic density by partial summation. Mira's window statement implies ordinary positive lower density by taking $N=\lfloor M/2\rfloor$, $H=N$, and keeping the wholly contained starts through digit $M$. It also gives a positive proportion in each of its specified shorter windows. A lower prefix bound with $\log A(N)/\log N\to1$ alone gives neither positive density. The primes already satisfy $A(N)\sim N/\log N$ and have logarithmic density zero.

* **Logarithmic versus ordinary.** The union of integer intervals $[e^{j^2},e^{j^2+j})$, $j\ge1$, has logarithmic density $1/2$. The complete intervals supply harmonic mass $\sum_{j<J}j\sim J^2/2$, and the last partial interval costs $O(J)$. Just before $e^{(J+1)^2}$ its ordinary proportion tends to zero, and just before $e^{J^2+J}$ it tends to one.
* **Disjunctivity.** Every finite word occurs. Applying this to arbitrarily long repetitions gives occurrences arbitrarily far out. Insert the list of all length-$j$ words starting at $2^{2^j}$ into an otherwise zero digit stream. The changed positions have ordinary and logarithmic density zero, while the stream is disjunctive.
* **Normality.** Every $k$-word must have limiting ordinary frequency $2^{-k}$. A typical Bernoulli stream with probability $1/3$ of a one has positive limiting frequencies for all words and limiting one-frequency $1/3$. It even satisfies the short-window claim for each fixed power $a>0$. To see this, split overlapping starts by their residue modulo $k$, use a binomial exponential tail on each disjoint class, and sum $O(N)\exp(-c_wN^a)$ over $N$. Take the countable intersection over words and positive rational $a$. Thus short-window lower bounds alone cannot settle normality.

## Audit of the November proof

**The arithmetic and the measure.** Expanding each Lambert denominator and collecting products gives $E=\sum_{m\ge1}\tau(m)2^{-m}$ by nonnegativity. At the one-based start $n$, all indices below $n$ drop out of $e(2^{n-1}E)$. For an integer word value $u$, put $A=2^{2u}$, choose odd squarefree $m$, $b=Am\le N^\theta$, $j_0=\omega(m)+k+1$, and use starts $n=bp-j_0$ with $p>b$ prime. Then $\tau(bp)=2^{\omega(m)+1}(2u+1)$ and its individual contribution is exactly $(2u+1)/2^{k+1}$. This calculation applies to both end cylinders. For a concrete failure of midpoint forcing alone, take $w=10$, $m=1$, $p=17$. The term at $n+3=272$ contributes $10/16$, yet the actual pair beginning at digit $n=269$ is `01`. The exact computation below verifies the carry. [Fixed-word construction][inc]

**First and second moments.** Let $F(n)$ count certifying factorizations at a uniformly chosen eligible start. For fixed $b$ the prime interval has endpoint $X\asymp N/b$ and length $Y\sim H/b$. Choose $a'<a$ above $7/12$ to absorb the $k-1$ end trim, then $\theta>0$ small with $(a'-\theta)/(1-\theta)>7/12$, $a'-\theta>1/2$ and $\theta<a'/4$. Short prime counts and partial summation give

```math
\mathbb E F \longrightarrow
\frac{2}{3\zeta(2) A}\log\!\left(\frac1{1-\theta}\right).
```

Indeed odd squarefree integers have density $2/(3\zeta(2))$, and integrating $dm/[m\log(N/(Am))]$ gives the displayed logarithm. Discarding $\omega(m)>C\log\log N$ costs $o(1)$ by the Euler product for $\sum z^{\omega(m)}/m$, for fixed $z>1$ over squarefree $m$. At a fixed offset the prime $p>\sqrt{bp}$ is unique. For two distinct offsets with $m=g m_1$ and $m'=g m_2$, the determinant difference $D=\omega(m_1)-\omega(m_2)$ is nonzero and $Ag\mid D$. The two primes are primitive linear forms in a parameter on an interval of length $Hg/(Amm')+O(1)$. At each prime outside the divisors of $m_1m_2 D/(Ag)$ there are two excluded residues. A dimension-two upper-bound sieve on the parameter gives the square of the prime-log saving. Inadmissible pairs give zero. To check the sum of the singular factors, enlarge the coprime cofactor pairs to two independent squarefree harmonic products, with Bernoulli prime probabilities $q_\ell=(1+C/\ell)/(\ell+1+C/\ell)$. Each normalizer is $O(\theta\log N)$. The characteristic function of the *difference* of the two prime counts has modulus $\le\exp[-cT\sin^2(t/2)]$, $T=\log\log N$, since their variances are comparable to $T$ even after omitting primes of $g\le CT$. Finite Fourier inversion bounds the probability of $d g\mid D$ by $O(1/(dg)+1/\sqrt T)$. Expansion of the remaining singular factor involves only $gd\le CT$ before enlargement. Its main sum is bounded by $\sum_g g^{-2}\sum_d\mu^2(d)C^{\omega(d)}/d^2$, and its error is $O((\log(2T))^{C+1}/\sqrt T)$. These checks fund $\mathbb EF(F-1)\ll_a\theta^2/A$ and $\mathbb EF^2\ll_a\theta/A$. These are moments of actual incidences. A lower bound for the proportion of starts with a good incidence follows from Cauchy–Schwarz only after the complementary phase has been controlled. [Adaptive count][adaptive] · [Fixed anchor][inc]

**Which short-interval theorem pays for the comparison.** Perelli, Pintz and Salerno, printed pp. 529–530, display (2) as a sum over $q\le Q$ of the maximum over reduced residues, $h\le y$ and $x/2\le z\le x$ of the absolute error in $\psi(z+h;q,r)-\psi(z;q,r)-h/\varphi(q)$. The bound is $\ll y/(\log x)^B$ for each fixed saving $B$. With $y=x^\vartheta$ they quote Huxley–Iwaniec's range $\nu\le3\vartheta-7/4-\epsilon$ for $7/12<\vartheta\le29/48$, where $Q=x^\nu/(\log x)^D$. The threshold is strict. Choose $\vartheta$ strictly below the actual uniform exponent for $Y$ and $\rho<\min(\nu,\vartheta-1/2)$. Split a longer prime interval into $O(Y/X^\vartheta)$ pieces and, if needed, a bounded number of dyadic ranges. The maxima in (2) pay for each translated piece, including the final short piece. Removing all prime powers costs $O(X^{\rho+1/2}\log^2 X)$ after summing over the moduli, negligible at every fixed log saving. This supplies a small positive power level for factorial moments on the actual $p$ intervals. The sum over moduli is outside the maximum over classes, so one must bound the multiplicity with which a modulus is charged. The normalized log-prime density relative to uniform counting of these primes is $1+O(1/\log X)$ pointwise. Consequently even an unbounded **nonnegative** marked expectation transfers multiplicatively. All final starts retain ordinary weight. [Printed inequalities][pps] · [Huxley–Iwaniec][hi] · [Use on the incidence measure][marked]

**The conditional estimate used by the proof.** Fix the selected incidence and omit only its midpoint from the circle product, leaving a product $R$. At another offset put $g_j=(b,j-j_0)$ and strip it to obtain the primitive form $(b/g_j)p+(j-j_0)/g_j$. The model counts eligible small prime divisors of these forms in successive disjoint prime ranges. On each individual prime it uses the *same* random reduced residue in all coordinates. Large primes exceeding the shift differences hit at most one label. The reciprocal mass lost from the divisors of $b$ is $O(\log T)$ even for the worst $b$, smaller than the $\sqrt T$ width. If $U_j$ is the resulting terminal count, the event $\mathcal A$ avoids $|j+1-U_j|\le W$ at central sites $|j-T|\le L\sqrt T$, omitting $j_0$. It concerns the count before the remaining prime factors are added. The following four checks distinguish the local estimate actually needed from an appeal to a scalar Erdős–Kac theorem.

1. At fixed order $q$, a central joint atom is of order $T^{-q/2}$. On primes above $T^B$ the cost of replacing mutually exclusive label hits by independent Bernoulli variables is $O_q(\sum_{\ell>T^B}\ell^{-2})=O_q(T^{-B})$, small at that atom scale if $B>q/2$. Small-prime increments need their own tail bound. Each has size at most $q$, and the total has a fixed exponential moment bounded by a power of $\log T$ for primes up to $T^B$. Changing finitely many forced prime classes displaces means by $O_q(1)$. These facts explain the product Gaussian *model*. To pass to arithmetic one needs mixed factorial moments with the extra forced prime or prime-power classes still attached. The source truncates the first characteristic-function Taylor series at degree $C_q T$ with endpoint $X^{1/T^8}$. Subsequent degrees decrease on iterated-log scales. A modulus with $O_q(T)$ prime factors has at most $\exp(O_q(T))$ assignments to the label subsets. The available arbitrary log savings cover that multiplicity. The inverse-binomial sum $\sum_{b\ge r}\binom br^{-1}=r/(r-1)$ for $r>1$ controls the exterior when a bank count exceeds its truncation. For one label with count $u$, Taylor expansion of $(1+z)^u$ on the segment from $1$ to $e^{it}$ gives an absolute remainder at most $2^r\binom ur$ after degrees below $r$, since that segment lies in the closed unit disk. For several labels, telescoping the product bounds its remainder by sums of products of these positive endpoint weights. At a later bank, primes assigned to distinct, separated labels cannot coincide. Dropping cross-label distinctness in the positive comparator sum only increases its factorial moment, bounding it by a product of $\mu_i^{k_i}/k_i!$ for label means $\mu_i$ (with bounded shifts under forces). Thus taking degrees large compared with the means makes an endpoint exponentially small. The recursion requires the earlier exact atom weighted by the factorial test for the new bank. The public weighted comparison gives a fixed tolerance plus an additive $\exp(-\kappa T)$ error. Its terminal exponent must retain quantitative dependence on $W$. [Mixed moments][weighted] · [Geometric cutoffs][atoms]
2. The central avoidance probability in the Gaussian model is $P_0=\prod_j(1-p_j)$ with $\sum p_j\le 2W+1+o(1)$ and $\max p_j=o(1)$, hence $P_0\ge e^{-4W}$ for large fixed $W$. A Bonferroni term at order $Q\ge100W$ is bounded by $(3eW/Q)^Q$. Summing atom errors over $O_W(T^{q/2})$ tuples costs exactly the inverse lattice scale. To estimate the complementary angle on this rare event, mark the excluded site's atom and up to two additional prime or power tests. Removing that site from the avoidance product gives $P_0/(1-p_j)$, leaving the *same* small probability in the numerator. An unconditional $O(1/W)$ tail divided by $e^{-4W}$ would yield no useful estimate. The polynomial-in-$W$ inverse terminal exponent and the $\exp(-r_f)$ local tolerance in §1 are material here. [Conditional isolation, §§1–3][isolate]
3. For a bank deficit $s=j+1-U_j$ outside $[-W,W]$, small valuation error and small log odd-part make the angular error zero or $O(2^{-|s|/2})$. Otherwise its bound of two is paid by $Z_j/s^2$, with $Z_j$ a constant times the sum of squares of the omitted prime count, repeated-power count, and $1+\Omega(g_j)$. The comparator mean is $\ll_a(1+\Omega(g_j))^2+\log^2(W+2)$. Positive divisor expansion of the gcd factor and summation over $j\equiv j_0\pmod d$ give $O(1/d+1/\sqrt T)$ against a normalized Gaussian, regardless of the adaptive $j_0$. In the subsequent average over $b$, multiples of $d$ in the cofactor's harmonic measure cost another $O(1/d)$ after normalization, with the fixed anchor pulled out first. Reversing those steps would presume independence of the cofactor and its own offset. For exterior sites the weighted one-site bound has the integrable factor $(1+(v-T)^2/T)^{-1}/\sqrt T$. The assertion for the **true** valuation needs the supplementary repeated-power moments, not just a maximum atom bound for the bank count. [Weighted tail][marked] · [Integrated deficit][integrated]
4. Taking $L=e^{20W}$ and the outer deficit cutoff $B_*=\lceil e^{50W}\rceil$ puts both $O(1/L)$ and $O(L\log^2(W+2)/B_*)$ below the scale of $P_0$. The remaining real tail after $J\ge10T$ has mean $O(T\log N\,2^{-J})+o(1)$ on incidences for fixed $\theta$, by divisor pairing on the ordinary interval and $F\le J+O(1)$. Thus the quoted central weighted estimate gives $\mathbb E_{\rm inc}(|R-1|\mid\mathcal A)\ll_{a,w}(1+\log^2(W+2))/W+o_W(1)$, where the last error tends to zero as $N\to\infty$ at **fixed** $W$. The cylinder midpoint has distance $2\sin(\pi/2^{k+1})$ to the nearer boundary on the circle. Choose $W$ after $k$ and before $N$. Markov then leaves positive incidence mass strictly inside the word. Finally $\Pr(F_{\rm good}>0)\ge(\mathbb EF_{\rm good})^2/\mathbb EF^2$. This last denominator is for the ordinary interval of eligible starts. [Isolation, §§3–5][isolate] · [Proof outline][outline]

**Verdict.** The primary short-interval theorem has the required range, and the counting, conditioning, endpoint and normalization steps above are consistent. No counterexample to the stated window theorem emerged. The analytic input with the greatest remaining verification burden is the uniform force-weighted, multi-bank exact-atom induction, in particular its relative error after the terminal cutoff is chosen as a function of $W$. We have checked its required counting scales and their downstream use. We did not independently reconstruct every mixed Taylor remainder with future-bank weights. The public result is an internally reviewed conventional proof. The local Lean transfer below accepts a count as a hypothesis and makes no assumption about how the count was obtained. [Public verification scope][miraverify]

## An unconditional localization of the divisor Fourier statistic

Fix $0<\delta\le1$, $N^\delta\le H\le N$, and an integer $h$. Average over integer shifts $N\le n<N+H$, writing $\mathbb E$ for this average. Put $T=\log\log N$, $B=4\sqrt{T\log T}$, and take $N$ large. With $J_N$ the positive integers $j$ satisfying $|j-T|\le B$, we obtain the uniform bound

```math
\mathbb E\left| e(h2^nE) -
e\left(h\sum_{j\in J_N}\tau(n+j)2^{-j}\right)\right|
\ll_{\delta,h} T^{-3}.
```

This is a paper deduction independent of the November conditional local limit theorem. October's S06 already reduces the prefix Fourier mean to the first $\lceil3\log_2\log N\rceil$ offsets. Here both ends of the divisor sum are removed on ordinary short windows. The absolute difference estimate also permits any additional row multiplier of modulus at most one. Conditioning divides the error budget by the probability of the event. [October work order W09][gist2]

**Uniform multiplicative moments.** Let $\omega_1(m)$ count primes of exponent exactly one in $m$. Take $r=B/(2T)$, $s=r/\log 2$. Eventually $0<s<1$. Apply Shiu's bound to the nonnegative multiplicative functions $f_-(m)=e^{-r\omega_1(m)}$ and $f_+(m)=\tau(m)^s$. They have common bounds $f(p^a)\le2^a$ and $f(m)\le\tau(m)\ll_\epsilon m^\epsilon$. Henriot explicitly states that the constants depend on these majorants and the fixed interval exponents, so taking $r$ to zero with $N$ is permitted. The unrestricted formulation takes modulus 1. For $j\le4\log_2 N+1$ use a length exponent strictly below $\delta$, since the translated endpoints are all comparable to $N$. The prime values $e^{-r}$ and $2^s=e^r$ and Mertens' prime reciprocal sum give

```math
\mathbb E f_-(n+j)\ll_\delta \exp[(e^{-r}-1)T],
\qquad
\mathbb E f_+(n+j)\ll_\delta \exp[(e^r-1)T].
```

Shiu's original Theorem 1 prints a reduced class $0<a<k$. One can also recover the unrestricted bound from $a=1,k=2$ by writing the argument as $2^v m$ with $m$ odd. For $v\le(\delta/4)\log_2 N$ the shortened intervals still have a fixed power margin, $\log(N/2^v)\asymp_\delta\log N$, and $\sum (v+1)2^{-v}<\infty$ pays the even factors. Larger $v$ are bounded together by divisibility by the first omitted power of two, with $f_\pm(m)\ll_\delta N^{\delta/8}$ and $O(HN^{-\delta/4}+1)$ possibilities. [Original theorem, pp. 162–163][shiu] · [Uniform dependence, p. 1][henriot]

**Early offsets.** Since $2^{\omega_1(m)}\mid\tau(m)$, the term at $j<T-B$ is integral unless $\omega_1(n+j)<j$. Markov bounds that probability by a constant times

```math
\exp[r(T-B)+(e^{-r}-1)T]\le\exp[-rB+r^2T]=T^{-4}.
```

Here $e^{-r}-1+r\le r^2$ and $r=B/(2T)$. A union over $O(T)$ early offsets costs $O_\delta(T^{-3})$. In particular the character built from *any fixed number* of first offsets tends to one in ordinary mean, for every fixed integer frequency. Retaining a fixed width at the beginning therefore destroys the cancellation statistic.

**Late offsets.** Let $M=\lceil4\log_2 N\rceil$. Between $T+B$ and $M$, use positivity and $(\sum a_j)^s\le\sum a_j^s$. The $s$-moment of the real tail on those offsets is bounded by a constant times

```math
\frac{\exp[(e^r-1)T-r(T+B)]}{1-e^{-r}}
\ll r^{-1}\exp[-rB+r^2T]\ll T^{-3}.
```

The second inequality uses $e^r-1-r\le r^2$ for sufficiently small $r$. For $x\ge0$, $|e(hx)-1|\le\min(2,2\pi|h|x)\ll_h x^s$ uniformly in $0<s<1$. Beyond $M$, the bound $\tau(n+j)\le n+j$ gives a deterministic real tail $O(N2^{-M})$. Finally the terms up to $n$ in $2^nE$ are integers. Multiplying the three unit phases and using the triangle inequality proves the localization.

**What remains.** For binary normality, it now suffices, and is necessary, that the localized signed sums are $o(N)$ on $N\le n<2N$ for every fixed odd $h$. A vanishing prefix mean gives the doubling-interval mean by subtraction. Conversely repeatedly halve a prefix, discarding at most one endpoint at each halving and a bounded initial segment, to recover the prefix $o(N)$ bound. Even frequencies are shifts of odd ones. Demanding cancellation on every shorter window would be a stronger condition. No rate of decay for the signed sum inside the retained band has been established here. In particular, treating the $\tau(n+j)$ as independent misses divisibility and real carries. [Repository Fourier criterion](../../NormalityChecker/FourierTest.lean) · [Exact doubling and odd-frequency sufficiency](../../NormalityChecker/Correlations.lean)

## A checked transfer from one word to a Fourier deficit

For an odd integer $h$ choose $k$ with $2^k\ge2\pi|h|$. Let $C$ count shifts $N\le n<N+H$ at which the length-$k$ word consisting of a one followed by zeros begins. Define $z_n=e(h2^nE)$. The finite inequality proved in Lean is

```math
2\left|\sum_{N\le n<N+H}z_n\right|\le 2H+2-C.
```

At every counted start the shifted fractional part lies in $[1/2,1/2+2^{-k})$. Since $e(h/2)=-1$, one has $|1+z_n|\le2\pi|h|2^{-k}\le1$. The doubling identity $z_{n+1}=z_n^2$ then gives $|z_n+z_{n+1}|\le1$ there, and the trivial bound is 2 elsewhere. Summing the pairs differs from twice the original sum by just two endpoint phases. This argument applies for every real number. The file specializes it to the literal Lambert series for $E$. [Lean statement and proof](../../NormalityChecker/ErdosBorweinFourier.lean)

On prefixes the elementary release gives, for this word and every sufficiently large $N$, an upper bound $1+1/N-\tfrac12\exp[-70000(\log\log N)^3]$ on the normalized Fourier norm. Using the November word count on its windows instead gives $1+1/H-c_{a,w}/2$. A wholly contained occurrence is eligible for the Lean count even though Lean also admits the last $k-1$ starts. In conjunction with the unconditional localization, the latter bound passes to the sum on $J_N$ with an extra $O_{\delta,h}(T^{-3})$. It gives a strict gap below one for each fixed nonzero frequency because for $h=2^v h_0$ shifting by $v$ changes the normalized sum by at most $2v/H$. To deduce normality one would need a limit of zero. No formal import of a different Lean toolchain or unproved short-interval theorem is used. [Elementary archive][elementary] · [November theorem][mira]

## Reproduction

In this checkout run the following commands. The note's Lean file is standalone so it can be checked without changing the library, the global declaration index or the manuscripts.

```sh
lake build
lake env lean NormalityChecker/ErdosBorweinFourier.lean
python3 scripts/portal.py check
```

The transfer prints exactly `propext`, `Classical.choice`, and `Quot.sound`. For the external elementary package the audit here checked the ZIP, the 43 listed file hashes, theorem types and the archived axiom reports. The upstream record reports 27 compiled modules and 40 axiom reports under Lean 4.33.1 / mathlib `0df444a360eaa60ab8c11dca51a86af692955474`. The local transfer was compiled with this repository’s Lean 4.36.0. The external 4.33.1 build was not rerun. [Elementary package][elementary]

```sh
curl -fLsS https://raw.githubusercontent.com/CaptainSude/erdos-borwein-disjunctivity-elementary/d51e93e91ff43efef6918efdd4258bbd43bad7aa/erdos-borwein-fully-verified-20260908.zip -o elementary.zip
sha256sum elementary.zip
# 2c4642a6d24c04fc4db418ba8342f41d56eee4610352ec0b140e89a414972d60
unzip -q elementary.zip
(cd erdos-borwein-fully-verified-20260908 && sha256sum -c SHA256SUMS)
```

For an independent finite check, after truncating at `L` the remaining sum times `2^L` is at most `L+2`, by the bound $\tau(m)\le m$. All the extracted prefixes below agree at the two enclosure endpoints. The four-bit word `1000` occurs at 258 of the first 4096 starts, and counts across all sixteen words range from 198 to 305. The first Fourier norm divided by 4096 is approximately 0.03450754. The exponential computation uses ordinary floating point. The digits and midpoint counterexample use integer arithmetic. These finite checks do not estimate a limiting frequency.

```python
from cmath import exp, pi
from math import isqrt
from collections import Counter

N, k, L = 4096, 4, 4200
tau = [0] * (L + 1)
for d in range(1, L + 1):
    for m in range(d, L + 1, d):
        tau[m] += 1
num = 0
for d in tau[1:]:
    num = 2*num + d

def prefix(n):
    lower = num >> (L-n)
    assert lower == (num+L+2) >> (L-n)
    return lower

def word(n, k):  # n digits skipped
    return prefix(n+k) % (1 << k)

counts = Counter(word(n,k) for n in range(N))
print("word 1000, all four-bit counts:", counts[8], min(counts.values()), max(counts.values()))
for p in range(17,75):
    if all(p%d for d in range(2,isqrt(p)+1)):
        n = 16*p-3  # n is the one-based first place for this marker
        assert tau[n+3] == 10
        if word(n-1,2) != 2:
            print("marker, actual word:", (p,n), format(word(n-1,2),'02b'))
            break
z = sum(exp(2j*pi*word(n,48)/2**48) for n in range(N))
print("first Fourier norm:", round(abs(z)/N, 8))
assert abs(z) + 2*pi*N/2**48 <= N+1-counts[8]/2
```

[mira]: https://github.com/Mira-Cult/math/blob/149831943806a656c9efaa14cacbd9c915b2a2ba/notes/number-theory/normal-numbers/erdos-borwein-positive-word-density/README.md
[miraverify]: https://github.com/Mira-Cult/math/blob/149831943806a656c9efaa14cacbd9c915b2a2ba/notes/number-theory/normal-numbers/erdos-borwein-positive-word-density/VERIFICATION.md
[original]: https://github.com/Mira-Cult/math/commit/a74afd540a6401026e7789a3734ce1492f823065
[archive]: https://github.com/Mira-Cult/math/tree/357d26a23fbbee5c900098938744ab732b84d03a
[rh]: https://github.com/Mira-Cult/rh
[gist1]: https://gist.github.com/Mira-acc/ea2791119de611279237096e35cbc976/d699a69c2037ee4420bfb8e1e0ad0b310bbc8eb0
[gist2]: https://gist.github.com/Mira-acc/79be9a5d4aa54a9df41e702c4f3113ea/41b5a780f79f7bdd275cd96e7e310b000a897d35
[elementary]: https://github.com/CaptainSude/erdos-borwein-disjunctivity-elementary/tree/d51e93e91ff43efef6918efdd4258bbd43bad7aa
[capmain]: https://github.com/CaptainSude/erdos-borwein-disjunctivity/blob/bd98789a177470cc4b3e33e6769e859f6144c906/lean/ErdosBorwein/Main.lean
[capinputs]: https://github.com/CaptainSude/erdos-borwein-disjunctivity/blob/bd98789a177470cc4b3e33e6769e859f6144c906/lean/ErdosBorwein/PrimeInputs.lean
[cappaper]: https://github.com/CaptainSude/erdos-borwein-disjunctivity/blob/bd98789a177470cc4b3e33e6769e859f6144c906/paper/erdos-borwein-disjunctivity.tex
[power]: https://github.com/CaptainSude/generalized-Lambert-disjunctivity-and-nonnormality/blob/fe33be210446c6c0b127ca7757fc8f1182c5b541/lean/PowerLambert/Results.lean
[erdos]: https://users.renyi.hu/~p_erdos/1948-04.pdf
[van]: https://arxiv.org/pdf/1206.0340v1
[agp]: https://doi.org/10.2307/2118576
[bc]: https://www.davidhbailey.com/dhbpapers/bcnormal-em.pdf
[crandall]: https://math.colgate.edu/~integers/m23/m23.pdf
[campbell]: https://arxiv.org/pdf/2605.24160v1
[hi]: https://doi.org/10.1112/S0025579300006069
[pps]: https://www.numdam.org/item/ASNSP_1984_4_11_4_529_0.pdf
[shiu]: https://gdz.sub.uni-goettingen.de/id/PPN243919689_0313?tify=%7B%22pages%22%3A%5B167%5D%7D
[henriot]: https://arxiv.org/pdf/1102.1643v1
[outline]: https://github.com/Mira-Cult/math/blob/149831943806a656c9efaa14cacbd9c915b2a2ba/notes/number-theory/normal-numbers/erdos-borwein-positive-word-density/proof.md
[adaptive]: https://github.com/Mira-Cult/math/blob/149831943806a656c9efaa14cacbd9c915b2a2ba/notes/number-theory/normal-numbers/erdos-borwein-positive-word-density/adaptive-marker-count.md
[inc]: https://github.com/Mira-Cult/math/blob/149831943806a656c9efaa14cacbd9c915b2a2ba/notes/number-theory/normal-numbers/erdos-borwein-positive-word-density/fixed-word-incidences.md
[weighted]: https://github.com/Mira-Cult/math/blob/149831943806a656c9efaa14cacbd9c915b2a2ba/notes/number-theory/normal-numbers/erdos-borwein-positive-word-density/weighted-local-comparison.md
[isolate]: https://github.com/Mira-Cult/math/blob/149831943806a656c9efaa14cacbd9c915b2a2ba/notes/number-theory/normal-numbers/erdos-borwein-positive-word-density/conditional-isolation.md
[marked]: https://github.com/Mira-Cult/math/blob/149831943806a656c9efaa14cacbd9c915b2a2ba/notes/number-theory/normal-numbers/erdos-borwein-positive-word-density/marked-tail.md
[integrated]: https://github.com/Mira-Cult/math/blob/149831943806a656c9efaa14cacbd9c915b2a2ba/notes/number-theory/normal-numbers/erdos-borwein-positive-word-density/integrated-deficit.md
[atoms]: https://github.com/Mira-Cult/math/blob/149831943806a656c9efaa14cacbd9c915b2a2ba/notes/number-theory/normal-numbers/erdos-borwein-positive-word-density/valuation-atom-bound.md
