# Reviewer packet

Christopher Anderson · Independent Researcher\
*Denominator Growth and Rational Shadowing for Classical Constants*, version 2.0

## Theorem A · Balanced trace denominator rates

**Statement.** A source is a monic integer polynomial $f$ whose roots have the form $2^{a/e}\zeta$, with a common nonnegative rational $a/e$ and with roots of unity $\zeta$. For an integer $t>a/e$, define
$$
S_{f,t}(x)=\sum_{1\le j\le x/(t-a/e)}
\frac{\sum_{f(\alpha)=0}\alpha^j}{j2^{tj}},
$$
counting roots with multiplicity. Let $S$ be a fixed finite rational linear combination with $S(\infty)=\log 2$. Then $Y_N=2^NS(N)$ has error $O((N+1)^{-1})$ from $2^N\log 2$. The limit of $\log\operatorname{den}(Y_N)/N$ exists and its two smallest possible values are $5/12$ and $13/30$, each at a unique prefix function. The minimum in the real class with normalized roots $\pm 2^{-k}$, $k\ge1$, is $1/2$, again unique.

**Evidence.** Lean-supported paper proof. Lean verifies the finite mass comparison and supporting Gaussian arithmetic. The cutoff classification, prime-band asymptotics and primitive-divisor descent have written proofs. [Finite Lean certificate](https://github.com/eldernos/MathematicsResearch/blob/e4809cf561573aef588e6ffc491a35cdb79fd9ec/NormalityChecker/AdaptiveLogarithmBounds.lean#L1158) · [Verification map](../VERIFICATION.md)

**Proof sketch.** Over the field of all roots of unity the Galois group of $2^{1/e}$ acts by a subgroup of the $e$th roots of unity. Its fixed power has exponent denominator at most two, since an Eisenstein real radical $2^{1/m}$ for $m>2$ generates a nonnormal field, while finite subfields of the cyclotomic closure are Galois. The resulting group order is $e$ for odd $e$ and $e/2$ for even $e$. Each irreducible factor is therefore a polynomial in $X^r$ for that order $r$. Reindexing the trace by multiples of $r$ preserves the cutoff. At the remaining half-integral radius, Möbius inversion on roots of unity and the sign character of $\sqrt2$ modulo eight give integral combinations of the $A_k$ and $G_t$ of §2 at every cutoff. Geometric summation gives the stated tail.

For odd $p$ larger than the coefficient-denominator primes and with $p^2>2N$, multiplication of the prefix by $p$ reduces modulo $p$ to $2^NS(N/p)$ by Fermat and Gaussian Frobenius. On $2N/(v+1)<p\le2N/v$ the short sum has the constant value $S(v/2)$. Each nonzero sum loses only finitely many numerator primes. Hadamard's prime number theorem gives the normalized contribution $2/[v(v+1)]$. The remaining bands have arbitrarily small weight and prime powers beyond the first cost $o(N)$.

After sign pairing, a largest real stride $h>6$ is eliminated by a prime of order $h$ from Bang–Zsigmondy. If a Gaussian stride with odd norm index $n\ge7$ is present at height $4n$, use Grechkoseeva's two primitive primes in $2^n\pm2^{(n+1)/2}+1$. The plus factor eliminates any real coefficient at $4n$, and the minus factor eliminates the Gaussian coefficient. Valuations at the remaining primes give the four-parameter family in Eq. (1). The certificate bounds the first 71 weights below by $13/30$ outside $(0,0,0,-5)$ and $(0,0,0,-2)$, which have weights $7/18$ and $73/180$. Direct evaluation up to cutoff 9 and the geometric tail give positivity on both exceptional tails, adding exactly $1/36$. For any other parameter the nonzero limit gives positive mass beyond the first 71 cells. The real coordinate at stride one either vanishes or incurs mass $1/2$ before cutoff two and positive mass later.

**External inputs and reproduction.** Bang, 1886, pp. 70–80 and Zsigmondy, 1892, §XII, pp. 282–283, for base pair $(2,1)$. Grechkoseeva, corrected Theorem 2, PDF p. 2, with parameters $(2,4,n)$. Hadamard, 1896, §19, p. 219, modulus 1. Run `python3 -B scripts/phase16_adaptive_log.py` from the checkpoint to reproduce the 71-cell comparison. [Bang archive](https://www.jstor.org/stable/24539988) · [Zsigmondy](https://doi.org/10.1007/BF01692444) · [Grechkoseeva](https://arxiv.org/html/2504.04729v1) · [Hadamard](https://www.numdam.org/item/BSMF_1896__24__199_1/) · [Exact computation](https://github.com/eldernos/MathematicsResearch/blob/e4809cf561573aef588e6ffc491a35cdb79fd9ec/scripts/phase16_adaptive_log.py)

**Review requested.** Check the preservation of cutoffs under the cyclotomic reduction, especially the twist when the phase order has 2-adic valuation three. Check the descent at a height occupied by both a real and a Gaussian factor. Assess whether a shorter prior argument gives the same classification.

## Theorem 5.3 and Proposition 5.4 · Legendre models and rounding

**Statement.** Fix a finite integral pole identity $\log 2=\sum_i c_i\int_0^1(a_i-\sigma_i x)^{-1}dx$ with positive denominators, $a_i\ge1$ integral, and $\sigma_i=\pm1$. Put $z_i=|2\sigma_i a_i-1|$ and $\rho=\min_i(z_i+\sqrt{z_i^2-1})$ after combining equal poles and omitting zero coefficients. For every sufficiently large integer $N$ a rational algorithm returns $Y_N$ with reduced denominator dividing $L=\operatorname{lcm}(1,\ldots,D)$ and
$$
|2^N\log 2-Y_N|\le (2L)^{-1}+O(\rho^{-D}),\qquad
D/N\to1/\log_2\rho.
$$
For a fixed identity $\pi=\sum_i c_i\arctan(1/a_i)$ with $a_i\ge2$ integral and $c_i$ integral, put $\rho=\min_i(a_i+\sqrt{a_i^2+1})$ over nonzero terms. The construction gives a reduced denominator dividing $L=\operatorname{lcm}(1,3,\ldots,2D-1)$, shifted error at most $(2L)^{-1}+O(\rho^{-2D})$ and $D/N\to1/(2\log_2\rho)$. In both cases $\limsup N^{-1}\log\operatorname{den}(Y_N)\le\log 2/\log\rho$ and $\liminf T_N/N\ge1/\log\rho$, where $T_N$ is the negative binary logarithm of shifted error. For target $\xi$ and scaled analytic residual $E$, the unrefined numerator equals the nearest integer to $L2^N\xi$ whenever its distance from half-integers exceeds $L|E|$. A rational refinement on the same grid terminates at the exact nearest integer for either target at every shift.

**Evidence.** Paper proof. Exact computations certify selected rounding decisions. [Verification map](../VERIFICATION.md)

**Proof sketch.** Divide the relevant shifted Legendre polynomial by each linear pole after subtracting its value at the pole. For $\pi$ first write $P_{2D}(x)=H_D(x^2)$ and divide by $y+a_i^2$ in $y=x^2$. Choose the first degree for which all absolute pole values reach $2^N$. Laplace's formula gives log growth $(\log\rho+o(1))D$ for real poles and $(2\log\rho+o(1))D$ for the even kernel at imaginary poles. The resulting first crossings have the stated ratios. The Chebyshev expansion of each pole denominator has tail $O(\rho^{-D})$, or $O(\rho^{-2D})$ in the even case, after dropping the polynomial part killed by Legendre orthogonality. Exact moment weights have gcd one, so rounding the rational integral to the nearest multiple of $1/L$ is attainable by an integer polynomial. A grid numerator can change only if the analytic perturbation reaches a half-integer. Holding the original grid fixed, increasing the kernel degree gives arbitrarily small rational error enclosures. Irrationality guarantees eventual strict containment in a rounding cell.

**External inputs and reproduction.** DLMF Table 18.3.1 and Eq. 18.10.5, Hadamard §19, p. 219, and the irrationality of $\log 2$ and $\pi$ as in Alladi–Robinson, §1, pp. 137–139, and Hata, Theorem 1.1, p. 336. Run `python3 -B scripts/phase17_classical_approximants.py` and `python3 -B scripts/phase18_classical.py`. [Orthogonality](https://dlmf.nist.gov/18.3#T1) · [Laplace integral](https://dlmf.nist.gov/18.10.E5) · [Hadamard](https://www.numdam.org/item/BSMF_1896__24__199_1/) · [Alladi–Robinson](https://doi.org/10.1515/crll.1980.318.137) · [Hata](https://doi.org/10.4064/aa-63-4-335-349) · [Logarithm script](https://github.com/eldernos/MathematicsResearch/blob/e4809cf561573aef588e6ffc491a35cdb79fd9ec/scripts/phase17_classical_approximants.py) · [π script](https://github.com/eldernos/MathematicsResearch/blob/e4809cf561573aef588e6ffc491a35cdb79fd9ec/scripts/phase18_classical.py)

**Review requested.** Check whether the prescription of the scale before choosing the degree has a direct Padé antecedent. Check the first crossing for imaginary poles and the rounding test. The denominator conclusion gives upper bounds, and the window and finite numeral checks leave limiting digit distribution open.

Independent human specialist review is outstanding. [Manuscript](../paper.pdf) · [Literature ledger](../LEDGER.md)

The manuscript also includes a written exact-completion theorem for a single prime, a mean loss bound, a period lower bound excluding full-period sampling on polynomial windows, and exact numerical discrepancies of individual Taylor rows. The [follow-up proof and verification record](https://github.com/eldernos/MathematicsResearch/blob/c2c9da683666b3b9368e5d4b5cb858caccf528f5/notes/phase19/verification.md) identifies the supporting finite checks.
