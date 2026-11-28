# Constructive normality, reciprocal spectra and the bounded continued-fraction cap (Phase 26, Track E)

**Headline (Paper proof + Finite certificate).** The cap in the computable badly approximable polynomial-normal construction of [GF-46](../phase25/nonlinear-and-badly-approx.md) comes down from *M* = 42 to **14** with no external input, and from *M* = 14 to **8** with the Weil–Estermann input. Both caps are optimal for their regimes, apart from *M* = 13 in the elementary regime, which remains open. More precisely, there are Turing-computable reals *x* with every partial quotient at most 8 (respectively 14) such that *P*(*x*) is absolutely normal for every nonconstant *P* ∈ ℚ[*X*], with *q*‖*qx*‖ > 1/10 (respectively 1/16) for every *q* ≥ 1. The new ingredient is a transfer-operator certificate for long block measures (*L* = 226 and *L* = 344). An exact barrier shows that the two-block large-sieve bookkeeping of GF-46 Theorem 2.3 cannot reach *M* ≤ 7 in the Weil regime, *M* ≤ 12 in the elementary regime, or *M* ≤ 4 under any Kloosterman exponent. Reaching the existence cap *M* = 2 of Kaufman (1980) and Queffélec–Ramaré (2003) therefore needs a different Fourier-decay mechanism.

On the reciprocal side (E1), a multiplier calculus covers both known constructions: the band regime of GF-34/E1 and the coprime fold of GF-45. A cyclotomic congruence theorem (E1.3A) shows that for every *g* ≥ 3 the identity is the only periodic band operation whose reciprocal multipliers are all ≡ 1 (mod *g*). So in radix *b* ≥ 4 no nontrivial band operation preserves the reciprocal orbit, and for *D* ≥ 3 with *D* ∣ *b* − 1 none preserves δ<sub>*r*/*D*</sub>. Every fold applies the multiplier 2 on its fold bands and removes near-*r*/*D* mass in proportion to its ratio (Lemma E1.3C). Hence, in the regime where GF-45's cycle comparison is used, neither mechanism can realize δ<sub>*r*/*D*</sub> for *D* ≥ 3 (Proposition E1.3D), and the cut-and-fold programme of realizing every rational-orbit mixture fails as posed. For *g* = 2 the answer is different. In radix 3 the factor Φ<sub>6</sub>/Φ<sub>3</sub> preserves δ<sub>1/2</sub> on every band and still contracts *x*, with exact cycle means 0.3000 → 0.1975 → 0.1590 → 0.1401 (Example E1.3B). There only the zero-band obstruction survives, and the radix-3 target δ<sub>1/2</sub> stays open. The new positive results for reciprocal spectra are exact frequency sums at the cylinders adjacent to 0, transfer of the GF-45 spectrum to any fixed power radix *b*<sup>*k*</sup>, and Liouville witnesses.

> **Cross-model review is not independent human peer review.** Nothing in this note changes a benchmark status. Its results concern constructed numbers, not the classical constants `BC-01`…`BC-50`.

## 0. Notation, scope and evidence

*T*<sub>*b*</sub>*t* = *bt* mod 1. ν<sub>*N*</sub>(*z*; *b*) is the orbit measure of the first *N* points. ‖·‖ is the distance to ℤ. *M*<sub>*b*</sub> = {*z* : *N*<sup>−1</sup>Σ<sub>*n*<*N*</sub>‖*b*<sup>*n*</sup>*z*‖ → 0} ⊂ *K*<sub>*b*</sub>. μ<sub>α</sub> = αδ<sub>0</sub> + (1 − α)λ. For a rational *r* = *A*/*D* with gcd(*D*, *b*) = 1, μ(*r*; *b*) is the uniform measure on its periodic orbit. *U*<sub>*D*</sub> is the uniform measure on (1/*D*)ℤ/ℤ. *F*<sub>*M*</sub> is the set of reals in (0, 1) with all partial quotients at most *M*. Σ(*M*, *L*, *s*) = Σ<sub>**u**∈{1..*M*}<sup>*L*</sup></sub>(*q*<sub>*L*</sub>(**u**) + *p*<sub>*L*</sub>(**u**))<sup>−2*s*</sup> is the block sum of GF-46 Lemma 2.2. ℛ<sub>*b*</sub> is the set of weak limits of ν<sub>*N*</sub>(1/*x*; *b*) over irrational *x* ∈ *M*<sub>*b*</sub>, with convergence along all *N*.

| Item | Result | Label | Objectives |
|---|---|---|---|
| E1.1 | Support lemma: limit points supported in (1/*D*)ℤ/ℤ ⇔ *Dy* ∈ *M*<sub>*b*</sub> | Paper proof | 3 |
| E1.2 | Exact band-multiplier calculus; Kronecker classification *G* = ∏Φ<sub>*d*</sub><sup>±1</sup> | Paper proof + Finite certificate | 3, 4 |
| E1.3 | Multiplier rigidity: mod-*g* theorem, cyclotomic congruence (*G* = 1 is the only solution of *G* ≡ 1 mod *g* for *g* ≥ 3), fold mass bound, the *D* ∣ *b* − 1 corollary for *D* ≥ 3, and an exact contracting example at *g* = 2 | Paper proof + Finite certificate | **4** |
| E1.4 | *f*(0<sup>*L*</sup>) + *f*((*b*−1)<sup>*L*</sup>) → α + 2(1 − α)*b*<sup>−*L*</sup> for GF-45 witnesses | Paper proof | 3 |
| E1.5 | *M*<sub>*b*</sub> = *M*<sub>*b*<sup>*k*</sup></sub>; for each fixed *k*, GF-45 witnesses with ν<sub>*N*</sub>(1/*x*; *b*<sup>*k*</sup>) → μ<sub>α</sub> | Paper proof + Finite certificate | 2, 3 |
| E1.6 | μ(1/*x*) = μ(*x*); Liouville witnesses; *M*<sub>*b*</sub> ∩ Bad ≠ ∅ | Paper proof; External input (Shallit 1979) | 3 |
| E2.1 | Transfer identity Σ(*M*, *L*, *s*) = (𝓛<sub>*s*</sub><sup>*L*</sup>1)(1) and the eigenfunction certificate | Paper proof + Finite certificate | infrastructure |
| **E2.2** | **Computable caps *M* = 14 (elementary) and *M* = 8 (Weil–Estermann)** | Paper proof + Finite certificate (+ Weil 1948, Estermann 1961 for *M* = 8) | **1, 3** |
| E2.3 | Barriers: *M* ≤ 7 (Weil regime), *M* ≤ 12 (elementary regime), *M* ≤ 4 (every ρ ≥ 0) | Paper proof + Finite certificate | **4** |
| E3 | Fix for Audit IV G1; alphabet-size trade-off | Paper proof + Finite certificate | 4 |
| E4 | Representation lemma: persistent all-prime support carries no intrinsic content | Paper proof | 3, 4 |
| E5 | Toeplitz determinants: Szegő limit, mixture bound, and the sandwich det ↔ *L*<sup>2</sup> Fourier mass | Paper proof + Finite certificate | 3, 4 |

---

## E1. The inverse measure-realization problem

### E1.0 Prior state

ℛ<sub>*b*</sub> ⊇ {μ<sub>α</sub> : 0 ≤ α ≤ 1} for every *b* ([GF-45](../phase25/partitions-and-reciprocals.md); Audit III passed with no Critical or Major findings). Also ℛ<sub>*b*</sub> ∋ μ(*r*; *b*) whenever 2 ∈ ⟨*b*⟩ (mod *D*) ([GF-34](../phase23/convergent-reciprocals-and-schedules.md) Theorem 1). The brief asks for every finite mixture Σ*c*<sub>*j*</sub>μ(*r*<sub>*j*</sub>; *b*) + *c*<sub>0</sub>λ, or even every *T*<sub>*b*</sub>-invariant μ.

**Answer.** This note neither settles the general inverse problem nor finds a necessary condition for *x* ∈ *M*<sub>*b*</sub> proper. GF-45 already shows that no atom at 0 is required, since μ = λ occurs. What it proves (E1.3) is that **every operation of both known mechanisms obeys a multiplier rigidity**. In particular, in the regime where GF-45's cycle comparison is used, the rational-anchor cut-and-fold programme cannot produce the laws δ<sub>*r*/*D*</sub> with *D* ∣ *b* − 1, *D* ≥ 3 and gcd(*r*, *D*) = 1 (Proposition E1.3D). For *D* = 2 the band mechanism is not excluded (Example E1.3B). The cleanest open case is radix 3: is there an irrational *x* ∈ *M*<sub>3</sub> such that the base-3 digits of 1/*x* are 1 with density one? Conjecture E1.C below predicts no, but no result here rules it out.

**On the shadowing heuristic in the brief.** Suppose *b*<sup>*n*</sup>*x* = *A* + ε with |ε| ≤ *b*<sup>−*g*</sup>. Then *y* = 1/*x* tracks the rational *b*<sup>*n*</sup>/*A* only for the times *j* < *n* + *g* − *O*(1). That rational's orbit is the periodic orbit of 1/*A*′, where *A*′ is the prime-to-*b* part of *A*, and its period ord<sub>*A*′</sub>(*b*) is in general far longer than the window. Choosing *A* therefore does not by itself make *y* shadow a fixed orbit *r*/*s*. The correct reformulation is E1.1: *y* shadows (1/*s*)ℤ/ℤ exactly when *sy* ∈ *M*<sub>*b*</sub>. So "*x* ∈ *M*<sub>*b*</sub> while 1/*x* stays near *r*/*s* for a proportion *c* of the time" is a **joint** condition on the pair (*x*, *s*/*x*), and E1.3 is about that joint condition.

### E1.1 Support lemma (Paper proof)

Let gcd(*D*, *b*) = 1 and let *y* be real. Every weak limit point of ν<sub>*N*</sub>(*y*; *b*) is supported in (1/*D*)ℤ/ℤ if and only if *Dy* ∈ *M*<sub>*b*</sub>.

*Proof.* ‖*Dt*‖ ≤ *D*·dist(*t*, (1/*D*)ℤ), and conversely dist(*t*, (1/*D*)ℤ) = ‖*Dt*‖/*D*. Average over the orbit and use weak compactness. ∎

For example, a law μ(*r*; *b*) with *r* = *A*/*D* forces both *x* ∈ *M*<sub>*b*</sub> and *D*/*x* ∈ *M*<sub>*b*</sub>. The residue process round(*b*<sup>*n*</sup>*Dy*) mod *D* then decides which orbits in (1/*D*)ℤ/ℤ are visited.

### E1.2 Exact band-multiplier calculus (Paper proof; certificate §E1)

Let *y* be rational with eventual period *P*<sub>*y*</sub> ∣ *l* and preperiod *a* < *l*, let *u* = *b*<sup>−*l*</sup>, and let *G*(*u*) = Σ*g*<sub>*i*</sub>*u*<sup>*i*</sup> ∈ ℤ⟦*u*⟧ with *G*(0) = 1 and bounded coefficients. Define the band multipliers by

```math
S(u)=\frac{G(u)}{1-u},\qquad T(u)=\frac{1}{(1-u)\,G(u)},\qquad\text{so}\qquad \sum_{i\le j}S_iT_{j-i}=j+1 .
```

**(a) Band tracking.** Let *y* > 0 and *x* = 1/*y* both have base-*b* preperiod at most *a* and eventual periods *P*<sub>*y*</sub>, *P*<sub>*x*</sub> dividing *l*. Let |*g*<sub>*i*</sub>| ≤ *C*<sub>*G*</sub>, and assume that the coefficients *h*<sub>*i*</sub> of 1/*G* are bounded as well, |*h*<sub>*i*</sub>| ≤ *C*<sub>1/*G*</sub>. Both bounds hold in the Kronecker class of (b). Then for *n* = *jl* + *m* with *a* ≤ *m* < *l*,

```math
\big\|\,b^n y\,G(u)-S_j\{b^n y\}\,\big\|\le 2C_G\,y\,b^{m-l},
\qquad
\big\|\,b^n x/G(u)-T_j\{b^n x\}\,\big\|\le 2C_{1/G}\,x\,b^{m-l},
```

where ‖·‖ is the distance to the nearest integer. On the part *m* < *l* − *H* of each band the error is therefore at most 2*C*<sub>*G*</sub>*y**b*<sup>−*H*</sup> (respectively 2*C*<sub>1/*G*</sub>*x**b*<sup>−*H*</sup>); *H* is a free margin, chosen before *l*. The statement is a congruence modulo 1. Near the wrap-around point 0 ≡ 1 the two fractional parts can differ by almost 1 as real numbers: for *b* = 3, *x* = 2, *G* = 1 + *u*, *l* = 4 and *n* = 1 one has {3*x*/*G*(*u*)} = 38/41 while *T*<sub>0</sub>{3*x*} = 0, at circle distance 3/41. *Proof.* Write *b*<sup>*n*</sup>*yG* = Σ*g*<sub>*i*</sub>*b*<sup>*m*+(*j*−*i*)*l*</sup>*y*. For *i* ≤ *j* the exponent is at least *m* ≥ *a*, so each term is ≡ *b*<sup>*m*</sup>*y* ≡ *b*<sup>*n*</sup>*y* (mod 1) by periodicity. Since *S*<sub>*j*</sub> = Σ<sub>*i*≤*j*</sub>*g*<sub>*i*</sub> is an integer, these terms add up to *S*<sub>*j*</sub>{*b*<sup>*n*</sup>*y*} modulo 1. The terms with *i* > *j* have total size at most *C*<sub>*G*</sub>*y**b*<sup>*m*</sup>/(*b*<sup>*l*</sup> − 1) ≤ 2*C*<sub>*G*</sub>*y**b*<sup>*m*−*l*</sup>. The same computation with *h*<sub>*i*</sub> and *T*<sub>*j*</sub> = Σ<sub>*i*≤*j*</sub>*h*<sub>*i*</sub> gives the second bound. ∎ The script checks both bounds exactly at 1 280 positions (640 per coordinate, every *m* < *l*) on nine rational pairs in radices 2, 3, 5, 7 and 10, and checks the wrap-around example.

**(b) Kronecker classification.** Both *S* and *T* are bounded and eventually periodic if and only if *G* = ∏<sub>*d*≥2</sub>Φ<sub>*d*</sub>(*u*)<sup>ε<sub>*d*</sub></sup> with ε<sub>*d*</sub> ∈ {−1, 0, 1}, finitely many nonzero.

*Proof.* If *S* = *A*(*u*)/(1 − *u*<sup>*N*</sup>) and *T* = *B*(*u*)/(1 − *u*<sup>*N*′</sup>) with *A*, *B* polynomials, then *AB* = Π<sub>*N*</sub>Π<sub>*N*′</sub>, where Π<sub>*N*</sub> = (1 − *u*<sup>*N*</sup>)/(1 − *u*). So *A* divides a product of cyclotomic polynomials, and by unique factorization *A* = ±∏Φ<sub>*d*</sub><sup>*a*<sub>*d*</sub></sup>. Simple poles of *S* and *T* at roots of unity force |ε<sub>*d*</sub>| ≤ 1. The factor Φ<sub>1</sub> cancels because *S* and *T* each have exactly a simple pole at *u* = 1. Conversely, the Φ<sub>*d*</sub> with *d* ≥ 2 are distinct irreducible factors of 1 − *u*<sup>*N*</sup> for every multiple *N* of *d*, and they are coprime to 1 − *u*. So for *G* = ∏Φ<sub>*d*</sub><sup>ε<sub>*d*</sub></sup> the denominator (1 − *u*)∏<sub>ε<sub>*d*</sub>=−1</sub>Φ<sub>*d*</sub> of *S* divides 1 − *u*<sup>*N*</sup> with *N* = lcm{*d* : ε<sub>*d*</sub> = −1}, and the denominator of *T* divides 1 − *u*<sup>*N*′</sup> with *N*′ = lcm{*d* : ε<sub>*d*</sub> = 1} (an empty lcm is 1). Hence *S* = *A*/(1 − *u*<sup>*N*</sup>) and *T* = *B*/(1 − *u*<sup>*N*′</sup>) with polynomials *A* and *B*, and both are bounded and eventually periodic. The coefficients of *G* and 1/*G* are bounded as well, being differences of consecutive *S*<sub>*j*</sub> or *T*<sub>*j*</sub>. ∎ This is the classification behind the heuristic remark in GF-34 §1, now proved.

**(c) The y-band laws.** On band *j* the reciprocal cycle law becomes (×*S*<sub>*j*</sub>)<sub>∗</sub>σ<sub>*y*</sub> and the *x* cycle law becomes (×*T*<sub>*j*</sub>)<sub>∗</sub>σ<sub>*x*</sub>. The eventual averages satisfy *S̄* = *G*(1) and *T̄* = 1/*G*(1). The operation Op(*c*, *l*) of GF-34, with *G* = Π<sub>*c*</sub>, has *T* = 𝟙[*c* ∣ *j*] and the forced transient *S*<sub>*j*</sub> = min(*j* + 1, *c*). Indeed, any run *T*<sub>1</sub> = ⋯ = *T*<sub>*c*−1</sub> = 0 forces *S*<sub>*j*</sub> = *j* + 1 for *j* < *c*.

### E1.3 Multiplier rigidity (Paper proof + Finite certificate; Objective 4)

A *periodic band operation* is a factor *G* in the Kronecker class of E1.2(b). These are exactly the operations whose band multipliers *S* and *T* are bounded and eventually periodic; GF-34's Op(*c*, *l*) and every example below are of this kind. Write *G* ≡ 1 (mod *g*) when *G* − 1 ∈ *g*ℤ⟦*u*⟧. Since *S* = *G*/(1 − *u*), this holds if and only if *S*<sub>*j*</sub> ≡ 1 (mod *g*) for every *j* ≥ 0.

**Theorem E1.3A (cyclotomic congruence).** Let *G* = ∏<sub>*d*≥2</sub>Φ<sub>*d*</sub><sup>ε<sub>*d*</sub></sup> with ε<sub>*d*</sub> ∈ {−1, 0, 1}, finitely many nonzero.
1. If *g* ≥ 3 and *G* ≡ 1 (mod *g*), then *G* = 1.
2. *G* ≡ 1 (mod 2) if and only if *G* is a finite product, over distinct odd *m* ≥ 3, of factors (Φ<sub>*m*</sub>(*v*)/Φ<sub>*m*</sub>(−*v*))<sup>±1</sup> with *v* = *u*<sup>2<sup>*r*−1</sup></sup> and *r* = *r*(*m*) ≥ 1. The simplest one is Φ<sub>3</sub>(−*u*)/Φ<sub>3</sub>(*u*) = Φ<sub>6</sub>/Φ<sub>3</sub>.

*Proof.* Write *G* = *A*/*B*, where *A* and *B* are products of distinct cyclotomic polynomials with constant term 1. Then *G* ≡ 1 (mod *g*) if and only if *A* ≡ *B* in (ℤ/*g*ℤ)[*u*]. Every *g* ≥ 3 is divisible by 4 or by an odd prime, so part 1 reduces to *g* = *p*, an odd prime, and to *g* = 4.

Fix a prime *p*. Each *d* ≥ 2 is uniquely *p*<sup>*k*</sup>*m* with *k* ≥ 0, *p* ∤ *m* and (*k*, *m*) ≠ (0, 1); put ε<sub>1</sub> = 0. For *k* ≥ 1 the identities Φ<sub>*pm*</sub>(*u*) = Φ<sub>*m*</sub>(*u*<sup>*p*</sup>)/Φ<sub>*m*</sub>(*u*) and Φ<sub>*p*<sup>*k*</sup>*m*</sub>(*u*) = Φ<sub>*pm*</sub>(*u*<sup>*p*<sup>*k*−1</sup></sup>), together with Frobenius, give Φ<sub>*p*<sup>*k*</sup>*m*</sub> ≡ Φ<sub>*m*</sub><sup>(*p*−1)*p*<sup>*k*−1</sup></sup> (mod *p*). The Φ<sub>*m*</sub> with *p* ∤ *m* are distinct factors of the separable polynomial *u*<sup>*N*</sup> − 1 over 𝔽<sub>*p*</sub>, where *N* is their lcm and *p* ∤ *N*. So they have simple roots and no common roots in 𝔽̄<sub>*p*</sub>. Reading off the order of *G* mod *p* at a root of Φ<sub>*m*</sub> gives

```math
G\equiv 1 \pmod p \iff e_m=0 \ \ (p\nmid m),\qquad e_m=\varepsilon_m+(p-1)\sum_{k\ge 1}p^{k-1}\varepsilon_{p^k m}.
```

*Odd p.* Then *e*<sub>*m*</sub> = 0 forces ε<sub>*m*</sub> ≡ 0 (mod *p* − 1). Since *p* − 1 ≥ 2 and |ε<sub>*m*</sub>| ≤ 1, ε<sub>*m*</sub> = 0, and so Σ<sub>*k*≥1</sub>*p*<sup>*k*−1</sup>ε<sub>*p*<sup>*k*</sup>*m*</sub> = 0. If some ε<sub>*p*<sup>*k*</sup>*m*</sub> were nonzero, dividing by *p*<sup>*k*−1</sup> for the least such *k* would give ±1 ≡ 0 (mod *p*). Hence every ε<sub>*d*</sub> = 0 and *G* = 1.

*p = 2, and part 2.* For odd *m* the condition reads ε<sub>*m*</sub> + ε<sub>2*m*</sub> + Σ<sub>*k*≥2</sub>2<sup>*k*−1</sup>ε<sub>2<sup>*k*</sup>*m*</sub> = 0. For *m* = 1 the least-term argument again gives ε<sub>2<sup>*k*</sup></sub> = 0 for every *k*. For *m* ≥ 3, either ε<sub>*m*</sub> + ε<sub>2*m*</sub> = 0, and then the remaining sum vanishes, so ε<sub>2<sup>*k*</sup>*m*</sub> = 0 for *k* ≥ 2; or ε<sub>*m*</sub> = ε<sub>2*m*</sub> = ±1 and Σ<sub>*k*≥2</sub>2<sup>*k*−2</sup>ε<sub>2<sup>*k*</sup>*m*</sub> = ∓1. Solving the last equation digit by digit, the nonzero solutions are exactly ±(1, …, 1, −1) on (ε<sub>*m*</sub>, ε<sub>2*m*</sub>, …, ε<sub>2<sup>*r*</sup>*m*</sub>) for some *r* ≥ 1, with all later entries zero. For odd *m* ≥ 3, ∏<sub>*k*<*r*</sub>Φ<sub>2<sup>*k*</sup>*m*</sub>(*u*) = Φ<sub>*m*</sub>(*u*<sup>2<sup>*r*−1</sup></sup>) and Φ<sub>2<sup>*r*</sup>*m*</sub>(*u*) = Φ<sub>*m*</sub>(−*u*<sup>2<sup>*r*−1</sup></sup>). So the *m*-component of *G* is (Φ<sub>*m*</sub>(*v*)/Φ<sub>*m*</sub>(−*v*))<sup>±1</sup>. Conversely every such factor is ≡ 1 (mod 2), because Φ<sub>*m*</sub>(−*v*) ≡ Φ<sub>*m*</sub>(*v*).

*g = 4.* Let *G* ≡ 1 (mod 4). By part 2, *G* = ∏<sub>*m*∈𝓜</sub>*G*<sub>*m*</sub> over a finite set 𝓜 of odd *m* ≥ 3, and each *G*<sub>*m*</sub> = 1 + 2*R*<sub>*m*</sub> with *R*<sub>*m*</sub> ∈ ℤ⟦*u*⟧. Then *G* ≡ 1 + 2Σ*R*<sub>*m*</sub> (mod 4), so Σ*R*<sub>*m*</sub> ≡ 0 (mod 2). Write Φ<sub>*m*</sub>(*u*) = *P*<sub>*m*</sub>(*u*<sup>2</sup>) + *u**Q*<sub>*m*</sub>(*u*<sup>2</sup>). Then *R*<sub>*m*</sub> = ±*v**Q*<sub>*m*</sub>(*v*<sup>2</sup>)/Φ<sub>*m*</sub>(∓*v*), with the upper signs for the exponent +1. Over 𝔽<sub>2</sub> one has *f*(*u*<sup>2<sup>*e*</sup></sup>) = *f*(*u*)<sup>2<sup>*e*</sup></sup>, so

```math
R_m\equiv\Big(\frac{u\,Q_m(u^2)}{\Phi_m(u)}\Big)^{2^{r-1}} \pmod 2 .
```

Here *Q*<sub>*m*</sub> ≢ 0 (mod 2). Otherwise Φ<sub>*m*</sub> ≡ *P*<sub>*m*</sub>(*u*)<sup>2</sup> would be a square, but Φ<sub>*m*</sub> is separable mod 2. Also deg *u**Q*<sub>*m*</sub>(*u*<sup>2</sup>) < φ(*m*) = deg Φ<sub>*m*</sub>, because φ(*m*) is even. So *R*<sub>*m*</sub> mod 2 is a nonzero rational function whose numerator has smaller degree than its denominator. It is not a polynomial, so it has a pole at some root ζ of Φ<sub>*m*</sub> in 𝔽̄<sub>2</sub>. Every other *R*<sub>*m*′</sub> has poles only at roots of Φ<sub>*m*′</sub>, and these differ from ζ. Therefore Σ*R*<sub>*m*</sub> has a pole at ζ, so it cannot vanish unless 𝓜 = ∅. Hence *G* = 1. ∎

The script checks the three ingredients exactly: 133 Frobenius congruences, 114 squarefreeness and 1 632 coprimality checks modulo *p* ∈ {2, 3, 5, 7}, and the odd parts *Q*<sub>*m*</sub> ≢ 0 (mod 2) for the 49 odd *m* < 100. It also runs an exhaustive search over all 3<sup>9</sup> = 19 683 exponent vectors on *d* = 2, …, 10. Modulo *q* ∈ {3, 4, 5, 6, 7, 8, 9, 12} only *G* = 1 survives; modulo 2 exactly the 9 vectors predicted by part 2 survive.

**Theorem E1.3.** Let *G* be a periodic band operation.
1. **Mod-*g* rigidity.** Let *g* ≥ 2. If *S*<sub>*j*</sub> ≡ 1 (mod *g*) for all *j*, then *T*<sub>*j*</sub> ≡ 1 (mod *g*) for all *j*. In particular no *x*-band is a zero band. *Proof.* Modulo *g*, *S* ≡ (1 − *u*)<sup>−1</sup>, and the identity *S*∗*T* = (*j* + 1) is triangular, so *T* ≡ (1 − *u*)<sup>−1</sup> by induction on *j*. ∎ (This part holds for every *G* ∈ ℤ⟦*u*⟧ with *G*(0) = 1.)
2. **Orbit-preserving band operations.** Suppose every *S*<sub>*j*</sub> is a power of *b*, *S*<sub>*j*</sub> = *b*<sup>*k*<sub>*j*</sub></sup>. On band *j* the new reciprocal orbit is then the old one shifted by *k*<sub>*j*</sub> steps, so its cycle law is unchanged on every band. Moreover *S*<sub>*j*</sub> ≡ 1 (mod *b* − 1).
   - *b* ≥ 4. Theorem E1.3A(1) with *g* = *b* − 1 ≥ 3 gives *G* = 1. The only orbit-preserving periodic band operation is the identity, and it leaves *x* unchanged.
   - *b* = 3. Part 1 with *g* = 2 makes every *T*<sub>*j*</sub> odd, so no *x*-band is a zero band. Nothing more is claimed. Within the family of Theorem E1.3A(2) with at most two components, odd *m* ≤ 15 and *r* ≤ 3, no factor has every *S*<sub>*j*</sub> a power of 3 (798 factors, each with an explicit witness band; Finite certificate). Whether such a factor exists at all is **Open**.
   - *b* = 2. The obstruction is empty. Besides E1's doubling (*S* = (1, 2, 2, …), *T* = (1, 0, 1, 0, …)), the factor *G* = Φ<sub>2</sub>Φ<sub>3</sub>/Π<sub>4</sub> = Φ<sub>3</sub>/Φ<sub>4</sub> has *S*-pattern (1, 2, 2, 1) and *T*-pattern (1, 0, 1), so it contracts by 2/3 (certificate). This is exactly why GF-45 had to leave the band regime for coprime periods.

   *Withdrawn argument.* An earlier draft claimed non-contraction for every *b* ≥ 3 through a "near-zero first moment" of the *x* cycle. That argument fails when |*T*<sub>*j*</sub>| > 1. Points with ‖*t*‖ ∈ (δ/|*T*<sub>*j*</sub>|, δ] leave the window [0, δ] under ×*T*<sub>*j*</sub>, so the bound does not iterate; and it is vacuous once max|*T*<sub>*j*</sub>| ≥ den(*x*), when the window contains no orbit point except 0. For *b* ≥ 4 it is no longer needed. For *b* = 3 only the zero-band statement remains.
3. **Fold multipliers.** In the GF-45 fold *F*′ = *F* + *w*/(*b*<sup>*m*</sup> − 1), a fold-band point is *b*<sup>*im*+*s*</sup>*F* + *b*<sup>*s*</sup>*F* = (1 + *b*<sup>*t*</sup>)*b*<sup>*s*</sup>*F* with *t* = *im* mod *P*<sub>*F*</sub>. The offsets *t* sweep the subgroup *g*ℤ/*P*<sub>*F*</sub>ℤ with *g* = gcd(*m*, *P*<sub>*F*</sub>), which **always contains *t* = 0**. Hence the fold-band law is the average over that subgroup of (×(1 + *b*<sup>*t*</sup>))<sub>∗</sub>σ. When *g* = 1 this average is σ∗σ, recovering GF-45; when *P*<sub>*F*</sub> ∣ *m* it is (×2)<sub>∗</sub>σ (2 301 subgroup checks).
4. **Corollary (the *D* ∣ *b* − 1 targets).** Let *D* ∣ *b* − 1 with *D* ≥ 2, and let gcd(*r*, *D*) = 1. Then (1/*D*)ℤ/ℤ consists of *T*<sub>*b*</sub>-fixed points, the multipliers that fix δ<sub>*r*/*D*</sub> are exactly the *S* ≡ 1 (mod *D*), and 1 + *b*<sup>*t*</sup> ≡ 2 (mod *D*) for every *t*. Call a band operation *δ<sub>*r*/*D*</sub>-preserving* when *S*<sub>*j*</sub> ≡ 1 (mod *D*) on every band *j* ≥ 0, that is, *G* ≡ 1 (mod *D*). Operations that preserve the law only on an initial run of bands are not covered.
   - (a) *D* ≥ 3. By Theorem E1.3A(1) the only δ<sub>*r*/*D*</sub>-preserving periodic band operation is *G* = 1, which does not move *x*.
   - (b) *D* = 2, so *b* is odd. Nontrivial δ<sub>1/2</sub>-preserving operations exist by Theorem E1.3A(2), and they **can contract *x*** (Example E1.3B). The claim of an earlier draft that "a band operation that preserves δ<sub>*r*/*D*</sub> never contracts *x*" is false at *D* = 2 and is withdrawn. What survives is part 1: every *T*<sub>*j*</sub> is odd, hence nonzero. So the denominator-independent contraction of Op(*c*, *l*), which sends a fixed proportion of bands to 0 through *T*<sub>*j*</sub> = 0, is unavailable. A band with *T*<sub>*j*</sub> ≠ 0 sends exactly the mass σ<sub>*x*</sub>((1/|*T*<sub>*j*</sub>|)ℤ/ℤ) to 0. For rational *x* with denominator prime to *b*, every orbit point has the same denominator den(*x*), so this mass is 1 if den(*x*) ∣ *T*<sub>*j*</sub> and 0 otherwise.
   - (c) Folds. A fold sends the δ<sub>*r*/*D*</sub>-mass on its fold bands to δ<sub>2*r*/*D*</sub> ≠ δ<sub>*r*/*D*</sub>. Lemma E1.3C quantifies this for approximate laws.
   - (d) Proposition E1.3D combines (a) and (c) for *D* ≥ 3. For *D* = 2 the band route is open.

**Example E1.3B (Finite certificate in exact arithmetic; reproduces the Track E review's counterexample).** Take *b* = 3, *D* = 2, *r* = 1, *y*<sub>0</sub> = 5/2 and *x*<sub>0</sub> = 2/5. Every orbit point {3<sup>*n*</sup>*y*<sub>0</sub>} equals 1/2, so its cycle law is δ<sub>1/2</sub> and *P*<sub>*y*</sub> = 1. The orbit of *x*<sub>0</sub> is {2/5, 1/5, 3/5, 4/5}, so *P*<sub>*x*</sub> = 4 and *M*(*x*<sub>0</sub>) = 3/10, where *M*(*z*) denotes the cycle mean of ‖3<sup>*n*</sup>*z*‖ for rational *z*. Apply

```math
G(u)=\frac{\Phi_6(u)}{\Phi_3(u)}=\frac{1-u+u^2}{1+u+u^2},\qquad S=(1,-1,1,1,-1,1,\dots),\qquad T=(1,3,5,5,3,1,\dots),
```

whose multipliers have period 6, at successive scales: *y*<sub>*k*</sub> = *y*<sub>*k*−1</sub>*G*(3<sup>−*l*<sub>*k*</sub></sup>) and *x*<sub>*k*</sub> = 1/*y*<sub>*k*</sub>, with *P*<sub>*x*<sub>*k*−1</sub></sub> and *P*<sub>*y*<sub>*k*−1</sub></sub> dividing *l*<sub>*k*</sub>. Every *S*<sub>*j*</sub> is odd, so ×*S*<sub>*j*</sub> fixes δ<sub>1/2</sub> on every band. Exact integer arithmetic gives the following cycle means (rounded here; each decrease is an exact rational inequality).

| Scales *l*<sub>1</sub>, *l*<sub>2</sub>, … | *M*(*x*<sub>0</sub>) → *M*(*x*<sub>1</sub>) → ⋯ | Contraction factors | Cycle mean of ‖3<sup>*n*</sup>*y*<sub>*k*</sub> − 1/2‖ |
|---|---|---|---|
| 8, 48, 288 | 0.3000 → 0.1975 → 0.1590 → 0.1401 | 0.658, 0.805, 0.881 | 0.0880, 0.1026, 0.1051 |
| 12, 72 | 0.3000 → 0.1983 → 0.1505 | 0.661, 0.759 | 0.0586, 0.0684 |

The last column measures how far the reciprocal cycle is from δ<sub>1/2</sub>. It comes from the tracking errors near the ends of the bands (E1.2(a)), which the multipliers ±1 neither enlarge nor remove; it is smaller for the larger first scale.

*Why x contracts.* In the error-free band calculus the *x*-law after one step is (1/6)Σ<sub>*j*<6</sub>(×*T*<sub>*j*</sub>)<sub>∗</sub>σ<sub>*x*</sub>. The cycle law of *x*<sub>0</sub> is ×3-invariant, and ×5 sends it to δ<sub>0</sub>. So the error-free laws are (2/3)<sup>*k*</sup>σ<sub>*x*<sub>0</sub></sub> + (1 − (2/3)<sup>*k*</sup>)δ<sub>0</sub>, with means (2/3)<sup>*k*</sup>·3/10 → 0. The actual factors are weaker, and they increase from step to step. Points that earlier steps left near 0, at distance of order 3<sup>*m*−*l*</sup>, are multiplied by |*T*<sub>*j*</sub>| ∈ {1, 3, 5} at every later step, since ‖*T*<sub>*j*</sub>*t*‖ = |*T*<sub>*j*</sub>|‖*t*‖ for ‖*t*‖ ≤ 1/(2|*T*<sub>*j*</sub>|). Whether some schedule of *g* = 2 factors drives *M*(*x*<sub>*k*</sub>) to 0 while the reciprocal laws tend to δ<sub>1/2</sub> along all prefixes is **Open**. That would be a band construction for the radix-3 case of Conjecture E1.C, and E1.3 does not exclude it.

**Lemma E1.3C (folds and cuts move near-*r*/*D* mass; Paper proof + Finite certificate).** Let *D* ≥ 2, gcd(*r*, *D*) = 1 and 0 < η < 1/(3*D*). Let *B* be the closed arc of radius η about *r*/*D*, let σ be a *T*<sub>*b*</sub>-invariant probability on 𝕋 with *p* = σ(*B*), and let 0 < ρ < 1/3.
1. *Fold.* The fold law (1 − ρ)σ + ρν<sub>*F*</sub>, with ν<sub>*F*</sub> the fold-band law of part 3 (ν<sub>*F*</sub> = σ∗σ for a coprime fold), satisfies

```math
\big((1-\rho)\,\sigma+\rho\,\nu_F\big)(B)\le p-\rho\,(3p-2).
```

2. *Cut.* The cut law σ/(1 + ρ) + ρδ<sub>0</sub>/(1 + ρ) gives *B* the mass *p*/(1 + ρ).
3. *Effect on x.* A cut multiplies the cycle mean of *x* by 1/(1 + ρ), and a fold multiplies it by at least 1 − ρ.

*Proof.* ν<sub>*F*</sub> is the law of *z* + *T*<sub>*b*</sub><sup>*t*</sup>*z*, averaged over the offsets *t* of part 3; for a coprime fold the two summands are independent. Both summands have law σ by invariance. If both lie in *B*, the sum lies within 2η of 2*r*/*D*, while ‖2*r*/*D* − *r*/*D*‖ = ‖*r*/*D*‖ ≥ 1/*D* > 3η. So the sum is outside *B*, and the union bound gives ν<sub>*F*</sub>(*B*) ≤ 2(1 − *p*). Then (1 − ρ)*p* + 2ρ(1 − *p*) = *p* − ρ(3*p* − 2). For the cut, 0 ∉ *B* because ‖*r*/*D*‖ > η. Part 3 follows from the two displayed laws (GF-45's cycle comparison) and ∫‖*t*‖ *d*ν<sub>*F*</sub> ≥ 0. ∎ The script checks part 1 exactly on 396 discrete coprime-fold instances and on 644 actual cycle laws with every offset *t*.

**Proposition E1.3D (the *D* ≥ 3 targets; Paper proof).** Let *D* ∣ *b* − 1, *D* ≥ 3 and gcd(*r*, *D*) = 1. Consider any sequence of steps *k* = 1, 2, …, each of which is either a δ<sub>*r*/*D*</sub>-preserving periodic band operation or a GF-45 pair (cut one coordinate and fold the other, with ratio ρ<sub>*k*</sub> < 1/3). Work in the comparison regime: the actual cycle laws after step *k* are coupled to the ideal laws of GF-45's cycle comparison with mass and displacement errors at most ε<sub>*k*</sub>, where Σε<sub>*k*</sub> < ∞ and Σε<sub>*k*</sub>/*M*(*x*<sub>*k*−1</sub>) < ∞. Both can be arranged by taking the scales large, since the comparison errors tend to 0 with the scale for fixed input. Then the cycle means and the reciprocal cycle laws cannot satisfy both *M*(*x*<sub>*k*</sub>) → 0 and σ<sub>*y*<sub>*k*</sub></sub> → δ<sub>*r*/*D*</sub>.

*Proof.* By part 4(a) the band steps are trivial, so only GF-45 pairs remain. A coupling with error ε changes a cycle mean by at most 2ε, and it gives σ<sub>actual</sub>(*B*<sub>ζ</sub>) ≤ σ<sub>ideal</sub>(*B*<sub>ζ+ε</sub>) + ε for the closed arcs *B*<sub>ζ</sub> about *r*/*D*.

*x side.* Lemma E1.3C(3) gives *M*(*x*<sub>*k*</sub>) ≥ (1 − ρ<sub>*k*</sub> − 2θ<sub>*k*</sub>)*M*(*x*<sub>*k*−1</sub>) with θ<sub>*k*</sub> = ε<sub>*k*</sub>/*M*(*x*<sub>*k*−1</sub>) summable. If Σρ<sub>*k*</sub> < ∞, the product of these factors stays bounded away from 0 from some *k* on, and *M*(*x*<sub>*k*</sub>) does not tend to 0. So *M*(*x*<sub>*k*</sub>) → 0 forces Σρ<sub>*k*</sub> = ∞.

*y side.* Choose *K* with Σ<sub>*k*>*K*</sub>ε<sub>*k*</sub> < 1/(12*D*), and radii ζ<sub>*K*</sub> = 1/(4*D*) and ζ<sub>*k*</sub> = ζ<sub>*k*−1</sub> − ε<sub>*k*</sub>, all in (1/(6*D*), 1/(4*D*)]. Put *p*<sub>*k*</sub> = σ<sub>*y*<sub>*k*</sub></sub>(*B*<sub>ζ<sub>*k*</sub></sub>). Lemma E1.3C(1),(2) with η = ζ<sub>*k*−1</sub> < 1/(3*D*) give *p*<sub>*k*</sub> ≤ *p*<sub>*k*−1</sub> − ρ<sub>*k*</sub>(3*p*<sub>*k*−1</sub> − 2) + ε<sub>*k*</sub> after a fold of *y*, and *p*<sub>*k*</sub> ≤ *p*<sub>*k*−1</sub>/(1 + ρ<sub>*k*</sub>) + ε<sub>*k*</sub> after a cut of *y*. If σ<sub>*y*<sub>*k*</sub></sub> → δ<sub>*r*/*D*</sub>, then *p*<sub>*k*</sub> → 1, because every *B*<sub>ζ<sub>*k*</sub></sub> contains the open arc of radius 1/(6*D*). So *p*<sub>*k*−1</sub> ≥ 5/6 for all large *k*, and both bounds give *p*<sub>*k*</sub> ≤ *p*<sub>*k*−1</sub> − ρ<sub>*k*</sub>/2 + ε<sub>*k*</sub>. Summing, Σρ<sub>*k*</sub> < ∞, which contradicts the *x* side. ∎

**Conjecture E1.C (Open).** If *D* ∣ *b* − 1, *D* ≥ 2 and *r* ≢ 0 (mod *D*), then δ<sub>*r*/*D*</sub> ∉ ℛ<sub>*b*</sub>. Write *r*/*D* in lowest terms; its denominator still divides *b* − 1. If that denominator is at least 3, Proposition E1.3D excludes both known mechanisms in the comparison regime; test cases are *b* = 4 and *b* = 10 with δ<sub>1/3</sub> (digits of 1/*x* mostly 1, respectively mostly 3). If it is 2, so that *r*/*D* = 1/2 and *b* is odd, the band mechanism is not excluded (Example E1.3B), and the radix-3 case δ<sub>1/2</sub> (digits of 1/*x* mostly 1) is open on both sides. E1.3 is a limitation of methods: it names the two mechanisms and proves that they cannot reach the targets with *D* ≥ 3. It is not a proof of the conjecture.

### E1.4 Exact frequency sums at the cylinders adjacent to zero (Paper proof)

Let *x* = *x*(*b*, α) be a GF-45 witness with 0 < α < 1 and let *L* ≥ 1. The only cylinders whose closures contain 0 are those of the words 0<sup>*L*</sup> and (*b* − 1)<sup>*L*</sup>. Their frequencies satisfy

```math
f_N(0^L;1/x)+f_N\big((b-1)^L;1/x\big)\longrightarrow \alpha+2(1-\alpha)b^{-L},
```

and each word separately has lower frequency at least (1 − α)*b*<sup>−*L*</sup>. *Proof.* On the circle, the union of the two cylinders is the arc [−*b*<sup>−*L*</sup>, *b*<sup>−*L*</sup>), whose boundary carries no μ<sub>α</sub>-mass. So the union is a continuity set, and weak convergence along all *N* (GF-45) gives the limit. ∎

Each word separately converges if and only if the one-sided atom masses α<sup>±</sup> (mass approaching 0 from above or from below) exist, and then the limits are α<sup>+</sup> + (1 − α)*b*<sup>−*L*</sup> and α<sup>−</sup> + (1 − α)*b*<sup>−*L*</sup>. In GF-45 the cut bands approach 0 strictly from above, since the future tail is positive. A fold band, however, subtracts *b*<sup>*s*−*d*</sup>*F* from a sum of two near-zero points, and a positive proportion of such sums cross below 0. So the split α<sup>+</sup>/α<sup>−</sup> depends on the construction and is **Open**.

### E1.5 Simultaneous radices *b* and *b*<sup>*k*</sup> (Paper proof; certificate)

1. *M*<sub>*b*</sub> = *M*<sub>*b*<sup>*k*</sup></sub>. *Proof.* ‖*b*<sup>*kn*+*r*</sup>*z*‖ ≤ *b*<sup>*r*</sup>‖*b*<sup>*kn*</sup>*z*‖ in one direction, and the times *kn* form a subsequence with density 1/*k* in the other. ∎
2. **Theorem.** For each fixed *k* ≥ 2 and each 0 ≤ α ≤ 1, the GF-45 witness can be chosen so that ν<sub>*N*</sub>(1/*x*; *b*<sup>*k*</sup>) → μ<sub>α</sub> as well. *Proof.* In GF-45's choice *d* = (*LP*<sub>*F*</sub>)<sup>*e*</sup>, *m* = *P*<sub>*C*</sub>(1 + *jLP*<sub>*F*</sub>), take *L* divisible by *k* and coprime to *P*<sub>*C*</sub>. Then the new periods *q* ≡ *m* ≡ *P*<sub>*C*</sub> (mod *k*) and *mP*<sub>*F*</sub> remain coprime to *k*, by induction from the seeds of period one (24 exact steps for *k* ∈ {2, 3, 4, 5, 6, 12}). Each residue class *n* ≡ *r* (mod *k*) therefore samples every cycle uniformly, and all of GF-45's comparisons hold on each progression, as in E1's base-2<sup>*e*</sup> argument. For the fold this needs one more check, because a fold-band point *b*<sup>*im*+*s*</sup>*F* + *b*<sup>*s*</sup>*F* involves the pair of orbit indices ((*im* + *s*) mod *P*<sub>*F*</sub>, *s* mod *P*<sub>*F*</sub>). Restrict to *im* + *s* ≡ *r*′ (mod *k*). For fixed *i*, the admissible *s* form an arithmetic progression of difference *k*, so *s* mod *P*<sub>*F*</sub> is uniform over every *kP*<sub>*F*</sub> consecutive values, whatever *i* is (gcd(*k*, *P*<sub>*F*</sub>) = 1). Over *P*<sub>*F*</sub> consecutive *i*, *im* mod *P*<sub>*F*</sub> is uniform (gcd(*m*, *P*<sub>*F*</sub>) = 1). Hence the pair is uniform on (ℤ/*P*<sub>*F*</sub>ℤ)<sup>2</sup> on each progression too, and the fold-band law is still σ∗σ there (1 205 exact checks). The endpoint α = 1 needs none of this: μ<sub>1</sub> = δ<sub>0</sub>, and ν<sub>*N*</sub>(1/*x*; *b*) → δ<sub>0</sub> means 1/*x* ∈ *M*<sub>*b*</sub> = *M*<sub>*b*<sup>*k*</sup></sub> by part 1, which is ν<sub>*N*</sub>(1/*x*; *b*<sup>*k*</sup>) → δ<sub>0</sub>. ∎ Whether a **single** witness works for all *k* is Open: the period factors created at early stages persist.

### E1.6 Approximation exponents (Paper proof / External input)

- μ(1/*x*) = μ(*x*) for irrational *x* (classical: |1/*x* − *q*/*p*| = |*x* − *p*/*q*|·*q*/(*p*|*x*|), and the heights are comparable).
- **GF-45 witnesses can be Liouville.** The witness satisfies |*x* − *x*<sup>(*i*)</sup>| ≤ *Cb*<sup>−*m*<sub>*i*+1</sub></sup>, and every constraint on *m*<sub>*i*+1</sub> is a lower bound. Imposing also *m*<sub>*i*+1</sub> ≥ *i*·log<sub>*b*</sub> den(*x*<sup>(*i*)</sup>) gives μ(*x*) = μ(1/*x*) = ∞ without changing the law.
- *M*<sub>*b*</sub> ∩ Bad ≠ ∅. The number Σ<sub>*k*≥0</sub>*u*<sup>−2<sup>*k*</sup></sup> lies in *M*<sub>*u*</sub>, and it has bounded partial quotients for integers *u* ≥ 3 by the explicit folded continued fractions of **Shallit (1979, J. Number Theory 11)** and **Kmošek (1979)** (`External input`, quoted, not re-verified). For *b* ≥ 3 take *u* = *b*. For *b* = 2 take *u* = 4 ≥ 3 and use *M*<sub>2</sub> = *M*<sub>4</sub> (E1.5(1)), so the hypothesis *u* ≥ 3 suffices for every radix. So membership in *M*<sub>*b*</sub> does not force good approximability. A run of length *g* after position *n* gives only *q*‖*qx*‖ ≤ *b*<sup>*n*−*g*</sup>.
- **Open.** Is there a badly approximable *x* ∈ *M*<sub>*b*</sub> whose reciprocal has law μ<sub>α</sub> for some 0 < α < 1? This would join E1 to E2.

**Rates (heuristic remark, not a theorem).** In the GF-45 schedule the periods multiply (*P*<sub>*F*′</sub> = *mP*<sub>*F*</sub>), so log log *m*<sub>*i*</sub> ≳ *i*. The coefficient recursion contracts like ∏(1 − (1 − α)*h*<sub>*j*</sub>) ≍ *j*<sup>−(1−α)</sup>. So the best rate this schedule could give is about (log log *N*)<sup>−(1−α)</sup>. An effective prescribed spectrum remains open (Audit III m6).

---

## E2. Lowering the computable bounded-partial-quotient cap

### E2.0 Why GF-46 stopped at 14, 42 and 100

GF-46 Theorem 2.3 needs a Frostman exponent *s* above the threshold

```math
s^*(\rho)=\frac{5-\rho}{2(3-\rho)},\qquad s^*(3/4)=\frac{17}{18},\quad s^*(1/2)=\frac{9}{10},\quad s^*(0)=\frac56 .
```

This follows from eliminating β and θ in (2.5): the system is feasible if and only if 2(1 − *s*)/(1 − ρ) < *s* − 1/2. The function *s*\* is strictly increasing in ρ, and the script checks the threshold exactly at 100 values of ρ. GF-46 met the threshold only with *L* ∈ {2, 4} certificates or the hand route at *L* = 52, and for small *L* the factor (*q* + *p*)<sup>−2*s*</sup> loses heavily. As *L* → ∞, however, Σ(*M*, *L*, *s*)<sup>1/*L*</sup> converges to the leading eigenvalue of the transfer operator, so the true limit of the method is dim<sub>H</sub>*F*<sub>*M*</sub> > *s*\*. The thresholds 17/18 and 9/10 confirmed by Audit IV stay unchanged here. What changes is the block length.

### E2.1 Transfer identity and eigenfunction certificate (Paper proof; certificate)

Let 𝓛<sub>*s*</sub>*f*(*x*) = Σ<sub>*a*≤*M*</sub>(*a* + *x*)<sup>−2*s*</sup>*f*(1/(*a* + *x*)) act on [0, 1]. Then

```math
\Sigma(M,L,s)=\sum_{\mathbf u}(q_L+q_{L-1})^{-2s}=(\mathcal L_s^L\mathbf 1)(1).
```

The first equality is the reversal (*q*<sub>*L*</sub>, *p*<sub>*L*</sub>)(**u**) = (*q*<sub>*L*</sub>, *q*<sub>*L*−1</sub>)(reversed **u**); 18 exact multiset identities are checked. The second holds because the inverse branch composition has derivative (*q* + *q*′*x*)<sup>−2</sup>; the script checks it as an exact rational identity at 2*s* ∈ {1, 2, 3} in 51 cases. In addition, (*q* + *p*)(**vw**) ≤ (*q* + *p*)(**v**)·(*q* + *p*)(**w**), so Σ is supermultiplicative in *L* (3 125 checks). *Proof.* Write *M*<sub>**v**</sub> = (*p*′<sub>**v**</sub>, *p*<sub>**v**</sub>; *q*′<sub>**v**</sub>, *q*<sub>**v**</sub>) by rows, with primes marking the index *L* − 1. Since *M*<sub>**vw**</sub> = *M*<sub>**v**</sub>*M*<sub>**w**</sub>, its second column gives (*q* + *p*)(**vw**) = (*q*<sub>**v**</sub> + *p*<sub>**v**</sub>)*q*<sub>**w**</sub> + (*q*′<sub>**v**</sub> + *p*′<sub>**v**</sub>)*p*<sub>**w**</sub>. This is at most (*q*<sub>**v**</sub> + *p*<sub>**v**</sub>)(*q*<sub>**w**</sub> + *p*<sub>**w**</sub>), because *p*′<sub>**v**</sub> ≤ *p*<sub>**v**</sub> and *q*′<sub>**v**</sub> ≤ *q*<sub>**v**</sub> when every partial quotient is at least 1. Raising to the power −2*s* < 0 and summing over **v** and **w** gives Σ(*M*, *L*<sub>1</sub> + *L*<sub>2</sub>, *s*) ≥ Σ(*M*, *L*<sub>1</sub>, *s*)·Σ(*M*, *L*<sub>2</sub>, *s*). ∎

**Certificate lemma.** Let *h* > 0 be decreasing on [0, 1].
- If 𝓛<sub>*s*</sub>*h* ≥ λ*h* on [0, 1], then Σ(*M*, *L*, *s*) ≥ λ<sup>*L*</sup>*h*(1)/*h*(0).
- If 𝓛<sub>*s*</sub>*h* ≤ λ*h* on [0, 1], then Σ(*M*, *L*, *s*) ≤ λ<sup>*L*</sup> for every *L*.

*Proof.* Use positivity of 𝓛 with *h*/*h*(0) ≤ **1** ≤ *h*/*h*(1), and evaluate at *x* = 1. ∎

**The check is exact.** *h* is piecewise linear with rational nodes on *x*<sub>*i*</sub> = *i*/*K*; the node values come from a float power iteration and are then rounded to rationals. On each interval [*x*<sub>*i*</sub>, *x*<sub>*i*+1</sub>], monotonicity gives 𝓛*h*(*x*) ≥ Σ<sub>*a*</sub>(*a* + *x*<sub>*i*+1</sub>)<sup>−2*s*</sup>*h*(1/(*a* + *x*<sub>*i*</sub>)) and *h*(*x*) ≤ *h*(*x*<sub>*i*</sub>), with the reverse inequalities for upper bounds. Every power (*K*/*n*)<sup>*P*/*Q*</sup> is bracketed by integer *Q*-th roots, as in GF-46 Lemma 2.2(3). In total the script verifies 4 000 interval inequalities in exact arithmetic.

### E2.2 New computable caps (Paper proof + Finite certificate)

| Regime | (*M*, *s*) | Certified λ (*K* = 1 500) | Even *L* | Conclusion |
|---|---|---|---|---|
| A, no external input (*s* > 17/18) | (14, 18/19) | 501/500 | **344** | Σ(14, 344, 18/19) > 1 |
| B, Weil 1948 + Estermann 1961 (*s* > 9/10) | (8, 46/51) | 1003/1000 | **226** | Σ(8, 226, 46/51) > 1 |

The midpoint parameters of GF-46 satisfy all five strict inequalities of (2.5) exactly for *r* = 1, 2, 3, 7. They are (α, β) = (33/76, 11/304) at *s* = 18/19 with ρ = 3/4, and (27/68, 43/816) at *s* = 46/51 with ρ = 1/2.

**Theorem E2.2.**
1. There is a Turing machine whose output *x* = [0; *a*<sub>1</sub>, *a*<sub>2</sub>, …] has 1 ≤ *a*<sub>*n*</sub> ≤ **14** for all *n*, satisfies *q*‖*qx*‖ > 1/16 for every *q* ≥ 1, and has *P*(*x*) absolutely normal for every nonconstant *P* ∈ ℚ[*X*]. The proof uses no external input; its only finite certificate is the one above.
2. With the Weil–Estermann bound as input, the same holds with **8** in place of 14 and 1/10 in place of 1/16.
3. Both statements extend to all larger caps, since *F*<sub>*M*</sub> ⊂ *F*<sub>*M*+1</sub> and Σ increases with *M*. Part (3) of GF-46 Theorem 2.4 carries over verbatim. In particular, *Z* = *x* − ⌊*x* − *S*⌋ has persistent all-prime support and satisfies *q*‖*qZ*‖ > 1/16 with no external input (cap 14, Regime A), and *q*‖*qZ*‖ > 1/10 under the Weil–Estermann input (cap 8, Regime B), since ‖*qZ*‖ = ‖*qx*‖.

*Proof.* GF-46 Lemma 2.2(1),(4), Theorem 2.3 and Theorem 2.4 use the block length *L* only through evenness, through *B*<sub>*M*,*L*</sub> ≤ 2(*M* + 1)<sup>*L*</sup> and through the stopping-time independence. Substitute (14, 344, 18/19) in Regime A and (8, 226, 46/51) in Regime B, and replace Step 3 by the G1-corrected weight rule of E3. ∎

**Prior-art precision (Audit IV G2 and G4).** **Existence** of normal numbers with partial quotients at most *N* goes back to Kaufman (1980), through R. C. Baker's observation recorded in Montgomery's *Ten Lectures* (CBMS 84, 1994), for *N* ≥ 3, and to Queffélec–Ramaré (2003) for *N* = 2. Jordan–Sahlsten (2016) extend this to Gibbs measures of dimension above 1/2. As quoted by Jordan–Sahlsten and not re-verified here, Hochman–Shmerkin (2015) give pointwise normality for such measures. Montgomery's question is an existence question and was already answered; nothing here answers or strengthens it. The contribution is **Turing computability with explicit rational constants** for every nonconstant *P* ∈ ℚ[*X*] at the caps 14 and 8, toward a computable form of Queffélec's 2006 remark that no explicit example in BAD was known. The machine runs in principle only, not in practice: see E3. Audit IV's G4(a)–(d) literature checks are still outstanding, so priority is provisional.

### E2.3 Barriers (Paper proof + Finite certificate; Objective 4)

| Claim | Certificate | Consequence |
|---|---|---|
| 𝓛<sub>9/10</sub>*h* ≤ (99/100)*h* for *M* = 7 | exact, *K* = 400 | Σ(7, *L*, 9/10) ≤ 0.99<sup>*L*</sup> < 1 for all *L* |
| 𝓛<sub>17/18</sub>*h* ≤ (199/200)*h* for *M* = 12 | exact, *K* = 400 | Σ(12, *L*, 17/18) < 1 for all *L* |
| 𝓛<sub>5/6</sub>*h* ≤ (19/20)*h* for *M* = 4 | exact, *K* = 200 | Σ(4, *L*, 5/6) < 1 for all *L* |

The bound Σ ≤ λ<sup>*L*</sup> also gives Σ<sub>**u**</sub>|*I*<sub>**u**</sub>|<sup>*s*</sup> ≤ Σ*q*<sub>*L*</sub><sup>−2*s*</sup> ≤ 2<sup>2*s*</sup>λ<sup>*L*</sup> → 0, so 𝓗<sup>*s*</sup>(*F*<sub>*M*</sub>) = 0. By the mass distribution principle, *F*<sub>*M*</sub> then carries **no** measure with μ(*I*) ≤ *C*|*I*|<sup>*s*</sup>, block-i.i.d. or not.

**Theorem E2.3.**
- Theorem 2.3 can never be applied on *F*<sub>*M*</sub> with *M* ≤ 7 in Regime B.
- It can never be applied with *M* ≤ 12 in Regime A.
- Within the two-block large-sieve bookkeeping (2.5), no rectangle-count exponent ρ ≥ 0 reaches *M* ≤ 4, because *s*\*(ρ) ≥ 5/6.

So the Weil-regime cap 8 is optimal. Regime A is optimal up to *M* = 13: the float measurement λ<sub>13</sub>(17/18) ≈ 1.000176 means dim *F*<sub>13</sub> ≈ 0.94453 exceeds 17/18 ≈ 0.94444 by about 9·10<sup>−5</sup>. A certificate for *M* = 13 would need *s* in that window, hence large denominators and a grid of about 10<sup>5</sup> points, so the case is **Open**. The stretch target *M* = 2 (dim *F*<sub>2</sub> ≈ 0.53128 as a float measurement, matching Hensley and Jenkinson–Pollicott) needs a Fourier-decay mechanism outside (2.5). Candidates are a computable form of the Queffélec–Ramaré multi-block large sieve, of the Jordan–Sahlsten argument, or of a spectral-gap (Dolgopyat-type) estimate in the style of Sahlsten–Stevens, Algom–Rodriguez Hertz–Wang or Baker–Banaji. I did not locate any joint "Bourgain–Kontorovich–Sahlsten–Stevens" paper. Bourgain–Kontorovich (Zaremba, Ann. Math. 2014) concerns a different counting problem.

Float measurements (`[finite]`, not certificates): the leading eigenvalue at *s* = 5/6 is about 0.9333 for *M* = 4 and 1.0058 for *M* = 5. A hypothetical input with ρ = 0 would therefore allow *M* = 5, and nothing smaller.

---

## E3. Effectiveness and complexity

- **G1 fixed.** Search only those *D* with *D*<sup>*Q*</sup> ≥ *B*<sub>*M*,*L*</sub><sup>*P*</sup>, where 2*s* = *P*/*Q*; this is an exact integer test. Every *a*<sub>*N*</sub> is then at least 1, every weight is positive and satisfies *a*<sub>*N*</sub><sup>*Q*</sup>*N*<sup>*P*</sup> ≤ *D*<sup>*Q*</sup>, and Σ*a*<sub>*N*</sub> > *D* holds once *D*(Σ − 1) exceeds the number of blocks. *Regression (exact):* for *M* = 30, *L* = 2, *s* = 10/11, the naive rule at *D* = 14 200 gives Σ*a*<sub>*N*</sub> = 14 206 > *D* with **461 of 900** weights equal to zero, which reproduces Audit IV. The corrected least *D*\* = 250 087 makes all 900 weights positive and admissible.
- **Sizes.** Each selection step evaluates *M*<sup>*L*</sup> children. That count has 105 digits for (100, 52), 7 for (42, 4) and 5 for (14, 4), but **395** for (14, 344) and **205** for (8, 226). *B*<sub>*M*,*L*</sub> has 396 and 206 digits respectively. Lowering the cap trades a constant-size alphabet for an astronomically large one. Near the threshold the certificate needs *L* ≈ log(*h*(0)/*h*(1))/log λ<sub>*M*</sub>(*s*), with λ − 1 roughly proportional to dim *F*<sub>*M*</sub> − *s*. So the alphabet grows like exp(*C* log *M*/(dim *F*<sub>*M*</sub> − *s*)); this is an estimate from the certificate shape, not a lower-bound theorem.
- **First partial quotient.** Emitting the first block requires the potential estimates of GF-46 Step 3 at precision 2<sup>−4</sup> over all *M*<sup>*L*</sup> children, with Lipschitz constants as large as *b*<sup>*J*²</sup> and *J* ≍ 2<sup>*m*</sup>Σ*K̄*/*w*(**a**). The cost of block *m* is doubly exponential in *m*, as in GF-46 §7 Q4. The construction is Turing-computable. Polynomial-time generation of a badly approximable absolutely normal number remains **Open**.
- **Effective rate.** As Audit IV m10 notes, Ψ(*x*) ≤ 1 bounds the number of bad indices *j* but not where they occur, so no discrepancy rate for *P*(*x*) is claimed.

## E4. Folding and explicit series

- **Attribution.** GF-46 Theorem 3.1(1) is the classical Folding Lemma of Mendès France (1973) and van der Poorten–Shallit (1992); only 3.1(2) is possibly new (Audit IV G3).
- **Representation Lemma (Paper proof).** Fix *b*. Let ℓ<sub>1</sub> < ℓ<sub>2</sub> < ⋯ be the primes not dividing *b*, and let *S* = Σℓ<sub>*n*</sub><sup>−1</sup>*b*<sup>−*n*</sup>. **Every** real *x* ∉ *S* + ℤ[1/*b*] has the expansion *x* = ⌊*x* − *S*⌋ + Σ<sub>*n*≥1</sub>(*d*<sub>*n*</sub> + 1/ℓ<sub>*n*</sub>)*b*<sup>−*n*</sup>, where *d*<sub>*n*</sub> are the digits of {*x* − *S*}. This expansion has full density, coefficients in (0, *b*) and shifted prefix denominators exactly ∏<sub>*n*≤*N*</sub>ℓ<sub>*n*</sub>. The last point holds because each ℓ<sub>*n*</sub> occurs to exact order −1 in exactly one term. Hence "persistent off-radix prime support" is a property of a representation, available for all but countably many reals. Combined with any intrinsic property, such as bounded partial quotients, μ = 2, polynomial normality or a uniform bound *q*‖*qx*‖ ≫ 1/ψ(*q*), it adds nothing about the real number itself. With E2.2 this gives series *Z* with persistent support, *q*‖*qZ*‖ > 1/16 (or > 1/10 under the Weil–Estermann input) and every *P*(*Z*) absolutely normal.
- **What remains substantive** is explicitness, meaning a closed form without measure selection. The Shallit–Kmošek numbers give closed-form bounded partial quotients but lie in *M*<sub>*u*</sub> and are therefore not normal. GF-46 Theorem 3.2 gives closed-form polynomial normality with defect exp(−*C*(log log *q*)ψ(log log *q*)). Getting both properties in one closed form is GF-46 Open 5 and remains **Open**.

## E5. Toeplitz Gram matrices and the determinant programme

For a probability measure ν on 𝕋, let *T*<sub>*r*</sub>(ν) = (ν̂(*i* − *j*))<sub>*i*,*j*<*r*</sub>.

1. *T*<sub>*r*</sub>(μ<sub>α</sub>) = *G*<sub>*r*</sub> = (1 − α)*I* + α*J*, with det *G*<sub>*r*</sub> = (1 − α)<sup>*r*−1</sup>(1 + (*r* − 1)α) (50 exact cases). (det *G*<sub>*r*</sub>)<sup>1/*r*</sup> → 1 − α, which is exp∫log *w* for the density *w* = 1 − α of the absolutely continuous part. For measures with a singular part this limit formula, lim(det *T*<sub>*r*</sub>(μ))<sup>1/*r*</sup> = exp∫log *w* for μ = *w*λ + μ<sub>s</sub>, is the Verblunsky–Kolmogorov–Krein extension of Szegő's theorem (external classical input); the singular part drops out. For any mixture μ = Σ*c*<sub>*j*</sub>π<sub>*j*</sub> + *c*<sub>0</sub>λ of discrete measures π<sub>*j*</sub>, *T*<sub>*r*</sub>(μ) ⪰ *c*<sub>0</sub>*I*, so det ≥ *c*<sub>0</sub><sup>*r*</sup>, and by the same theorem the limit equals *c*<sub>0</sub>. For purely atomic μ, det *T*<sub>*r*</sub> = 0 as soon as *r* exceeds the size of the support. This is checked exactly for the orbit of 1/3 under *T*<sub>2</sub> (support 2) and for *U*<sub>3</sub> (support 3), with 54 mixture instances.
2. **Sandwich (Paper proof; 36 real and 99 complex non-symmetric exact instances).** With *F*<sub>*r*</sub>(ν) = Σ<sub>*k*=1</sub><sup>*r*−1</sup>(*r* − *k*)|ν̂(*k*)|²,

```math
F_r(\nu)\le \tfrac18\ \Longrightarrow\ e^{-2F_r(\nu)}\le \det T_r(\nu)\le e^{-F_r(\nu)/2}.
```

   *Proof.* *E* = *T*<sub>*r*</sub> − *I* is Hermitian with zero trace and ‖*E*‖<sub>op</sub> ≤ ‖*E*‖<sub>F</sub> = (2*F*)<sup>1/2</sup> ≤ 1/2. For |λ| ≤ 1/2 one has λ − λ² ≤ log(1 + λ) ≤ λ − λ²/4. Sum over the eigenvalues. ∎ The complex instances use measures (1 − *t*)λ + *t*π with π on (1/4)ℤ/ℤ and unequal weights at 1/4 and 3/4, so the Fourier coefficients lie in ℚ(*i*) and *T*<sub>*r*</sub> is Hermitian but not real symmetric.

3. **Answer to the brief.** Determinant positivity is an **equivalent reformulation**, up to constants, of the weighted *L*<sup>2</sup> Fourier mass that Weyl's criterion and the GF-46 potential Ψ already control. Indeed, for each base, normality of *P*(*x*) ⇔ det *T*<sub>*r*</sub>(ν<sub>*N*</sub>) → 1 for every *r*. (⇒) *F*<sub>*r*</sub>(ν<sub>*N*</sub>) → 0, so eventually *F*<sub>*r*</sub> ≤ 1/8 and the sandwich gives det ≥ *e*<sup>−2*F*<sub>*r*</sub></sup> → 1, while det ≤ 1 by Hadamard's inequality. (⇐) Here *F*<sub>*r*</sub>(ν<sub>*N*</sub>) ≤ 1/8 is not known in advance, so the sandwich does not apply; use Fischer's inequality instead. For 1 ≤ *k* < *r*, split the indices into {0, *k*} and the rest. The remaining principal block is positive semidefinite with unit diagonal, so its determinant is at most 1 by Hadamard, and det *T*<sub>*r*</sub>(ν) ≤ 1 − |ν̂(*k*)|². Hence det *T*<sub>*r*</sub>(ν<sub>*N*</sub>) → 1 forces ν̂<sub>*N*</sub>(*k*) → 0 for every *k* ≥ 1, and Weyl's criterion gives normality. Alternatively, a weak\* limit point ν of (ν<sub>*N*</sub>) with ν̂(*k*) ≠ 0 would satisfy det *T*<sub>*r*</sub>(ν) = 1 by continuity, and the equality case of Hadamard's inequality would force *T*<sub>*r*</sub>(ν) = *I*, a contradiction. The script checks Fischer's bound on all 135 sandwich instances. Determinants supply neither a new effective cylinder-selection criterion in E2 nor any saving: evaluating them needs the same exponential sums. For E1 targets the useful invariant is the Szegő limit, which recovers the Lebesgue weight *c*<sub>0</sub> exactly. For example, it equals 1 − α for GF-45 witnesses.

---

## Reproduction

```sh
python -B scripts/phase26_constructive_spectra.py
```

On Windows (Python 3.13), the script exits **0** in about 19 seconds. It was not run on Hail: Track E constraints required a direct Windows run. Exact certificate counts:

| Group | Count |
|---|---|
| Exact *S*∗*T* = (*j* + 1) identities, over 1 563 cyclotomic factors *G* | 112 536 |
| Mod-*g* rigidity instances over those factors, *g* ∈ {2, 3, 4, 5, 6, 7, 8, 9, 12}: trivial *G* = 1 / nontrivial (all at *g* = 2, all in the family of E1.3A(2)) | 9 / 6 |
| Theorem E1.3A: exhaustive exponent vectors on *d* = 2, …, 10 | 19 683 |
| Theorem E1.3A ingredients: Frobenius congruences / squarefreeness / pairwise coprimality mod *p* / odd parts *Q*<sub>*m*</sub> / negative controls for the gcd routine | 133 / 114 / 1 632 / 49 / 3 |
| Op(*c*, *l*) transient identities | 7 |
| Base-2 skip factor | 1 |
| Band-tracking positions on actual rationals, *y* and *x* sides / wrap-around example | 1 280 / 1 |
| Example E1.3B: multiplier patterns / error-free band laws / exact contraction steps | 1 / 1 / 5 |
| *b* = 3: classified *g* = 2 factors with a non-power-of-3 multiplier | 798 |
| Lemma E1.3C: discrete coprime folds / actual cycle laws with every offset | 396 / 644 |
| Fold-offset subgroup checks | 2 301 |
| Fold multiplier ≡ 2 (mod *D*) checks | 42 |
| *b*<sup>*k*</sup> period-coprimality steps | 24 |
| Fold-pair uniformity on progressions mod *k* (E1.5(2)) | 1 205 |
| Transfer identities at 2*s* ∈ {1, 2, 3} | 51 |
| Reversal multiset identities | 18 |
| Supermultiplicativity checks | 3 125 |
| Exact transfer-operator interval inequalities | 4 000 |
| Lowered-cap certificates (2) and barrier certificates (3) | 5 |
| LP threshold checks | 100 |
| (2.5) parameter certificates | 8 |
| G1 regression and G1 fix | 2 |
| E3 size computations | 6 |
| Toeplitz determinants / mixture bounds / real sandwich instances / complex non-symmetric sandwich instances | 50 / 54 / 36 / 99 |

Floating point is used only to generate the candidate *h* (afterwards rounded to exact rationals and checked exactly) and in the `[finite]` eigenvalue printout. No assertion that proves a theorem uses floats; the decimals printed for Example E1.3B are rendered from exact fractions.

## Open problems

1. Conjecture E1.C (δ<sub>*r*/*D*</sub> ∉ ℛ<sub>*b*</sub> for *D* ∣ *b* − 1), and more generally a necessary condition on ℛ<sub>*b*</sub>. For *D* = 2: can a schedule of the *g* = 2 band factors of Theorem E1.3A(2) drive *M*(*x*<sub>*k*</sub>) to 0 while keeping the reciprocal at δ<sub>1/2</sub> (Example E1.3B)? Is there a nontrivial periodic band operation in radix 3 with every *S*<sub>*j*</sub> a power of 3? Is ℛ<sub>2</sub> equal to the set of all *T*<sub>2</sub>-invariant measures? The band regime preserves every reciprocal orbit in base 2, but there is no operation that changes the seed.
2. The one-sided split α<sup>±</sup> in E1.4. A single GF-45 witness for all radices *b*<sup>*k*</sup>. A badly approximable GF-45 witness. An effective prescribed spectrum.
3. The cap *M* = 13 in the elementary regime (Open; the float measurement suggests it is attainable). Computable caps below 8 need Fourier decay outside (2.5); the existence cap *M* = 2 is classical and its computable form is open.
4. Polynomial-time generation, and a closed-form series that is both badly approximable and normal.

**Evidence summary.** E2.2 is `Paper proof` resting on GF-46 together with the `Finite certificate` of E2.1, plus Weil 1948 and Estermann 1961 for *M* = 8. E2.3 and E1.3 are limitation theorems about named methods; Theorem E1.3A is unconditional, and Proposition E1.3D holds in the stated comparison regime. Example E1.3B is an exact finite computation, and the radix-3 power-of-3 search is a `Finite certificate` for a finite family only. Shallit 1979, Kmošek 1979 and the Szegő–Verblunsky–Kolmogorov–Krein theorem are `External input`. Finite digit statistics establish nothing asymptotic, and cross-model review is not independent human peer review.

## Revision after the Track E review

The cross-model review [`reviews/track-e-review.md`](reviews/track-e-review.md) returned REVISE with one Major and nine Minor findings. This revision addresses all of them.

- **M1.** The universal non-contraction claim for band operations is withdrawn. Theorem E1.3A proves that *G* = 1 is the only cyclotomic factor with *G* ≡ 1 (mod *g*) for *g* ≥ 3, which closes E1.3(2) for *b* ≥ 4 and E1.3(4) for *D* ≥ 3. At *g* = 2 the review's counterexample is recorded exactly (Example E1.3B), and only the zero-band obstruction is claimed. Lemma E1.3C supplies the union bound *p*′ ≤ *p* − ρ(3*p* − 2) for folds, and Proposition E1.3D states the interleaved conclusion for *D* ≥ 3 with its hypotheses.
- **m1.** E1.2(a) is stated modulo 1 with explicit hypotheses (preperiod of *x*, bounded *h*<sub>*i*</sub>, margin *H*); the wrap-around example is checked. **m2.** The converse in E1.2(b) is reworded. **m3.** The rigidity count is split into 9 trivial and 6 nontrivial instances, and *x*-side band tracking is checked. **m4.** E1.6 covers *b* = 2 through *M*<sub>2</sub> = *M*<sub>4</sub>. **m5.** E1.5(2) treats α = 1 and fold pairs on progressions. **m6.** E2.1 proves supermultiplicativity and checks the transfer identity at three values of *s*. **m7.** E2.2(3) and E4 state the regime of each bound on *q*‖*qZ*‖. **m8.** E5 uses Fischer's inequality (or Hadamard's equality case with compactness) for (⇐), attributes the singular-part case to Verblunsky–Kolmogorov–Krein, and checks complex non-symmetric instances. **m9.** The reproduction table lists every counter, including the E3 size computations.
