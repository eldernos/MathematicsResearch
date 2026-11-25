# Specialist Reviewer Packet — Paper IV (Version 2.0)

**Title:** Arithmetic Certificates for Normality and Mathematical Limitations  
**Author:** Christopher Anderson (Independent Researcher)  
**Version:** 2.0 (supersedes `papers/04-arithmetic-certificates`, v1.1)  
**Pinned Lean baseline:** [`e4809cf561573aef588e6ffc491a35cdb79fd9ec`](https://github.com/eldernos/MathematicsResearch/tree/e4809cf561573aef588e6ffc491a35cdb79fd9ec)  
**Review status:** Lean kernel replay and axiom audit completed at `e4809cf`; written proofs, literature comparisons and priority statements have been checked only by AI models across providers and have not undergone independent human peer review.

---

## Core results and shortest complete proofs / sketches

### 1. Mean rational approximation and fixed-support cancellation (Theorems 1.1 & 1.2; AC-01, AC-04)

- **Evidence:** Theorem 1.1 is **Lean-supported paper proof** (`ArithmeticCertificate.lean#L62` composed with `SmoothOrbit.lean#L207`, checked in `Check.lean`); Theorem 1.2 is **Kernel-verified** (`SmoothOrbit.lean#L207`).
- **Exact statements:**
  - *Theorem 1.2 (qualitative form of Vandehey 2019, Cor. 1.2):* For coprime $b,c \ge 2$, $d \ge 0$, $\epsilon > 0$, there exists $M(b,c,d,\epsilon)$ such that $|T^{-1}\sum_{i<T} e(b^i a/Q)| \le \epsilon$ whenever $T \ge 1$, $\gcd(a,Q)=1$, $Q \mid c^j$, and $M \le Q \le T^d$.
  - *Theorem 1.1:* Fix coprime $b,c \ge 2$, $L \ge 2, B \ge 1, d \ge 0$, and $P_n \in \mathbb Q$ with $b^n x - P_n \to 0$. At scale $k$ put $A=(LB)^k$, $T=B^k$, $m=L^k$. If for each $u \in \{1,\dots,LB-1\}$, $M \ge 1$, $\eta > 0$, all large $k$ admit $E \subseteq \{0,\dots,m-1\}$ with $|E| \le \eta m$ such that every $j \notin E$ has a rational $y$ with $c$-supported reduced denominator $M \le Q \le T^d$ and $T^{-1}\sum_{i<T}\|P_{uA+jT+i}-b^i y\|_{\mathbb T} \le \eta$, then $x$ is base-$b$ normal.
- **Proof sketch & external inputs:** Theorem 1.2 uses $r=\varphi(c^2)$, $C=b^r-1$, lifting the exponent $v_p(b^{rm}-1)=v_p(C)+v_p(m)$ (handling even $c$ since $4\mid C$), complete-period orthogonality $|S(a)|\le\sqrt{Q}$, and Cauchy–Schwarz differencing along shifts $jv_D$ with $K \le D \le cK$ inducting on $Q \le K^s$. Theorem 1.1 applies Theorem 1.2 to $hy$, transfers via $|e(hs)-e(ht)|\le 2\pi|h|\|s-t\|_{\mathbb T}$, sums over geometric shells $[A,(LB)A)$, and concludes via Weyl's criterion (Weyl 1916, §1).

### 2. Overlap rigidity and counting obstruction (Theorems 3.1 & 4.1, Corollary 3.2; AC-03, AC-10)

- **Evidence:** Theorem 3.1 is **Kernel-verified** (`OrbitRigidity.lean#L32`); Corollary 3.2 is **Lean-supported paper proof** (`OrbitRigidity.lean#L83,101`); Theorem 4.1 is **Lean-supported paper proof** (`ModelCounting.lean#L14` checks the finite word inequality; measure bound and Borel–Cantelli are on paper).
- **Exact statements:**
  - *Theorem 3.1:* For coprime $b,c \ge 2$ and $d \ge 0$, there exists $\gamma(b,c,d)>0$ such that for any $T \ge 1$, any $c$-supported rationals $y,z$ with denominators $\le T^d$ and $y-z \notin \mathbb Z$, and any $f_0,\dots,f_{T-1} \in \mathbb R$, $T^{-1}\sum_{i<T}(\|f_i-b^iy\|_{\mathbb T}+\|f_i-b^iz\|_{\mathbb T}) \ge \gamma$.
  - *Corollary 3.2:* Vanishing combined mean error forces $y_j - z_j \in \mathbb Z$ eventually, and along a compatible overlapping chain forces eventually constant reduced denominator.
  - *Theorem 4.1:* With $a=b^2$ and $\eta_b = 1/(16a^2)$, $\lambda(E_{n,T}) \le T^{2d}\exp(-\lfloor T/2\rfloor/(4a))$, so on any prescribed schedule $T_k = B^k$ ($B \ge 2$) with $O(T_k^A)$ starts per scale, almost every $x$ admits no such model at any large $k$.
- **Proof sketch & external inputs:** Theorem 3.1 applies Theorem 1.2 to $w=y-z$ (denominator $Q \le T^{2d}$) for $Q \ge M(b,c,2d,1/2)$ to get mean distance $\ge 1/(4\pi)$, and uses the grid gap $1/Q \ge 1/M$ for $1<Q<M$. Theorem 4.1 uses base-$b^2$ digits of uniform $z=\{b^nx-y\}$, weights digit $1$ by $1$ and others by $2$ to get $2^K(1-1/(2a))^J \le \exp(-J/(4a))$, union-bounds over $\le T^{2d}$ rationals, and applies the first Borel–Cantelli lemma.

### 3. Countermodels and eight method obstructions (Propositions 5.1–5.2 & Section 6; AC-11)

- **Evidence:** **Paper proof** (finite exact checks in `scripts/phase17_limitations.py`).
- **Exact statements & external inputs:**
  - *Proposition 5.1 (Pair A):* $Y_n(x) = R_n + 2^{-n}(\lfloor 2^n t_n(x)\rfloor - \lfloor 2^n R_n\rfloor)$ for $x \in \{C, F\}$ gives identical odd-primary components and reduced odd denominators at every cutoff with error $< 2^{-n}$, while $D_N^{(2)}(C) \to 0$ and $D_N^{(2)}(F) \to 1$.
  - *Proposition 5.2 (Pair B):* Zeroing $C$ on $[2^{2^j}, j 2^{2^j})$ preserves limiting logarithmic word frequencies $2^{-k}$ and disjunctivity while giving $D_\infty^{(2)} = 1$.
  - *Section 6 (Items 1–8):* Isolates obstructions for fixed-support certificates, overlaps/prescribed starts, nearby Taylor cutoffs (external input: Hadamard 1896 PNT), balanced trace sources, prime-by-prime statistics, higher-rank density (external input: Furstenberg 1967, Theorem IV.1), complex product endpoints $P_N(a_N, e(x))$, and irrationality exponents/runs (external input: van der Poorten–Shallit 1992, pp. 240–242).

### 4. Computability on digit-program names (Lemma 7.1, Proposition 7.2, Theorems 7.3–7.4, Corollary 7.5; AC-11)

- **Evidence:** Lemma 7.1, Theorem 7.3, and Theorem 7.4 are **Kernel-verified** (`ComputableNormalityUndecidability.lean`, parameterized by endpoint streams); Proposition 7.2 is **Paper proof**; Corollary 7.5 is **Lean-supported paper proof**.
- **Exact statements:** Let `Names code s` mean $\forall n, \varphi_{\mathrm{code}}(n) = s(n) \in \{0,1\}$, and `TranscendentalZeroOnePromise s` mean $V(s)$ is transcendental over $\mathbb Q$ and $D_N^{(2)}(V(s)) \to 0$ or $1$. Given computable endpoints $a, b_*$ with transcendental values, $V(a)$ binary normal, and $D_N^{(2)}(V(b_*)) \to 1$ (constructed elementarily by Liouville's polynomial test in Proposition 7.2), bounded-evaluation halting switches produce total computable s-m-n maps into promised names reducing $\overline{K_0}$ and $K_0$ to binary normality. Hence no computable, c.e., or co-c.e. predicate on `Nat.Partrec.Code` (and no partial correct decider halting on all promised names) decides or recognizes binary normality on the promise.
- **Prior-art positioning:** Framed strictly as an elementary formalizable two-limit promise reduction, NOT as priority on Borel or effective completeness (contrast Ki–Linton 1994, $\boldsymbol{\Pi}^0_3$-completeness; Becher–Heiber–Slaman 2014, Theorem 3.2 and Corollaries 3.3–3.4, effective $\Pi^0_3$-completeness; Becher–Slaman 2014, Theorem 1, $\Sigma^0_4$-completeness).

### 5. Consistency-relative Rosser independence (Theorem 8.1, Remark 8.2; AC-11)

- **Evidence:** **Paper proof** (external input: Rosser 1936, Theorem II).
- **Exact statement:** For $T \in \{\mathrm{PA}, \mathrm{ZFC}\}$, switching from $C$ to $F$ at the first proof code $p \le n$ witnessing the Rosser predicate $W(p)$ yields a primitive recursive stream $s_T$ such that $T \vdash \mathsf{Norm}(s_T) \leftrightarrow R$, so consistency of $T$ alone implies $T \nvdash \mathsf{Norm}(s_T)$ and $T \nvdash \neg\mathsf{Norm}(s_T)$. Remark 8.2 notes the weak-arithmetic boundary ($Q$ vs. PA; $I\Delta_0 + \neg\mathrm{Exp}_2$) and explicitly states that nothing here bears on the truth or provability of normality for any named classical constant ($\ln 2, \pi, e, \sqrt{2}$, Erdős–Borwein).

---

## Reproduction links

- **Pinned repository commit:** https://github.com/eldernos/MathematicsResearch/tree/e4809cf561573aef588e6ffc491a35cdb79fd9ec
- **Lean 4 check file:** `papers/04-arithmetic-certificates-v2/Check.lean` (30 declarations audited against `propext`, `Classical.choice`, `Quot.sound`)
- **Finite script:** `python -B scripts/phase17_limitations.py`
- **Verification map & novelty ledger:** `papers/04-arithmetic-certificates-v2/VERIFICATION.md`, `papers/04-arithmetic-certificates-v2/LEDGER.md`

---

## Specific steps on which human specialist review is requested

1. **Prior art for overlap rigidity (Theorem 3.1 / Corollary 3.2):** Does an equivalent finite-overlap separation or denominator-constancy obstruction for aligned fixed-support rational models appear in the Korobov/Vandehey or symbolic-dynamics literature?
2. **Section 6, Items 3, 6, and 7:** Verification of (i) the uniform $h=o(K)$ nearby-Taylor affine-combination denominator rate via PNT prime bands (Item 3), (ii) the $M_N$ sparse construction (Item 6), and (iii) the moving-parameter complex-product endpoint counterexample and $D^+(x)<1 \iff \liminf N^{-1}\sum_{n<N} E(2^n x) > 0$ equivalence (Item 7).
3. **Elementary Liouville-normal endpoint (Proposition 7.2):** Verification of the unfinished-copy error bound $\ell_j/S_{j-1} \le 2/[j(j-1)]$ and periodic-rational Liouville approximation $2^{-S_j} \le q_j^{-(j+1)^2}$ for $V(a)$.
4. **Computability positioning (Section 7):** Confirmation that our framing of `TranscendentalZeroOnePromise` on `Names` cleanly and accurately distinguishes our elementary formalizable reduction from Ki–Linton (1994), Becher–Heiber–Slaman (2014, 2015), and Becher–Slaman (2014).
5. **PA-internal frequency transfer in Theorem 8.1:** Verification that the integer-only Champernowne count and $p + 1 + \lfloor\log_2 N\rfloor$ upper bound for $F$ formalize $T \vdash \mathsf{Norm}(s_T) \leftrightarrow R$ cleanly in PA (and in ZFC's natural numbers) without hidden analytic assumptions.
