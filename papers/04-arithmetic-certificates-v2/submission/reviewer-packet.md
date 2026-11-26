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
  - *Theorem 1.2 (qualitative form of Vandehey 2019, Cor. 1.2, arXiv preprint p. 2):* For coprime integers $b,c \ge 2$, integer $d \ge 0$, and $\epsilon > 0$, there exists an integer $M(b,c,d,\epsilon) \ge 1$ such that $|T^{-1}\sum_{i<T} e(b^i a/Q)| \le \epsilon$ whenever $T \ge 1$ is an integer, $\gcd(a,Q)=1$, $Q \mid c^j$, and $M \le Q \le T^d$.
  - *Theorem 1.1:* Fix coprime integers $b,c \ge 2$, integers $L \ge 2, B \ge 1, d \ge 0$, and $P_n \in \mathbb Q$ with $b^n x - P_n \to 0$. At scale $k \ge 0$ put $A=(LB)^k$, $T=B^k$, $m=L^k$. If for each $u \in \{1,\dots,LB-1\}$, integer $M \ge 1$, and $\eta > 0$, all large $k$ admit $E \subseteq \{0,\dots,m-1\}$ with $|E| \le \eta m$ such that every $j \notin E$ has a rational $y$ with $c$-supported reduced denominator $M \le Q \le T^d$ and $T^{-1}\sum_{i<T}\|P_{uA+jT+i}-b^i y\|_{\mathbb T} \le \eta$, then $x$ is base-$b$ normal.
- **Proof sketch & external inputs:** Theorem 1.2 uses $r=\varphi(c^2)$, $C=b^r-1$, lifting the exponent $v_p(b^{rm}-1)=v_p(C)+v_p(m)$ (handling even $c$ since $4\mid C$), complete-period orthogonality $|S(a)|\le\sqrt{Q}$, and Cauchy–Schwarz differencing along shifts $jv_D$ with $K \le D \le cK$ inducting on $Q \le K^s$. Theorem 1.1 applies Theorem 1.2 to $hy$, transfers via $|e(hs)-e(ht)|\le 2\pi|h|\|s-t\|_{\mathbb T}$, sums over geometric shells $[A,(LB)A)$, and concludes via Weyl's criterion (Weyl 1916, §1).

### 2. Overlap rigidity and counting obstruction (Theorems 3.1 & 4.1, Corollary 3.2; AC-03, AC-10)

- **Evidence:** Theorem 3.1 is **Kernel-verified** (`OrbitRigidity.lean#L32`); Corollary 3.2 is **Lean-supported paper proof** (`OrbitRigidity.lean#L83,101`); Theorem 4.1 is **Lean-supported paper proof** (`ModelCounting.lean#L14` checks only the finite weighted word inequality; uniformity of the shifted point, cylinder probability calculation, union bound over rationals, and Borel–Cantelli are written).
- **Exact statements:**
  - *Theorem 3.1:* For coprime integers $b,c \ge 2$ and integer $d \ge 0$, there exists $\gamma(b,c,d)>0$ such that for any integer $T \ge 1$, any $c$-supported rationals $y,z$ with denominators $\le T^d$ and $y-z \notin \mathbb Z$, and any $f_0,\dots,f_{T-1} \in \mathbb R$, $T^{-1}\sum_{i<T}(\|f_i-b^iy\|_{\mathbb T}+\|f_i-b^iz\|_{\mathbb T}) \ge \gamma$.
  - *Corollary 3.2:* Fix $b,c,d$ as in Theorem 3.1. For each integer $j \ge 0$, let $T_j \ge 1$ be an integer and let $y_j, z_j \in \mathbb Q$ have $c$-supported reduced denominators at most $T_j^d$; if for real observations $f^{(j)}_0, \dots, f^{(j)}_{T_j-1}$ the combined mean circle error $T_j^{-1}\sum_{i<T_j}(\|f^{(j)}_i - b^i y_j\|_{\mathbb T} + \|f^{(j)}_i - b^i z_j\|_{\mathbb T}) \to 0$, then $y_j - z_j \in \mathbb Z$ for all sufficiently large $j$. In particular, for consecutive blocks with rational models $y_j, y_{j+1}$ whose start indices differ by an integer $r_j \ge 0$ and whose overlap has integer length $T_j \ge 1$, if both denominators are $c$-supported and at most $T_j^d$ and the combined mean error of the aligned models $b^{r_j}y_j, y_{j+1}$ on their common observations tends to zero, then $\operatorname{den} y_j$ is eventually constant.
  - *Theorem 4.1:* Fix integers $b \ge 2$, $d \ge 0$, put $a = b^2$, and set $\eta_b = 1/(16a^2) = 1/(16b^4)$. For a prescribed integer start $n \ge 0$ and integer length $T \ge 2$, let $E_{n,T}$ consist of all $x \in [0,1)$ for which a rational $y$ with $\operatorname{den} y \le T^d$ satisfies $T^{-1}\sum_{i<T}\|b^{n+i}x - b^i y\|_{\mathbb T} \le \eta_b$. Then $\lambda(E_{n,T}) \le T^{2d}\exp(-\lfloor T/2\rfloor/(4a))$. Consequently, on any independently prescribed schedule $T_k = B^k$ ($k \ge 1$, integer $B \ge 2$) with $O(T_k^A)$ prescribed starts per scale ($A \ge 0$), for almost every $x \in [0,1)$ there is $k_0(x) \ge 1$ such that none of the prescribed starts admits such a model at any scale $k \ge k_0(x)$.
- **Proof sketch & external inputs:** Theorem 3.1 applies Theorem 1.2 to $w=y-z$ (denominator $Q \le T^{2d}$) for $Q \ge M(b,c,2d,1/2)$ to get mean distance $\ge 1/(4\pi)$, and uses the grid gap $1/Q \ge 1/M$ for $1<Q<M$. Theorem 4.1 uses base-$b^2$ digits of uniform $z=\{b^nx-y\}$, weights digit $1$ by $1$ and others by $2$ to get $2^K(1-1/(2a))^J \le \exp(-J/(4a))$, union-bounds over $\le T^{2d}$ rationals, and applies the first Borel–Cantelli lemma.

### 3. Countermodels and eight method obstructions (Propositions 5.1–5.2 & Section 6; AC-11)

- **Evidence:** **Paper proof** (finite exact checks in `scripts/phase17_limitations.py`).
- **Exact statements & external inputs:**
  - *Proposition 5.1 (Pair A):* $Y_n(x) = R_n + 2^{-n}(\lfloor 2^n t_n(x)\rfloor - \lfloor 2^n R_n\rfloor)$ for $x \in \{C, F\}$ (where $C$ is the binary Champernowne constant) gives identical odd-primary components and reduced odd denominators at every cutoff with error $< 2^{-n}$, while $D_N^{(2)}(C) \to 0$ and $D_N^{(2)}(F) \to 1$.
  - *Proposition 5.2 (Pair B):* Zeroing $C$ on $[2^{2^j}, j 2^{2^j})$ preserves limiting logarithmic word frequencies $2^{-k}$ and disjunctivity while giving $D_\infty^{(2)} = 1$.
  - *Section 6 (Items 1–8):* Isolates obstructions for fixed-support certificates (Stoneham 1973; Bailey–Crandall 2002, Theorem 4.8, p. 535), overlaps/prescribed starts, nearby Taylor cutoffs (external input: Hadamard 1896 PNT), balanced trace sources ($X^2-1$ vs. $X^2+1$ equal-modulus comparison), prime-by-prime statistics, higher-rank density (external input: Furstenberg 1967, Theorem IV.1, p. 48), complex product endpoints $P_N(a_N, e(x))$, and irrationality exponents/runs (external input: van der Poorten–Shallit 1992, pp. 240–242).

### 4. Computability on digit-program names (Lemma 7.1, Proposition 7.2, Theorems 7.3–7.4, Corollary 7.5; AC-11)

- **Evidence:** Lemma 7.1, Theorem 7.3, Theorem 7.4, and Corollary 7.5 are **Lean-supported paper proof**; Proposition 7.2 is **Paper proof**. Each individual component declaration in `ComputableNormalityUndecidability.lean` is kernel-verified at `e4809cf` under explicit endpoint hypotheses, while the two-way transcendence deduction (applying `transcendental_add_rat` to $\pm q$), bundling of components, endpoint existence (Proposition 7.2), and the partial-decider consequence (Corollary 7.5) are written deductions.
- **Exact statements:** Let `Names code s` mean $\forall n, \varphi_{\mathrm{code}}(n) = s(n) \in \{0,1\}$, and `TranscendentalZeroOnePromise s` mean $V(s)$ is transcendental over $\mathbb Q$ and $D_N^{(2)}(V(s)) \to 0$ or $1$. Given computable endpoints $a, b_*$ with transcendental values, $V(a)$ binary normal, and $D_N^{(2)}(V(b_*)) \to 1$ (constructed elementarily by Liouville's polynomial test in Proposition 7.2), bounded-evaluation halting switches produce total computable s-m-n maps into promised names reducing $\overline{K_0}$ and $K_0$ to binary normality. Hence no computable, c.e., or co-c.e. predicate on `Nat.Partrec.Code` (and no partial correct decider halting on all promised names) decides or recognizes binary normality on the promise.
- **Prior-art positioning:** Framed strictly as an elementary formalizable two-limit promise reduction, distinct in hierarchy and domain from unrestricted completeness classifications (Ki–Linton 1994, boldface Borel $\boldsymbol{\Pi}^0_3$-completeness for fixed-base normality; Becher–Heiber–Slaman 2014, Theorem 3.2 and Corollaries 3.3–3.4, p. 67, effective and boldface $\Pi^0_3$-completeness for absolute and fixed-base normality; Becher–Slaman 2014, Theorem 1, index $\Sigma^0_4$- and boldface $\boldsymbol{\Sigma}^0_4$-completeness for normality to at least one base) and from online prefix-generation algorithms (Lutz–Mayordomo 2016/2021, Theorem 5.5, arXiv p. 17).

### 5. Consistency-relative Rosser independence (Theorem 8.1, Remark 8.2; AC-11)

- **Evidence:** **Paper proof** (external input: Rosser 1936, Theorem II).
- **Exact statement:** For $T \in \{\mathrm{PA}, \mathrm{ZFC}\}$, switching from $C$ to $F$ at the first proof code $p \le n$ witnessing the Rosser predicate $W(p)$ yields an effectively specified primitive recursive stream $s_T$ such that $T \vdash \mathsf{Norm}(s_T) \leftrightarrow R$, so consistency of $T$ alone implies $T \nvdash \mathsf{Norm}(s_T)$ and $T \nvdash \neg\mathsf{Norm}(s_T)$. In the standard natural numbers under that consistency hypothesis, $s_T$ is the unmodified binary Champernowne stream $C$. Remark 8.2 notes the weak-arithmetic boundary ($Q$ vs. PA; $I\Delta_0 + \neg\mathrm{Exp}_2$, where $\mathrm{Exp}_2$ is $\forall x\,\exists y\,(y=2^x)$) and explicitly states that the results establish neither normality nor independence for any named classical constant ($\ln 2, \pi, e, \sqrt{2}$, Erdős–Borwein).

---

## Reproduction links

### Pinned Lean 4 baseline (`e4809cf561573aef588e6ffc491a35cdb79fd9ec`)

- **Repository baseline:** https://github.com/eldernos/MathematicsResearch/tree/e4809cf561573aef588e6ffc491a35cdb79fd9ec
- **Finite script (checks $C$, $F$, Stoneham, edits, switches, Pairs A & B; not Proposition 7.2's stream $a$):** `python -B scripts/phase17_limitations.py` (https://github.com/eldernos/MathematicsResearch/blob/e4809cf561573aef588e6ffc491a35cdb79fd9ec/scripts/phase17_limitations.py)
- **Checkpoint verification record:** https://github.com/eldernos/MathematicsResearch/blob/e4809cf561573aef588e6ffc491a35cdb79fd9ec/notes/phase18/verification.md

### Manuscript revision files (version 2.0; postdates `e4809cf`)

*(Pin to the immutable `manuscripts-v2.0.0` release tag once published.)*

- **LaTeX source:** https://github.com/eldernos/MathematicsResearch/blob/manuscripts-v2.0.0/papers/04-arithmetic-certificates-v2/paper.tex
- **Lean 4 check file (`Check.lean`, 30 declarations audited against `propext`, `Classical.choice`, `Quot.sound`):** https://github.com/eldernos/MathematicsResearch/blob/manuscripts-v2.0.0/papers/04-arithmetic-certificates-v2/Check.lean
- **Verification map & novelty ledger:** https://github.com/eldernos/MathematicsResearch/blob/manuscripts-v2.0.0/papers/04-arithmetic-certificates-v2/VERIFICATION.md · https://github.com/eldernos/MathematicsResearch/blob/manuscripts-v2.0.0/papers/04-arithmetic-certificates-v2/LEDGER.md

---

## Specific steps on which human specialist review is requested

1. **Prior art and quantifier structure for overlap rigidity (Theorem 3.1 / Corollary 3.2):** Does an equivalent finite-overlap separation or denominator-constancy obstruction for aligned fixed-support rational models appear in the Korobov/Vandehey or symbolic-dynamics literature, and is the quantifier structure of Theorem 3.1 / Corollary 3.2 sound?
2. **Section 6, Items 3, 6, and 7:** Verification of (i) the uniform $h=o(K)$ nearby-Taylor affine-combination denominator rate via PNT prime bands (Item 3), (ii) the $M_N$ sparse construction (Item 6), and (iii) the moving-parameter complex-product endpoint counterexample and $D^+(x)<1 \iff \liminf N^{-1}\sum_{n<N} E(2^n x) > 0$ equivalence (Item 7).
3. **Elementary Liouville-normal endpoint (Proposition 7.2):** Verification of the unfinished-copy error bound $\ell_j/S_{j-1} \le 2/[j(j-1)]$ and periodic-rational Liouville approximation $2^{-S_j} \le q_j^{-(j+1)^2}$ for $V(a)$.
4. **Computability positioning and promise-restricted references (Section 7):** Confirmation that our framing of `TranscendentalZeroOnePromise` on `Names` cleanly distinguishes our elementary formalizable reduction from Ki–Linton (1994), Becher–Heiber–Slaman (2014, 2015), and Becher–Slaman (2014), and whether other computability references address promise-restricted normality recognition.
5. **PA-internal frequency transfer in Theorem 8.1:** Verification that the explicit uniform integer error bound $|2^k A_C(N)-N| \le 2^k(k+5)2^r$ and the $p + 1 + \lfloor\log_2 N\rfloor < N/4$ bound for $F$ formalize $T \vdash \mathsf{Norm}(s_T) \leftrightarrow R$ cleanly in PA (and in ZFC's natural numbers) without hidden analytic assumptions.
