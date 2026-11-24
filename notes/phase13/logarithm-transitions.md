# Binary discrepancy of ln 2 at finite cutoffs

**Theorem.** Let $y_n=\{2^n\ln 2\}$, and let $D_N$ be the supremum over half-open intervals in $[0,1]$ of the absolute difference between their frequency among $y_0,\ldots,y_{N-1}$ and their length. Put $k=\lfloor(\log_{68}N)/2\rfloor$. For every sufficiently large integer $N$,

$$
1-D_N\ \ge\ \frac{k^2}{N}.
$$

This is a kernel-checked consequence of the logarithm's auxiliary integral. It improves the previous finite gap of order $(\log N)/N$ by a factor of order $\log N$. The gain comes from the positions *before* each of several well-separated transitions. The same order is attained by an explicit irrational with maximal limiting discrepancy. The strict inequality $\limsup_N D_N(\ln 2)<1$ remains open here. [New Lean proof](../../NormalityChecker/LogarithmTransitionBounds.lean) · [Integral and dyadic separation](../../NormalityChecker/LogTwoLinearForms.lean) · [Previous transition and middle-third estimates](../transition-discrepancy.md)

Except for the explicitly identified Lean statements, the results below are paper deductions. All logarithms without a base are natural. Write $\|u\|$ for distance to the nearest integer. A transition at $t$ means that the first two bits of $y_t$ differ, or equivalently that $y_t\in[1/4,3/4)$. Use the terminating expansion at dyadic rationals. After `lake build`, check the standalone formalization with `lake env lean NormalityChecker/LogarithmTransitionBounds.lean`.

## From a transition to a discrepancy bound

For a general $x$, write $y_n=\{2^nx\}$. For $0<r\le1/4$, let $g$ be the frequency in $[2r,1-2r)$. For $N\ge2$,

$$
1-D_N(x)\ \ge\ \min(r,g).
$$

For a deficit only intervals of length greater than $1-r$ need consideration, and those contain $[2r,1-2r)$. For an excess only intervals of length less than $r$ matter. Such an interval either misses the interior interval or cannot contain consecutive shifts. Indeed, if it contains $y_n,y_{n+1}$, then $\|y_n\|=\|y_{n+1}-y_n\|<r$, placing the whole interval within $2r$ of an endpoint on that side. With no consecutive visits its frequency is at most $\lceil N/2\rceil/N\le3/4$. The Lean proof includes the half-open endpoint cases. [Interior-frequency inequality](../../NormalityChecker/LogarithmTransitionBounds.lean)

If $t$ is a transition, then $\|y_{t-j}\|\ge2^{-j}/4$ for $0\le j\le t$, by $\|2u\|\le2\|u\|$. In the checked bound the interior interval has left endpoint $a=2^{-k}/4$. In each of the $k$ shells $[s,68s)$ with $s=68^i$ and $k\le i<2k$, the integral-based theorem supplies a transition in $[2s,68s)$. Its last $k$ positions up to and including the transition are inside this shell and inside $[a,1-a)$. Thus $g\ge k^2/N$ for $r=a/2$. Also $k^2/N\le r$ when $k\ge1$ and $N\ge68^{2k}$. This proves the opening theorem at every sufficiently large cutoff, including cutoffs inside the next shell. [Integral-based window](../../NormalityChecker/LogTwoTransitions.lean) · [Shell count and all-prefix bound](../../NormalityChecker/LogarithmTransitionBounds.lean)

### The coefficient from an arithmetic window

Suppose $B>1$ and every sufficiently late $[m,Bm)$ contains a transition. Then

$$
\liminf_{N\to\infty}\frac{N(1-D_N(x))}{(\log N)^2}
\ \ge\ \frac{1}{\log 2\,\log B}. \tag{1}
$$

Fix $A>B$ and $c>1/(\log 2\,\log A)$. Put $r=c(\log N)^2/N$ and $L=\lfloor\log_2(1/(16r))\rfloor$. In every complete shell $[A^j,A^{j+1})$ with $A^j\ge C_{A,B}(L+1)$ use the hypothesis at $m=\lceil A^j\rceil+L$. Choosing $C_{A,B}$ sufficiently large ensures $Bm\le A^{j+1}$. Each chosen transition supplies $L$ positions in its shell with distance at least $2^{-L}/4>2r$ from an integer. The number of these shells is $(\log N-O_{A,B}(\log(L+1)))/\log A+O_{A,B,x}(1)$. Since $L\sim(\log N)/\log 2$, the interior-frequency inequality gives (1) with $A$. Let $A$ decrease to $B$.

Suppose an irrational $x$ satisfies $|x-p/2^m|>2^{-\nu m}$ for all sufficiently large $m$ and all integers $p$. Absence of a transition at the $h$ starts $m,\ldots,m+h-1$ makes the first $h+1$ bits identical. It gives an endpoint approximation with error at most $2^{-(m+h+1)}$. Thus every $B>\nu$ is admissible. The proof also works with estimates initially stated for reduced denominators: reduction only decreases the denominator, and the finitely many small reduced denominators near $x$ have positive minimum distance from it.

| Constant | Arithmetic input | Consequence of (1) |
| --- | --- | --- |
| ln 2 | Repository integral and middle-third window | Coefficient at least $1/(\log 2\,\log 34)$ on paper |
| ln 2 | Marcovecchio, Theorem 1.1, $\mu(\ln2)<3.57455391$ | Coefficient at least $1/(\log 2\,\log 3.57455391)$ |
| ln 2 | Liu–Jiang–Zhang, 2026 preprint, Theorem 1 for $r=2$ | Coefficient at least $1/(\log 2)^2$ |
| π | Zeilberger–Zudilin's bound $\mu(\pi)<7.104$, or the 2026 exponent-two preprint | Coefficients at least $1/(\log 2\,\log 7.104)$ and $1/(\log 2)^2$, respectively |
| $e$ | Euler's continued fraction gives $\mu(e)=2$ | Coefficient at least $1/(\log 2)^2$ |

The 2026 inputs are attributed preprint theorems, independent of the local Lean proof. Each exponent-two application first takes $B>2$ and then passes to $2$ in the coefficient. No uniform $c/q^2$ lower approximation bound is used. For $e$, the partial quotients in Euler's expansion grow at most linearly in their index, and the convergent denominators grow at least as fast as Fibonacci numbers. Thus $\log q_{j+1}/\log q_j\to1$, giving exponent two by the convergent error bounds and Legendre's criterion. [Marcovecchio, Theorem 1.1](https://www.impan.pl/shop/publication/transaction/download/product/82234) · [Liu–Jiang–Zhang, Theorem 1, v3](https://arxiv.org/abs/2610.10192v3) · [Zeilberger–Zudilin](https://arxiv.org/abs/1912.06345) · [2026 π preprint](https://github.com/openai/math/tree/main/preprints/The-irrationality-exponent-of-pi-is-2-September-24-2026) · [Cohn's proof of Euler's expansion](https://arxiv.org/abs/math/0601660)

Rivoal's Padé estimates distinguish pure radix powers from mixed denominators. For ln 2 the pure-power table on p. 936 reports $4.6221$ for its bound. The exponent $1.948967$ in the remark on p. 937 uses the denominator $2^m d_m$, where $d_m$ is the lcm through $m$. Embedding $p/2^m$ in this grid gives an exponent relative to $2^m$ of $1.948967(1+1/\log 2)+o(1)$, by the prime number theorem. It does not give a pure-power exponent below two. [Rivoal, Theorems 1 and 4](https://ems.press/journals/rmi/articles/4766)

## The first Fourier deficit

Set $F(u)=1-\cos(2\pi u)$ and
$$
C_* = \sum_{d=1}^\infty F(2^{-d}).
$$
The first two terms sum to 3 and the remaining terms sum to at most $\pi^2/24$, by $1-\cos v\le v^2/2$. Under the same window hypothesis as (1),

$$
\liminf_{N\to\infty}\frac{1}{\log N}\sum_{n<N}F(2^n x)
\ \ge\ \frac{C_*}{\log B}. \tag{2}
$$

To see the cost of a transition, fix $L\ge2$ and consider one at $t$. If $[t,t+3L]$ contains at least four transitions, its cost is at least $4>C_*$. Otherwise there is a transition $u$ in this interval followed by $L$ consecutive nontransitions within it. Indeed, starting at $t$, if such a stretch fails one finds another transition within $L$ steps, up to three times. The bits then put $y_u$ within $2^{-L}$ of $1/2$. For $0\le j<L$, $\|y_{u-j}\|\ge 2^{-j}(1/2-2^{-L})$. The function $F$ increases on $[0,1/2]$ and has Lipschitz constant $2\pi$. Consequently the sum on $[t-L,t+3L]$ is at least
$$
\sum_{j=0}^{L-1}F(2^{-j-1})-4\pi\,2^{-L}.
$$
In the shell proof of (1), increase the fixed starting threshold so the entire interval $[t-L,t+3L]$ fits inside its shell. For fixed $L$ the number of complete shells is $\log N/\log A+O_{x,A,B,L}(1)$. Take the lower limit first, then $L\to\infty$ and $A\downarrow B$. This proves (2).

For the actual rational sequence $R_0=0$, $R_{n+1}=2R_n+1/(n+1)$, the same coefficient applies to $\sum_{n<N}F(R_n)$. Indeed,
$$
e_n=2^n\ln 2-R_n=\sum_{j\ge1}\frac{2^{-j}}{n+j},\qquad 0<e_n\le\frac{1}{n+1}.
$$
The modulus of $\sin$ is 1-Lipschitz. Since $\sqrt{F(u)}=\sqrt{2}|\sin(\pi u)|$, the reverse triangle inequality for Euclidean norm gives, on every integer interval $I\subseteq[M,\infty)$ with $M\ge1$,
$$
\left|\sqrt{\sum_{n\in I}F(R_n)}-
       \sqrt{\sum_{n\in I}F(2^n\ln2)}\right|
\le \pi\sqrt{2\sum_{n\in I}e_n^2}\le \pi\sqrt{2/M}.
$$
Lean checks the finite tail-interval bound above for every length, using $1/(n+1)^2\le1/n-1/(n+1)$ in the final sum. For prefixes starting at zero the right side is bounded independently of $N$. Hence the two unnormalized sums have ratio tending to one by (2). Bounding each difference of $F$ by $2\pi e_n$ separately would incur an error of order $\log N$, the very scale in (2). The exponent-two logarithm input yields at least $C_*$ per $\log_2 N$ in the lower limit, while the local integral gives $C_*$ per $\log_{34}N$. The normalized mean can still tend to zero. [New Fourier stability theorem](../../NormalityChecker/LogarithmTransitionBounds.lean) · [Logarithmic tail](../../NormalityChecker/LogTwo.lean) · [Existing finite Fourier and transition inequalities](../../NormalityChecker/FirstFrequency.lean)

## A gap caused by the rational recurrence itself

**Proposition.** For every orbit $z_{n+1}=2z_n+1/(n+1)\pmod1$, its first $N\ge256$ terms have interval discrepancy at most $1-1/(8\sqrt N)$. In particular this holds for the actual rational prefixes. The order is sharp uniformly in the initial point.

Put $r=1/(8\sqrt N)$. Discrepancy exceeding $1-r$ would give a circle arc $J$ of length less than $r$ with more than $(1-r)N$ visits. For an excess take the test interval, and for a deficit take its complement. There must be two consecutive visits with first index $n\ge\lceil N/2\rceil$: the last half contains at least $\lfloor N/4\rfloor-1>rN$ disjoint pairs. Such a pair implies $\|z_n+1/(n+1)\|<r$. Consequently every $y\in J$ satisfies $\|y\|<2r+2/N\le3r$. For an earlier consecutive pair with first index $m\ge1$, this would force
$$
\frac1{m+1}=\left\|\frac1{m+1}\right\|
\le \|z_m+1/(m+1)\|+\|z_m\|<4r.
$$
For $m+1\le\sqrt N$ the left side is at least $8r$. Thus each consecutive disjoint pair within indices $1,\ldots,\lfloor\sqrt N\rfloor$ contains a miss. There are more than $rN$ such pairs, a contradiction.

Take now $z_n=-e_n\pmod1$, using the exact logarithmic tail above. This solves the *same* recurrence and shadows the exact orbit of zero. For $n\ge\lceil\sqrt N\rceil$ its terms belong to $[1-1/\sqrt N,1)$, giving a discrepancy at least $1-2/\sqrt N-1/N$. The rational initial condition $R_0=0$ selects ln 2, while this comparison orbit has $z_0=-\ln2\pmod1$. It isolates the amount of dispersion that the forcing alone can produce. In particular a square-root gap measured for the rational prefixes need not transfer at that scale to the exact doubling orbit by the pointwise shadow bound alone.

## Aggregate age and the cosine spikes

For an integer hit set, let $A_0=0$, and put $A_{n+1}=0$ after a hit at $n$ and $A_{n+1}=A_n+1$ otherwise. For $W_N=\sum_{n=0}^N A_n$, if every sufficiently late $[m,Bm)$ contains a hit, then
$$
\limsup_{N\to\infty}\frac{W_N}{N^2}\ \le\ \frac{B-1}{2(B+1)}. \tag{3}
$$
Partition $[0,N+1)$ at the reset positions one past each hit. A segment $[s,e)$ of length $d=e-s$ contributes $d(d-1)/2$. For every $B'>B$ the late segment endpoints satisfy $e\le B's$, also for the final truncated segment. Indeed a hit occurs after or at $s$ and before $Bs$, so the next reset is at most $Bs+1$. Hence
$$
(e-s)^2=\frac{e-s}{e+s}(e^2-s^2)
\le\frac{B'-1}{B'+1}(e^2-s^2).
$$
Summation telescopes, the finitely many initial segments cost $O(1)$, and $B'\downarrow B$ gives (3). Each sufficiently late true transition of ln 2 yields a rational middle-third hit at offset 0, 1 or 2. Thus the exponent-two input gives (3) with constant $1/6$ for the **actual rational middle-third age**, and for the true transition age. This bounds the quadratic-scale coefficient. The linear-scale age bound needed for positive lower hit density is stronger. [Offset theorem](../../NormalityChecker/LogTwoTransitions.lean) · [Age convention and conditional density theorem](../../NormalityChecker/AggregateGaps.lean)

For irrational $x$, set $v_n=-\log|\cos(\pi2^nx)|$. The double-angle identity gives
$$
\sum_{n<N} v_n = N\log2+\log|\sin(\pi x)|-\log|\sin(\pi2^Nx)|.
$$
Since $2\|u\|\le |\sin(\pi u)|\le\pi\|u\|$, the limsup of the mean on the left equals $\lambda_2(x)\log2$, where
$$
\lambda_2(x)=\limsup_{N\to\infty}
   \frac{-\log\min_{p\in\mathbb Z}|x-p/2^N|}{N\log 2}.
$$
Its liminf is $\log2$, since an irrational orbit has infinitely many transitions and sine there is bounded away from zero. In particular the exponent-two input bounds the upper mean for ln 2 by $2\log2$. The following obstruction explains why a bounded first moment at that scale cannot establish uniform control of the excess above a fixed cutoff. [Formal finite cosine identity](../../NormalityChecker/TrigonometricMoments.lean)

### A sharp sparse example

For $K=\sum_{j\ge0}2^{-2^j}$, both limits below exist:
$$
\lim_{N\to\infty}\frac{N(1-D_N(K))}{(\log_2 N)^2}=1,
\qquad
\lim_{N\to\infty}\frac{\sum_{n<N}F(2^nK)}{\log_2 N}=C_*.
$$
Indeed, at $t=s-1$ the first two shifted digits are 10 whenever the digit at $s=2^j$ is an isolated 1. Hence every $B>2$ is admissible. Equations (1) and (2) give the lower bounds. For $n\ge1$, let $s$ be the next power of two strictly above $n$. Then
$$
y_n=2^{n-s}(1+\eta_s),\qquad
\eta_s=\sum_{2^j>s}2^{-(2^j-s)}\le 2^{1-s}.
$$
In $[0,N)$, apart from the first position, $y_n\ge1/N$ can occur only within $\log_2(2N)$ positions before one of at most $\log_2 N+O(1)$ possible powers $s\le2N$. Testing $[0,1/N)$ proves the matching upper bound on the discrepancy gap. On a complete shell $s/2\le n<s$, set $d=s-n$. The Fourier sum differs from $C_*$ by at most $2\pi\eta_s\sum_{d\ge1}2^{-d}+O(4^{-s/2})$, using the Lipschitz and square bounds on $F$. These errors are summable over the shells. The unfinished shell costs $O(1)$ by nonnegativity and the same full-shell bound. This gives the second limit. In particular both normalized statistics are compatible with limiting discrepancy one. [Kernel-checked separation and maximal discrepancy of this constant](../../NormalityChecker/SparseTransitions.lean)

Van der Poorten and Shallit show that $2K$ has bounded partial quotients. Thus $2K$ is badly approximable, and so is $K$, since $|2K-2p/q|=2|K-p/q|$. Both limiting coefficients are therefore optimal even under an ordinary bound $|x-p/q|\gg q^{-2}$ for *all* denominators. [Van der Poorten–Shallit, *Folded continued fractions*](https://web.williams.edu/Mathematics/sjmiller/public_html/book/papers/vdp/PoortenShallit_FoldedContFrac.pdf)

At large $s$, precisely $n=s-1$ in the shell $[s/2,s)$ hits the exact middle third, by the displayed expression for $y_n$. At cutoffs $N=2^j$ the sum of the squared completed segment lengths is $N^2/3+O(1)$, by the geometric series of reset lengths $1,2,4,\ldots,N/2$. Thus $W_N/N^2\to1/6$ along these cutoffs, attaining (3) for $B\downarrow2$. Also $y_{s-1}=(1+\eta_s)/2$ with $2^{-s}\le\eta_s\le2^{1-s}$. This gives $v_{s-1}=s\log2+O(1)$. At $N=s$, this one term forces the mean squared spike to grow at least linearly in $N$. For any fixed cutoff $M$, the spikes at all powers through $N=s$ alone give $\limsup_N N^{-1}\sum_{n<N}(v_n-M)_+\ge2\log2$. The bounded first moment accommodates this concentration.

Even **arbitrarily slow decay** of a prescribed separation lower bound leaves strict limiting discrepancy open. Let $h(n)>0$ be nonincreasing with $h(n)\to0$. Start an integer sequence at $p_1$ with $h(p_1)\le1/4$ and let $p_{j+1}=p_j+\lfloor\log_2(1/h(p_j))\rfloor$. The binary real having ones exactly at these positions is irrational, has transition density zero, and satisfies $\|2^n x\|\ge h(n)$ eventually. For $p_j\le n<p_{j+1}$ its tail is at least $2^{-(p_{j+1}-p_j)}\ge h(p_j)\ge h(n)$ and at most $(1/2)\sum_{i\ge0}4^{-i}=2/3$. The gaps tend to infinity, so the ones and their two neighboring transition starts have density zero. This rules out a density argument based solely on any vanishing single-position lower bound, even one much stronger than the integral estimate.

## A stronger transfer for algebraic irrationals

For every real algebraic irrational $x$ the same interior-interval argument gives
$$
1-D_N(x)\ \gg_x\ \frac{(\log N)^{5/2}}{N\sqrt{\log\log N}}. \tag{4}
$$
In particular (4) applies to the golden ratio. It uses the distribution of *lengths* of digit runs in Bugeaud–Evertse's proof. Their aggregate count of changes on its own would allow many changes to cluster in a short part of the prefix. [Bugeaud–Evertse, §8, (8.1)–(8.3) and Lemma 8.1](https://arxiv.org/abs/0709.1560)

Here are the details. Let $n_j$ denote the positive digit positions at which a run ends, so the transition starts are $n_j-1$. Passing to the fractional part or its complement if needed puts $x$ in the normalization of §8 and preserves the transition positions. Write $d_j=n_{j+1}-n_j$ and $u_j=d_j/n_j$. Equation (8.3) of that paper bounds $1+u_j\le 2\deg x$ eventually (use the degree of the normalized number). Lemma 8.1 gives, for $0<t\le1$ and $n_j\ge\max(U,10/t)$,
$$
\#\{j:u_j\ge t,\ n_j\ge\max(U,10/t)\}\ \ll_x\ t^{-3}\log(2/t),
$$
where $U$ is fixed. Use complete gaps with $\sqrt N\le n_j<n_{j+1}\le N$. Their sum of $\log(1+u_j)$ is at least $\tfrac12\log N-O_x(1)$ by telescoping and the bounded endpoint ratio. For $\epsilon=C_x\sqrt{\log\log N/\log N}$, the cutoff $\sqrt N$ exceeds $\max(U,10/\epsilon)$ eventually. On these complete gaps the total $\log(1+u_j)$ for $u_j>\epsilon$ is $O_x(\epsilon^{-2}\log(2/\epsilon))$. To see this, bound $\log(1+u_j)\le u_j$ and use $\epsilon\#\{u_j>\epsilon\}+\int_\epsilon^{2\deg x}\#\{u_j>t\}\,dt$, bounding the range $t\ge1$ by its count at 1. Choose $C_x$ large enough. The remaining gaps $u_j\le\epsilon$ then carry at least $\tfrac14\log N$ in total log ratio.

Put $r=(\log N)^{5/2}/(N\sqrt{\log\log N})$ and $L=\lfloor\log_2(1/(16r))\rfloor$. In $[n_j,n_{j+1})$, the last $\min(L,d_j)$ starts, ending at transition $n_{j+1}-1$, all lie in the interior test interval. For the remaining gaps,
$$
\min(L,d_j)\ \ge\ (L/\epsilon)\log(1+u_j).
$$
For $d_j\ge L$ this follows from $\log(1+u_j)\le\epsilon$. For $d_j<L$ use $d_j\ge n_j\log(1+u_j)$ and $n_j\ge\sqrt N\ge L/\epsilon$. Summing these disjoint contributions yields $g\gg_x L\log N/(N\epsilon)\gg_x r$. The finite interior-frequency inequality proves (4). The input concerns algebraic irrationals. Deriving a comparable distribution of long runs for ln 2, and ultimately a positive lower density of transitions, would require further arithmetic information.
