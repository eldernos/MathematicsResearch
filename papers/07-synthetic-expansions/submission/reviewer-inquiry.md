# Reviewer inquiry templates (drafts for the owner; not to be sent as is)

These drafts use placeholders only. Before sending, check that the cited paper is the addressee's own, and adjust the wording. Each template asks one question.

---

## Inquiry 1: the normality switch and Korobov-type criteria

Dear [Name],

I am writing about a preprint draft, *Synthetic Arithmetic Expansions and Prescribed Discrepancy*. Its first theorem concerns the series

$$X_s=\sum_{k\ge1}p^{-s v_p(k)}\,b^{-n_k},$$

where $p\nmid b$ is prime, $t=\operatorname{ord}_p(b)$, and $(n_k)$ is any strictly increasing sequence of multiples of $t$ with $n_k\ge k^2$. The theorem says that $X_s$ is normal to base $b$ for every $s\ge1$, while its extreme discrepancy tends to one for $s=0$. After the $K$th insertion the reduced denominator of the shifted prefix is exactly $p^{s\lfloor\log_pK\rfloor}$. This statement and the switch have been checked in Lean 4; the written proof of the positive side combines the exact prefix denominators with a fixed-support short-orbit estimate, the qualitative content of your Corollary 1.2.

Your work [cite: e.g. *Differencing methods for Korobov-type exponential sums*, J. Anal. Math. 138 (2019), or the addressee's relevant paper] gives the closest results I found. Theorem 7.4 there treats series $\sum1/(c_kb^{m_k})$ with $c_k\mid c_{k+1}$ supported on a fixed finite set of primes. The insertion denominators $p^{sv_p(k)}$ drop back to one whenever $p\nmid k$, although the prefix denominators do form a chain, and on the cubic schedule grouping consecutive insertions produces unbounded normalized numerators, so I have not been able to deduce the switch from that theorem or from Kano's Theorem 1 (Osaka J. Math. 30 (1993), p. 911).

**Question.** Is the switch, under some representation of the series, a known consequence of the Korobov–Stoneham–Kano criteria or of your work, and if so which reference should be cited?

The manuscript was produced in an AI-assisted research project. The denominator identity and the switch are checked by the Lean 4 kernel; the written proofs and the literature comparisons have been checked only by AI models and await review by a human specialist.

The verification map and the exact Lean statements are at <https://github.com/eldernos/MathematicsResearch/blob/manuscripts-v2.0.0/papers/07-synthetic-expansions/VERIFICATION.md>.

With thanks,
Christopher Anderson

---

## Inquiry 2: normality of the square of a valuation-weighted series

Dear [Name],

A preprint draft of mine proves that for $\xi=\sum_{k\ge1}3^{-v_3(k)}2^{-2k^3}$ the number $\xi^2$ is normal to base $2$ and that $(\xi,\xi^2)$ is jointly normal; more generally every rational polynomial of total degree two in the series $\sum_ip^{-av_p(i)}b^{-ti^d}$, for an integer $d\ge3$ and distinct orders $a$, is normal. The leading $p$-adic residue of the shifted prefixes of $\xi^2$ vanishes on a set of shifts of positive lower density, so the linear method does not apply. The proof shows instead that the limiting $p$-adic mass $M(u)$ of the normalized prefixes, a $\mathbb Z_p$-valued function of the position $u$ of the shift in its $p$-adic shell whose reduction modulo each power of $p$ is a finite step function, has Lebesgue-null level sets. Primitive jumps on the grids $p^{-H}\mathbb Z$ are isolated in positive proportion by a third-derivative van der Corput estimate for the curves $x=(z^d+y^d-1)^{1/d}$, and a second-moment argument shows that almost every point lies in infinitely many isolated neighbourhoods.

Your work on [cite: the addressee's paper on rings of normal numbers, e.g. Kano and Shiokawa, *Rings of normal and nonnormal numbers*, Israel J. Math. 84 (1993), whose Theorem 5 gives rings all of whose nonzero elements are normal to one base] is the closest published work I found; those rings already contain normal polynomial images of their generators, which have rapidly separated exponents.

**Question.** Is normality of polynomial images known for generators on a polynomial schedule such as $ti^d$, where consecutive positions have ratio tending to one?

The manuscript was produced in an AI-assisted research project. The quadratic theorem is a written proof that has been checked only by AI models and has not been formalized; it awaits review by a human specialist.

With thanks,
Christopher Anderson
