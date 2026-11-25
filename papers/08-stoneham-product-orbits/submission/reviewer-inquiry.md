# Draft Specialist Review Inquiries (for Owner Approval; Do Not Send Directly)

## Template 1: Discrepancy and short-orbit estimates for Stoneham products

**To:** [Name]  
**Subject:** Brief question on a preprint concerning discrepancy and $p$-adic cancellation in Stoneham products

Dear Professor [Name],

I am directing an AI-assisted mathematics project (with partial Lean 4 formalization) and preparing a preprint draft, *Exceptional Orbits and Discrepancy of Stoneham Products* (v1.0). The manuscript has not yet been read by an independent human specialist, and I am writing to ask one targeted question where your work is directly relevant.

In Theorem A and Theorem 2.1 of the draft, we study the binary product $x = \alpha(2,3)\alpha(2,5)$ and show that its subsequential empirical shift measures are mixtures of Lebesgue measure and $\{3,5\}$-smooth binary cycles, with $D^+(x) \le 4/11 + 2.85 \times 10^{-10}$ and $D^+(x) \le 4/11 \iff C_0 \le 4/11$, where $C_0$ is the upper density of integer shifted prefixes (ordinary normality remains open). Our block-counting step relies on a qualitative fixed-support short-orbit estimate patterned on your Corollary 1.2 in *Differencing methods for Korobov-type exponential sums* (*J. Anal. Math.* 138, 2019, 405–439), together with a circle-perturbation transfer across atomic endpoints.

Could you advise whether the empirical-mixture discrepancy transfer (Theorem 2.1) and the zero-slack reduction to $C_0 \le 4/11$ (Section 5) are sound as stated, and whether you are aware of any prior results bounding the discrepancy of products of Stoneham or Korobov series on distinct prime axes? I would be glad to share the short reviewer packet (with exact statements, proofs, and pinned Lean/Python verification links) if you have time to look.

Best regards,  
Christopher Anderson  
Independent Researcher  
(Project repository: `https://github.com/eldernos/MathematicsResearch`)

---

## Template 2: Simultaneous $p$-adic approximation of implicitly defined Mahler roots

**To:** [Name]  
**Subject:** Question on $p$-adic approximation of implicit roots arising from Stoneham products

Dear Professor [Name],

I am directing an AI-assisted research project preparing a preprint draft, *Exceptional Orbits and Discrepancy of Stoneham Products* (v1.0), which has not yet received independent human review. Your monograph *Distribution Modulo One and Diophantine Approximation* (Cambridge Univ. Press, 2012) and your paper with M. Laurent (*J. Number Theory* 61, 1996, 311–342) on $p$-adic distances between powers of algebraic numbers are directly relevant to the arithmetic obstruction we encounter.

In Propositions 3.1–3.2 and Theorem 3.3 of the draft, reducing the $3$-adic and $5$-adic prefix denominators of $\alpha(2,3)\alpha(2,5)$ on each nonrectangular shape $(a,d)$ leads to unique $p$-adic zeros $\zeta_{3,a,d} \in \Z_3$ and $\zeta_{5,d,a} \in \Z_5$ of Mahler-interpolated fibre sums. We prove $\zeta_{p,a,d} \notin \Z$ via Eisenstein irreducibility of $X^{q^H} - 2$, and deduce power-tower spacing between exceptional shells and $O_\varepsilon(\log^* T)$ scale sparsity. Similarly, for the dyadic Stoneham quadratic $\alpha(b,2)^2 - 2\alpha(b,2)$, normality is equivalent (by a kernel-verified theorem) to excluding $v_2(k - \kappa_0(b)) \ge k - O(1)$ infinitely often for a $2$-adic parameter $\kappa_0(b) = -C_{\mathrm{int}}(\lambda)/\lambda$ whose intercept series is transcendental as a function of $\lambda$.

One specific question: do you know of any $p$-adic transcendence or Diophantine-approximation method that could establish an irrationality/algebraic-type measure $v_p(m - \zeta) = o(m)$ (or even rule out super-exponential integer approximations) for such implicitly defined Mahler-series roots at a fixed integer base $B$, or any literature where this specific obstruction has been analyzed? A short reviewer packet is ready if it would be useful.

Best regards,  
Christopher Anderson  
Independent Researcher  
(Project repository: `https://github.com/eldernos/MathematicsResearch`)
