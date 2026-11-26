# Reviewer inquiry drafts (for the owner; not to be sent)

Placeholders in square brackets must be filled in by the owner. No email addresses are included.

## Inquiry 1: two-point correlations for e(θV)χ(U) at almost all scales

Subject: A question on Theorem 3.1 of "Quantitative correlations and some problems on prime factors of consecutive integers"

Dear [Name],

I am writing about your paper with [co-author] (arXiv:2512.01739, v2), specifically Theorem 3.1 and Theorem 1.7. I have posted a research note on the binary digits of the Erdős–Borwein constant E = Σ τ(m)2^(−m) (it is not a claim of normality or non-normality; it is AI-assisted and has had no human review). Writing τ(m) = 2^V(m)·U(m) with U(m) odd, the note reduces a sufficient condition for a digit frequency different from 1/2 (its Theorem 5.1) to the joint law of (V, U mod 2^16) at about log log N consecutive integers. For the two-point case it isolates a hypothesis (Hypothesis E): a saving of o((A√T)^(−1)), with T = log log N, uniformly in shifts |k| ≤ A√T, for correlations of g_θ(m) = e(θV(m))χ(U(m)) with χ a character modulo 2^r.

The closest prior work I know is your Theorem 3.1, which gives a saving L^(−c) at almost all scales for 1-bounded multiplicative functions g_1, g_2, with g_1 non-pretentious (or equidistributed) and shifts h_1 ≠ h_2 = O(L^c). Your Theorem 1.7 gives P(τ(n) = τ(n+1)) = (c_τ + O(log_2^(−c) x)) / (2√(π log_2 x)) outside an exceptional set of scales. The family g_θ takes the value e(θ) at every prime (since τ(p) = 2 gives V(p) = U(p) = 1), which is the prime-value pattern of the test function e(αΩ(n)) in your Section 4.1. My reading (and that of a referee model) is that your Section 4.1 computation bounds the pretentious distance of g_θ from below by ≫ R^(−2) log_2 X for 1/R ≤ ‖θ‖ ≤ 1/2, so that the non-pretentious case (ii) of Theorem 3.1 applies to g_θ at each fixed θ in that range, with L = exp(c_0 R^(−2) log_2 X), and, after integrating over θ as in your (4.4), gives an L^1-in-θ saving at almost all scales. I may well be misreading the hypotheses of case (ii).

**Questions.** (1) Is this reading of case (ii) correct for g_θ, including the uniformity in the shifts (|k| up to a small power of log log N) and in the characters modulo 2^r? (2) Is there a way to obtain a single exceptional set of scales that works simultaneously for all θ with 1/R ≤ ‖θ‖ ≤ 1/2? (A crude θ-net seems to need about log N points, which is too many.) The step I cannot see how to take is from two-point to r-point correlations with r ≥ 3 (the note shows that r ≥ 9 would be needed for an argument using only moment information of 16 columns); do you know of an approach?

The note and its verification map are at [link to released note]. I would be grateful for any pointer and will credit any correction.

With thanks,
Christopher Anderson (Independent Researcher)

## Inquiry 2: a sharp lower bound for E(−1)^N from binomial moments

Subject: Is the sharp bound Σ_{k≤r}(−2)^k/k! for E(−1)^N, given Poisson binomial moments, in the literature?

Dear [Name],

I am writing about Bonferroni-type inequalities and sharp bounds for count variables with prescribed lower binomial moments, in the tradition of M. Sibuya (Ann. Inst. Statist. Math. 43 (1991), 261–285) and J. Galambos and I. Simonelli (*Bonferroni-type inequalities with applications*, Springer, 1996). In a research note on the binary digits of the Erdős–Borwein constant I prove (Theorem 7.1) that for odd r and any law of N on the non-negative integers with E C(N,k) = 1/k! for 1 ≤ k ≤ r (the first r binomial moments of a Poisson(1) variable), E(−1)^N ≥ e_r = Σ_{k≤r}(−2)^k/k!, with equality for an explicit law on {0,…,r}. The value e_r first becomes positive at r = 5 (e_5 = 1/15) and increases to e^(−2). For even r the infimum is e_(r−1) and is not attained (Proposition 7.2). The pointwise inequality Σ_{k≤r}(−2)^k C(n,k) ≤ (−1)^n for odd r is verified in Lean (`parity_bonferroni_dual_le`); the rest is a short written proof.

This is an instance of the majorant–minorant method for the moment space, extended from {0,…,n} to the non-negative integers. A referee model read Sibuya (1991) and found no statement of the parity functional E(−1)^N or of this value (the paper treats P(N = m) and P(N ≥ m)); I have not located it in Galambos–Simonelli either, but I may have missed it.

**Question.** Is the sharp value of inf E(−1)^N, over laws whose first r (odd) binomial moments are those of Poisson(1), already in the literature, and if so where?

The note is at [link to released note]. It is AI-assisted and has not been reviewed by a human specialist; I would be grateful for any correction.

With thanks,
Christopher Anderson (Independent Researcher)
