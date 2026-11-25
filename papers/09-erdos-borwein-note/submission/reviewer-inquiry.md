# Reviewer inquiry drafts (for the owner; not to be sent)

Placeholders in square brackets must be filled in by the owner. No email addresses are included.

## Inquiry 1: two-point correlations for e(θV)χ(U) at almost all scales

Subject: A question on Theorem 3.1 of "Quantitative correlations and some problems on prime factors of consecutive integers"

Dear [Name],

I am writing about your paper with [co-author] (arXiv:2512.01739, v2), specifically Theorem 3.1 and Theorem 1.7. I have posted a research note on the binary digits of the Erdős–Borwein constant E = Σ τ(m)2^(−m) (it is not a claim of normality or non-normality; it is AI-assisted and has had no human review). Writing τ(m) = 2^V(m)·U(m) with U(m) odd, the note reduces a sufficient condition for a digit frequency different from 1/2 (its Theorem 5.1) to the joint law of (V, U mod 2^16) at about log log N consecutive integers. For the two-point case it isolates a hypothesis (Hypothesis E): a saving of o((A√T)^(−1)), with T = log log N, uniformly in shifts |k| ≤ A√T, for correlations of g_θ(m) = e(θV(m))χ(U(m)).

The closest prior work I know is your Theorem 3.1. It gives a saving L^(−c) at almost all scales for 1-bounded multiplicative functions g_1, g_2, with g_1 non-pretentious (or equidistributed) and shifts h_1 ≠ h_2 = O(L^c). Your Theorem 1.7 treats P(τ(n) = τ(n+1)). I have not verified whether the family g_θ, which depends on θ and N and takes the value e(θ) at every prime, satisfies the non-pretentiousness inequality (3.3) uniformly in θ, nor whether the technical condition (3.2) near primes in [exp(log^(1/11) X), exp(log^(1/10) X)] can be arranged.

**Question.** Does your method (Theorem 3.1) apply to g_1 = e(θV)χ(U), uniformly for 1/L ≤ ‖θ‖ ≤ 1/2 with L a small power of log log N and χ a character modulo 2^16? If not, which hypothesis fails?

The note and its verification map are at [link to released note]. I would be grateful for any pointer and will credit any correction.

With thanks,
Christopher Anderson (Independent Researcher)

## Inquiry 2: a sharp lower bound for E(−1)^N from binomial moments

Subject: Is the sharp bound Σ_{k≤r}(−2)^k/k! for E(−1)^N, given Poisson binomial moments, in the literature?

Dear [Name],

I am writing about [Bonferroni-type inequalities and sharp bounds for distributions on {0,…,n} with prescribed lower binomial moments; the closest work I found is by Sibuya, Ann. Inst. Statist. Math. (exact reference to be confirmed by the owner), or by [other author]]. In a research note on the binary digits of the Erdős–Borwein constant I prove (Theorem 7.1) that for odd r and any law of N on the non-negative integers with E C(N,k) = 1/k! for 1 ≤ k ≤ r (the first r binomial moments of a Poisson(1) variable), E(−1)^N ≥ e_r = Σ_{k≤r}(−2)^k/k!, with equality for an explicit law on {0,…,r}. The value e_r first becomes positive at r = 5 (e_5 = 1/15) and increases to e^(−2). The pointwise inequality Σ_{k≤r}(−2)^k C(n,k) ≤ (−1)^n for odd r is verified in Lean (`parity_bonferroni_dual_le`); the rest is a short written proof.

This looks like an instance of the majorant–minorant method for Bonferroni-type inequalities, but I could not find the statement in the sources I examined and do not know whether it is a known special case.

**Question.** Is the sharp value of inf E(−1)^N, over laws whose first r (odd) binomial moments are those of Poisson(1), already in the literature, and if so where?

The note is at [link to released note]. It is AI-assisted and has not been reviewed by a human specialist; I would be grateful for any correction.

With thanks,
Christopher Anderson (Independent Researcher)
