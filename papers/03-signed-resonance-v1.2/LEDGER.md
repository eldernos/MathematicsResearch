# Claim-to-source ledger: Paper III, version 1.2

This ledger restates the literature comparison recorded for version 1.1 ([REVIEW.md](REVIEW.md), searches of 24 November 2026) in the Wave 2 format. Priority is provisional. We have not located the exact statements below in the sources examined, and a failed search does not establish novelty. No human specialist has reviewed these comparisons.

### Theorem 3 (CR-01): cyclotomic resonance for finite rational combinations
- **Statement and hypotheses:** for an odd prime *p* not dividing *b* and rational weights on finitely many radix-dilated Stoneham-type components with parameter *p*, the sum is normal in base *b* exactly when the cyclotomic polynomial of order ord<sub>*p*</sub>(*b*) divides no cell polynomial.
- **Evidence:** Kernel-verified (`cyclotomic_normal_iff`, `cyclotomicNormalTest_correct`).
- **Earliest relevant literature:** Stoneham, Acta Arith. 16 (1970), DOI 10.4064/aa-16-3-239-254; Kano, Osaka J. Math. (1993), DOI 10.18910/10356; Kano–Shiokawa, Israel J. Math. (1993), DOI 10.1007/BF02760950; Wagner, J. Number Theory (1995), DOI 10.1006/jnth.1995.1114.
- **Closest published results:** Bailey–Borwein, Ramanujan J. (2012), DOI 10.1007/s11139-012-9417-3, which studies nonnormality in other bases and poses the two-sum question. The normal-ring literature establishes additive normality in specific constructions.
- **Closest public-repository results:** Captain Sude, *Stoneham-sum-normal* (pinned f4d3d1f01d00c57425c684409849053e58e42261), which fixes the construction radix for two standard constants.
- **Relation:** different setting (weights on dilated components on one prime axis). Apparently new in the sources examined.
- **Outstanding review:** the clearing factor (*p* − 1)·*D* for coincident insertions and signed weights.

### Theorem 1 (DS-01, DS-03): discrepancy of signed expansions at every prefix
- **Statement:** the discrepancy equals the proportion of positions in zero-phase shells up to *o*(1). Rational translation multiplies the main term by the rational-orbit discrepancy.
- **Evidence:** Kernel-verified.
- **Earliest relevant literature:** Stoneham's successive-difference construction (1970); Kano, Theorem 1 (sufficient nondivisibility criterion); Vandehey, arXiv:1606.07911, §7 (incomplete-orbit bounds).
- **Relation:** the eventually unit-phase case already satisfies Kano's normality test. The exact all-prefix discrepancy formula was not located in the sources examined.

### Theorem 7 and Corollary 8 (DS-04): the attainable spectrum
- **Statement:** the attainable upper discrepancies are exactly the base-*p* values, with digits 0 and *p* − 1, of binary words that dominate all their suffixes lexicographically.
- **Evidence:** Kernel-verified.
- **Closest published results:** Kaneko–Steiner (DOI 10.1112/mtk.12250) study exactly these lexicographic sup-words, their closure and the first positive word. Baiocchi–Komornik (arXiv:0710.3001), Theorem 2.5(a), treat quasi-greedy expansions of one. Allouche (DOI 10.1051/ita:2007058) uses a complementary suffix restriction. Carminati–Tiozzo (DOI 10.1017/etds.2015.135), §2, give the doubling-hole parameter set, which equals the reflection of the binary spectrum.
- **Relation:** the symbolic set is inherited from this literature, which is credited in the paper. The identification with a discrepancy spectrum is the contribution.

### Proposition 9 and Theorem 11: small positive discrepancy and normal summands
- **Earliest relevant literature:** de Bruijn (1946) for cyclic words; Becher–Carton (DOI 10.1016/j.jco.2019.03.003) for the discrepancy of necklace constructions.
- **Relation:** the manuscript uses a single finite rational cycle with a translation product. Theorem 11 is a specific explicit pair.

**Search record:** see the query strings in [REVIEW.md](REVIEW.md#literature-search-and-priority). No new search was run for version 1.2. Phase 19 adds no signed-shell results ([audit](../wave2-audits/paper-III-audit.md)).
