# Review of the Phase 19 nonlinear note: normality of quadratic images through null shell levels

Status: **preliminary**. This file is updated as the audit proceeds.

This is an independent adversarial review of the Phase 19 claim that every quadratic polynomial in $C(b,p,s,d)$, $d\ge3$, $s\ge1$, is normal to base $b$. The case $s=1$ includes the flagship square $C(2,3,1,3)^2$, which Phase 18 left open with the bound $\limsup D_N<2.94\cdot10^{-10}$. I re-derived the steps by hand and wrote separate numerical checks. I did not reuse the author's code. The earlier proof is [Phase 18 algebra](../../phase18/algebra.md), and the all-prefix criterion is in [Phase 18 principal](../../phase18/principal.md#a-fixed-support-criterion-for-all-prefixes).

## Material reviewed

The author committed the draft as `ff756bd` on `research/phase-19-operations`. Its content matches the working copy in the author's worktree `t3/phase19-nonlinear-zero-set`, apart from math delimiters and line endings.

| File | Blob SHA-1 at `ff756bd` |
|---|---|
| `notes/phase19/nonlinear.md` | `8a6b674ed43ca80377adae47363faf1eb9be8eca` |
| `scripts/phase19_nonlinear.py` | `9432c1156fdc7cc8f7ce517aabab1ae68bed9962` |

`python -B scripts/phase19_nonlinear.py` passes in the author's checkout.

## Preliminary verdict

No gap has been found so far in the square theorem. The chain is:

1. The frozen mass $M(u)\in\mathbb Z_p$ on the shell.
2. Primitive jumps $2p^{sH}$ at $x=c/p^H$, $p\nmid c$, in $x=(u-1)^{1/d}$.
3. A count of competing endpoints through the third-derivative test.
4. A second-moment argument that almost every $x$ lies in infinitely many good intervals.
5. The density-point argument that every level set of $M$ is null.
6. The transfer through the Phase 18 all-prefix criterion.

Each step has been re-derived. The detailed objections and the numerical evidence follow.

## Numerical evidence so far

These are independent implementations, kept for the final review.

**Isolation of primitive centers.** I took $(p,d)=(3,3)$, $x\in[1/2,5/2]$, all competitor pairs of total loss at most $H$, and radius $\epsilon/(H3^H)$. The number $B_H$ of competitor endpoints within that radius of $3^{-H}\mathbb Z$, counted with ordered multiplicity, stays at $B_H\approx4.6\,\epsilon\cdot\#\{\text{primitive centers}\}$ for $6\le H\le10$ and $\epsilon\in\{1/8,1/32,1/128\}$. The fraction of spoiled primitive centers stays at about $1.4\epsilon$. This matches the shape of estimate (1), a constant times $\epsilon|I|p^H$.

**Failed measure.** For the flagship $(p,s,d)=(3,1,3)$, the relative measure of $E_L=\{u\in[1,27):M(u)\equiv0\bmod 3^L\}$ satisfies $3^L|E_L|/26\in[0.79,2.02]$ for $1\le L\le11$. The values are $0.3077$ at $L=1$, which is $8/26$ from the cells $[1,2)\cup[9,16)$, and $1.13\cdot10^{-5}$ at $L=11$. This decay is consistent with an atomless mass whose density near zero is comparable to Haar measure.
