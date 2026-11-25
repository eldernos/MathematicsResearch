"""Independent checks for the review of notes/phase19/nonlinear.md.

Written without importing or copying scripts/phase19_nonlinear.py.

1. Exact isolation: for (p,s,d) and level H, a primitive center x0 = c/p^H (p not
   dividing c) is counted when no jump of M mod p^(sH+1), from any pair at all,
   lies within x-distance 1/(8H p^H) of x0 other than x0 itself. The jump there must be
   2 p^(sH) mod p^(sH+1). The script reports the isolated fraction of centers in x
   in [1/2, 5/2] and the hit count B_H.
2. Main term: competitor endpoints within eps/(H p^H) of p^-H Z, counted with
   ordered multiplicity, against the equidistribution prediction (2 eps/H) * #endpoints.
3. Failed measure: the relative length of E_L = {u in [1,p^d): M(u) = 0 mod p^L}.
4. Freezing: for the flagship (b,p,s,d,t) = (2,3,1,3,2) the normalized shifted
   prefix p^(2J) b^(-n) R_n of the ordered square, computed from the original indices,
   agrees with M(u) mod p^L at every breakpoint in shells J = 4, 5.

Run: python -B notes/phase19/reviews/nonlinear-check.py
"""
import numpy as np


def numerators(p, h):
    a = np.arange(1, p ** (h + 1), dtype=np.int64)
    return a[a % p != 0]


def jump_table(p, s, d, H, mod):
    """Locations (u scaled by p^(dH)) and weights mod `mod` of all pairs of loss <= H.

    Also returns the locations of pairs with both coordinates different from 1."""
    S = p ** H
    top = (p * S) ** d
    locs, wts, comp = [], [], []
    for h in range(H + 1):
        A = numerators(p, h) * (S // p ** h)
        for k in range(H - h + 1):
            w = pow(p, s * (h + k), mod)
            if w == 0:
                continue
            B = numerators(p, k) * (S // p ** k)
            U = A[:, None] ** d + B[None, :] ** d
            keep = U < top
            locs.append(U[keep])
            wts.append(np.full(int(keep.sum()), w, dtype=np.int64))
            notone = (A[:, None] != S) & (B[None, :] != S) & keep
            comp.append(U[notone])
    U = np.concatenate(locs)
    W = np.concatenate(wts)
    order = np.argsort(U, kind="stable")
    U, W = U[order], W[order]
    uniq, idx = np.unique(U, return_index=True)
    Wc = np.add.reduceat(W, idx) % mod
    nz = Wc != 0
    return uniq[nz], Wc[nz], np.unique(np.concatenate(comp))


def isolation(p, s, d, H, lo=0.5, hi=2.5):
    mod = p ** (s * H + 1)
    S = p ** H
    base = S ** d
    q = 8 * H  # radius 1/(8H) in units of p^-H
    U, W, comp = jump_table(p, s, d, H, mod)
    centers = [c for c in range(int(np.ceil(lo * S)), int(hi * S) + 1) if c % p]
    good = 0
    for c in centers:
        left = base + -((-(q * c - 1) ** d) // q ** d)  # ceil
        right = base + ((q * c + 1) ** d) // q ** d    # floor
        uc = base + c ** d
        i, j = np.searchsorted(U, [left, right + 1])
        inside = U[i:j]
        if inside.size == 1 and int(inside[0]) == uc:
            assert int(W[i]) == (2 * p ** (s * H)) % mod
            good += 1
        else:
            # A nonisolated center must be spoiled by a competitor, never by the grid family.
            ci, cj = np.searchsorted(comp, [left, right + 1])
            assert cj > ci
    return good / len(centers), len(centers)


def main_term(p, d, H, eps_list, lo=0.5, hi=2.5):
    """Compare competitor hits near p^-H Z with the equidistribution prediction.

    Returns (predicted, measured...) for B_H / (eps * #primitive centers), where the
    prediction is (2 eps / H) * #(ordered competitor endpoints in [lo, hi]).
    Uses floating cube roots, which is adequate for these statistics."""
    S = p ** H
    base = S ** d
    total, hits = 0, {e: 0 for e in eps_list}
    for h in range(H + 1):
        A = numerators(p, h) * (S // p ** h)
        A = A[A != S]
        for k in range(H - h + 1):
            B = numerators(p, k) * (S // p ** k)
            B = B[B != S]
            U = (A[:, None] ** d + B[None, :] ** d).ravel()
            U = U[U > base]
            X = np.cbrt((U - base).astype(np.float64))
            X = X[(X >= lo * S) & (X <= hi * S)]
            total += X.size
            dist = np.abs(X - np.rint(X))
            for e in eps_list:
                hits[e] += int((dist <= e / H).sum())
    centers = sum(1 for c in range(int(np.ceil(lo * S)), int(hi * S) + 1) if c % p)
    return 2 * total / (H * centers), [hits[e] / (e * centers) for e in eps_list]


def failed_fraction(p, s, d, L):
    H = (L - 1) // s
    U, W, _ = jump_table(p, s, d, H, p ** L)
    S = p ** H
    top, left = float((p * S) ** d), float(S ** d)
    M = np.cumsum(W) % p ** L
    edges = np.append(U, int((p * S) ** d)).astype(np.float64)
    lens = np.clip(edges[1:], left, None) - np.clip(edges[:-1], left, None)
    measure = lens[M == 0].sum() + max(0.0, edges[0] - left)
    return measure / (top - left)


def v(n, p):
    e = 0
    while n % p == 0:
        n //= p
        e += 1
    return e


def freezing(J, L):
    b, p, s, d, t = 2, 3, 1, 3, 2
    mod = p ** L
    H = (L - 1) // s
    U, W, _ = jump_table(p, s, d, H, mod)
    Mcum = np.cumsum(W) % mod
    # direct pairs from the original indices i, j < p^(J+1)
    idx = np.arange(1, p ** (J + 1), dtype=np.int64)
    vals = np.array([v(int(i), p) for i in idx])
    inv = pow(b, -t, mod)
    unit = np.array([pow(inv, int(i) ** d, mod) for i in idx], dtype=np.int64)
    wt = np.array([pow(p, s * (J - int(e)), mod) for e in vals], dtype=np.int64)
    term = (wt * unit) % mod
    loc = idx[:, None] ** d + idx[None, :] ** d  # i^d + j^d <= n / t
    tw = (term[:, None] * term[None, :]) % mod
    lo, hi = p ** (d * J), p ** (d * (J + 1))
    keep = loc < hi
    loc, tw = loc[keep], tw[keep]
    order = np.argsort(loc, kind="stable")
    loc, tw = loc[order], tw[order]
    cum = np.cumsum(tw) % mod
    last = np.append(loc[1:] != loc[:-1], True)  # last entry of each breakpoint
    sel = np.nonzero(last & (loc >= lo))[0]
    m = loc[sel]  # cutoff n = t*m, so u = m / p^(dJ)
    # M(u) at precision L: pairs on the grid p^(-H) with scaled location <= u p^(dH)
    scaled = m // p ** (d * (J - H))
    r = np.searchsorted(U, scaled, side="right")
    model = np.where(r > 0, Mcum[np.maximum(r - 1, 0)], 0)
    assert np.all((cum[sel] - model) % mod == 0)
    # also just below each breakpoint (cutoff m - 1)
    below = np.searchsorted(loc, m, side="left") - 1
    scaled_b = (m - 1) // p ** (d * (J - H))
    rb = np.searchsorted(U, scaled_b, side="right")
    model_b = np.where(rb > 0, Mcum[np.maximum(rb - 1, 0)], 0)
    ok = below >= 0
    assert np.all((cum[below[ok]] - model_b[ok]) % mod == 0)
    return sel.size


if __name__ == "__main__":
    for p, s, d, Hmax in [(3, 1, 3, 9), (3, 2, 3, 6), (5, 1, 3, 5), (3, 1, 4, 6)]:
        for H in range(2, Hmax + 1):
            frac, n = isolation(p, s, d, H)
            print(f"isolation (p,s,d)=({p},{s},{d}) H={H}: {frac:.3f} of {n} centers")
    for H in range(6, 11):
        pred, meas = main_term(3, 3, H, [1 / 8, 1 / 32])
        print(f"main term (3,3) H={H}: predicted {pred:.3f}, measured "
              + ", ".join(f"{m:.3f}" for m in meas))
    for L in range(1, 12):
        print(f"failed measure L={L}: {failed_fraction(3, 1, 3, L):.4e}")
    for J, L in [(4, 3), (5, 3), (5, 4)]:
        print(f"freezing J={J} L={L}: {freezing(J, L)} breakpoints agree")
