"""Figure 7: proof-dependency map from common techniques, through intermediate
frameworks, to the principal theorems.

The layout is drawn by hand. The edge claims are checked mechanically:
``compute`` parses the ``import`` and ``public import`` lines of every module under
NormalityChecker/, builds the module import graph, and asserts that

* for every solid edge, each module of the source node is transitively imported by a
  module of the target node (the shortest import path is recorded), and some
  public declaration of the source module is referenced by name in a module on such a
  path (a cheap guard against imports that carry no mathematics);
* every foundation module is imported by all eight principal result modules;
* the dashed edges are not logical dependencies: the cyclotomic classification is not
  imported by the signed-shell theorem, and none of the public declarations of the
  order-one joint-failure module is referenced by any other module.

The dashed edges record research history (results.md, Phase 10 and Phase 11 tables;
commit order). The dotted edge is a published theorem used only on paper.
"""

from __future__ import annotations

from collections import deque
import json
import pathlib
import re

from svg import Svg, fmt

SLUG = "proof-dependency-map"
ROOT = pathlib.Path(__file__).resolve().parent.parent.parent
LEAN = ROOT / "NormalityChecker"

RESULTS = ["ST-01", "ST-05", "DS-01", "DS-03", "DS-04", "CR-01", "LS-01", "MW-01"]

META = {
    "number": 7,
    "summary": 'Which techniques the principal theorems use. Solid edges are checked against the Lean import graph; dashed edges are historical, not logical.',
    "title": "Proof-dependency map: which common mathematical techniques support the main theorems",
    "caption": (
        "Techniques (left) feed intermediate frameworks (centre) and the eight principal theorems "
        "(right), grouped by family: Stoneham polynomial images and joint uniformity (ST-01, ST-05), "
        "exact signed-shell discrepancy, translation and spectrum (DS-01, DS-03, DS-04), the "
        "cyclotomic classification (CR-01), and the unsigned finite-support dichotomy with its "
        "polynomial-weight extension (LS-01, MW-01). Every solid edge is verified by the figure "
        "generator against the Lean import graph: each module of the source is transitively "
        "imported by the target, and a declaration of the source is referenced along the import "
        "path. Dashed edges are historical, not logical: the order-one joint-failure formula of "
        "Phase 10 preceded the all-orders theorem, and the cyclotomic checker preceded the "
        "signed-shell analysis; the generator checks that neither is used as a dependency. The "
        "dotted edge marks Ridout's theorem, a published input used only on paper for the "
        "transcendence corollary of signed expansions (DS-07). All eight theorem modules also import the "
        "definition of normality, Weyl's criterion and the Fourier test."
    ),
    "alt": (
        "Node-link diagram in three columns. Left column, techniques: upper-orthant sums with "
        "K(p) congruent to 1 mod p minus 1; short-orbit cancellation on a fixed prime support; "
        "shell counting of signed phases; discrepancy of rational orbits; complete-orbit "
        "character sums; p-adic lift of cell coefficients; recurrence on the logarithmic circle; "
        "finite differences and finite-ray separation. Middle column, frameworks: rational-prefix "
        "normality certificate; discrepancy on selected positions; Ridout's theorem as a paper "
        "input; insertion-cell model; the order-one joint-failure formula of Phase 10 as a "
        "historical node; persistent failed regions with exact discrepancy at all orders; "
        "polynomial masks. Right column, results ST-01, ST-05, DS-01, DS-03, DS-04, CR-01, LS-01, "
        "MW-01. Solid arrows: orthant sums and the certificate to ST-01, ST-01 to ST-05; "
        "short-orbit cancellation to the certificate, certificate to selected positions, which "
        "with shell counting feeds DS-01; DS-01 to DS-03 and DS-04; rational orbits to DS-03; "
        "orbit sums and p-adic lifts to the cell model, which feeds CR-01; recurrence, finite "
        "differences and persistent regions to LS-01; LS-01 and polynomial masks to MW-01. "
        "Dashed arrows: CR-01 to DS-01 and the order-one formula to persistent regions, both "
        "historical. A dotted arrow from Ridout's theorem to DS-01. A band at the bottom states "
        "that all eight result modules import the definition of normality, Weyl's criterion and "
        "the Fourier test."
    ),
    "provenance": "exact",
    "results": RESULTS,
    "sources": [
        "NormalityChecker/StonehamPolynomial.lean",
        "NormalityChecker/StonehamJoint.lean",
        "NormalityChecker/SignedShellDiscrepancy.lean",
        "NormalityChecker/TranslatedShells.lean",
        "NormalityChecker/ShellHistories.lean",
        "NormalityChecker/CyclotomicClassification.lean",
        "NormalityChecker/UnsignedNormality.lean",
        "NormalityChecker/FullPolynomialNormality.lean",
        "notes/results.md",
        "notes/stoneham-powers-products.md",
        "notes/signed-shell-discrepancy.md",
        "notes/unsigned-finite-support.md",
        "notes/arithmetic-certificates.md",
    ],
}

# -- nodes ------------------------------------------------------------------------------
# id: (column, centre y, label lines, modules, kind)
# kind: technique | framework | result | historical | paper
NODES = {
    # Stoneham family
    "orth": (1, 138, ["Upper-orthant sums", "K(p) ≡ 1 mod (p − 1)"],
             ["StonehamPolynomialOrthant"], "technique"),
    "short": (1, 196, ["Short-orbit cancellation", "on a fixed prime support"],
              ["SmoothOrbit", "OrbitDifferencing", "StonehamOrder"], "technique"),
    "cert": (2, 196, ["Rational-prefix", "normality certificate"],
             ["ArithmeticCertificate", "CertificateBlocks"], "framework"),
    "ST-01": (3, 138, ["Polynomial images", "of Stoneham numbers"], ["StonehamPolynomial"], "result"),
    "ST-05": (3, 196, ["Joint uniformity of", "Stoneham powers"], ["StonehamJoint"], "result"),
    # signed shells
    "supp": (2, 254, ["Discrepancy on", "selected positions"], ["SupportDiscrepancy"], "framework"),
    "shell": (1, 296, ["Shell counting of", "signed phases"], ["SignedPhases"], "technique"),
    "ridout": (2, 330, ["Ridout's theorem, for", "transcendence (DS-07)"], [], "paper"),
    "rat": (1, 366, ["Discrepancy of", "rational orbits"],
            ["RationalOrbitCycle", "CircleDiscrepancy", "SharpDiscrepancy"], "technique"),
    "DS-01": (3, 258, ["Exact signed-shell", "discrepancy"], ["SignedShellDiscrepancy"], "result"),
    "DS-03": (3, 320, ["Rational translation", "of signed shells"], ["TranslatedShells"], "result"),
    "DS-04": (3, 380, ["Attainable", "discrepancy spectrum"], ["ShellHistories"], "result"),
    # cyclotomic
    "comp": (1, 436, ["Complete-orbit", "character sums"], ["OrbitSum", "StonehamOrbit"], "technique"),
    "padic": (1, 490, ["p-adic lift of", "cell coefficients"], ["CyclotomicLift"], "technique"),
    "cell": (2, 462, ["Insertion-cell model", "and cell limits"],
             ["Insertion", "CellModel", "CyclotomicCell"], "framework"),
    "CR-01": (3, 456, ["Cyclotomic", "classification"], ["CyclotomicClassification"], "result"),
    # unsigned supports
    "joint1": (2, 580, ["Order-one joint failure", "formula (Phase 10)"], ["JointPersistent"], "historical"),
    "rec": (1, 548, ["Recurrence on the", "logarithmic circle"], ["UnsignedRotation"], "technique"),
    "pers": (2, 638, ["Persistent failed regions", "and all-order discrepancy"],
             ["PersistentRegion", "HigherOrderCells", "DiscrepancyChecker", "HigherOrderDiscrepancy"],
             "framework"),
    "diff": (1, 672, ["Finite differences,", "finite-ray separation"],
             ["UnsignedWeights", "UnsignedRays"], "technique"),
    "mask": (2, 706, ["Polynomial masks,", "local valuations"],
             ["PolynomialMasks", "MaskedSeries", "MaskClassification"], "framework"),
    "LS-01": (3, 594, ["Unsigned finite-", "support dichotomy"], ["UnsignedNormality"], "result"),
    "MW-01": (3, 656, ["Full-support rational", "polynomial weights"], ["FullPolynomialNormality"],
              "result"),
}

FOUNDATION = ["Basic", "Analysis.Weyl", "FourierTest"]

# (source, target, style, routing)
#   style: solid | dashed | dotted
#   routing: "h"   cubic with horizontal tangents between facing sides
#            "v"   straight vertical arrow between stacked boxes in one column
#            "arc" loop on the right of column 3 (offset in px)
# Source/target ports are y offsets from the node centres.
EDGES = [
    ("orth", "ST-01", "solid", ("h", 0, 0)),
    ("short", "cert", "solid", ("h", 0, 0)),
    ("cert", "ST-01", "solid", ("h", 0, 10)),
    ("ST-01", "ST-05", "solid", ("v",)),
    ("cert", "supp", "solid", ("v",)),
    ("supp", "DS-01", "solid", ("h", 0, -8)),
    ("shell", "DS-01", "solid", ("h", 0, 4)),
    ("ridout", "DS-01", "dotted", ("h", 0, 14)),
    ("DS-01", "DS-03", "solid", ("v",)),
    ("rat", "DS-03", "solid", ("h", 0, 8)),
    ("DS-01", "DS-04", "solid", ("arc", 12, 8, 0)),
    ("comp", "cell", "solid", ("h", 0, 0)),
    ("padic", "CR-01", "solid", ("h", 0, 13)),
    ("cell", "CR-01", "solid", ("h", 0, -1)),
    ("CR-01", "DS-01", "dashed", ("arc", 24, 0, -14)),
    ("joint1", "pers", "dashed", ("v",)),
    ("rec", "LS-01", "solid", ("h", 0, -13)),
    ("pers", "LS-01", "solid", ("h", 0, 0)),
    ("diff", "LS-01", "solid", ("h", 0, 13)),
    ("LS-01", "MW-01", "solid", ("v",)),
    ("mask", "MW-01", "solid", ("h", 0, 10)),
]

# Historical justification for dashed edges (results.md and commit order).
HISTORY = {
    ("CR-01", "DS-01"): (
        "The cyclotomic checker for prime-parameter Stoneham sums (commit a11e0aa, 10th commit) "
        "preceded the exact discrepancy of signed Stoneham phases (commit 5c2e7d8, 27th commit). "
        "SignedShellDiscrepancy does not import CyclotomicClassification."),
    ("joint1", "pers"): (
        "results.md, Phase 10: Lean proves the exact limiting discrepancy formula at order one "
        "(commit b731ad7); Phase 11: the all-orders, all-prefix persistent discrepancy theorem "
        "(commit 10a24c0). HigherOrderDiscrepancy imports JointPersistent, but no public "
        "declaration of JointPersistent is referenced by any other module."),
}
PAPER = {
    ("ridout", "DS-01"): (
        "results.md, Phase 10: transcendence of signed expansions follows on paper using Roth or "
        "Ridout (notes/signed-shell-discrepancy.md). No Lean module."),
}

# -- geometry ---------------------------------------------------------------------------
W, H = 720, 822
COLX = {1: (24, 208), 2: (244, 428), 3: (462, 688)}
BOX_H = 42


def box(node):
    col, cy, *_ = NODES[node]
    x0, x1 = COLX[col]
    return x0, cy - BOX_H / 2, x1, cy + BOX_H / 2


# -- import graph -----------------------------------------------------------------------

def module_name(path: pathlib.Path) -> str:
    return ".".join(path.relative_to(LEAN).with_suffix("").parts)


IMPORT = re.compile(r"^\s*(?:public\s+)?(?:meta\s+)?import\s+(NormalityChecker\.\S+)")
DECL = re.compile(r"^(?:@\[[^\]]*\]\s*)?(?:noncomputable\s+)?(?:protected\s+)?"
                  r"(?:theorem|lemma|def|abbrev|structure|class|inductive)\s+([^\s(:{\[]+)")


def import_graph():
    graph, text = {}, {}
    for path in sorted(LEAN.rglob("*.lean")):
        name = module_name(path)
        src = path.read_text()
        text[name] = src
        graph[name] = sorted({m.group(1)[len("NormalityChecker."):]
                              for line in src.splitlines() if (m := IMPORT.match(line))})
    return graph, text


def closure(graph, start):
    seen, todo = set(), [start]
    while todo:
        for d in graph.get(todo.pop(), []):
            if d not in seen:
                seen.add(d)
                todo.append(d)
    return seen


def shortest_path(graph, a, b):
    queue, prev = deque([a]), {a: None}
    while queue:
        u = queue.popleft()
        if u == b:
            out = []
            while u is not None:
                out.append(u)
                u = prev[u]
            return out[::-1]
        for v in graph.get(u, []):
            if v not in prev:
                prev[v] = u
                queue.append(v)
    return None


def public_declarations(text):
    """Public declarations per module as (innermost namespace, short name) pairs, and the
    namespaces each module enters."""
    decls, spaces = {}, {}
    for mod, src in text.items():
        names, stack, entered = set(), [], set()
        for line in src.splitlines():
            if line.startswith("namespace "):
                parts = line.split()[1].split(".")
                stack.append(parts)
                entered.add(parts[-1])
            elif line.startswith("end ") and stack and line.split()[1].split(".")[-1] == stack[-1][-1]:
                stack.pop()
            m = DECL.match(line)
            if m:
                full = m.group(1).split(".")
                ns = full[-2] if len(full) > 1 else (stack[-1][-1] if stack else "")
                names.add((ns, full[-1]))
        decls[mod], spaces[mod] = names, entered
    return decls, spaces


def word(pattern: str):
    return re.compile(r"(?<![\w.'])" + pattern + r"(?![\w'])")


def compute():
    graph, text = import_graph()
    clo = {m: closure(graph, m) for m in graph}
    decls, spaces = public_declarations(text)
    owners: dict[str, set[str]] = {}
    for mod, names in decls.items():
        for _ns, n in names:
            owners.setdefault(n, set()).add(mod)
    for node, (_c, _y, _l, mods, kind) in NODES.items():
        for m in mods:
            assert m in graph, (node, m)
        assert (kind == "paper") == (not mods), node
    for r in RESULTS:
        assert NODES[r][4] == "result" and len(NODES[r][3]) == 1

    def uses(n, ns, source_mod, m):
        """Does module m refer to declaration ns.n of source_mod?  Accepted forms: the
        qualified name ns.n; a distinctive short name (six or more characters, defined in one
        module only); or the bare name inside the same namespace."""
        if ns and ns != "NormalityChecker" and word(re.escape(f"{ns}.{n}")).search(text[m]):
            return True
        bare = word(re.escape(n)).search(text[m]) is not None
        if bare and len(n) >= 6 and owners[n] == {source_mod}:
            return True
        defined_here = any(k == n for _s, k in decls[m])
        return bare and ns in spaces[m] and ns != "NormalityChecker" and not defined_here

    def referenced(source_mod, target_mod):
        """A public declaration of ``source_mod`` named in a module that lies on an import
        path from ``target_mod`` down to ``source_mod``."""
        between = [m for m in sorted(clo[target_mod] | {target_mod})
                   if m != source_mod and (source_mod in clo[m])]
        for ns, n in sorted(decls[source_mod], key=lambda d: (-len(d[1]), d)):
            for m in between:
                if uses(n, ns, source_mod, m):
                    return (f"{ns}.{n}" if ns and ns != "NormalityChecker" else n), m
        return None

    verified = []
    for src, dst, style, _route in EDGES:
        if style != "solid":
            continue
        for s in NODES[src][3]:
            hits = [t for t in NODES[dst][3] if s in clo[t]]
            assert hits, f"solid edge {src} -> {dst}: no module of {dst} imports {s}"
            t = hits[0]
            use = referenced(s, t)
            assert use, f"solid edge {src} -> {dst}: no declaration of {s} used on a path from {t}"
            verified.append({"edge": [src, dst], "target_module": t, "source_module": s,
                             "import_path": shortest_path(graph, t, s),
                             "declaration_used": use[0], "used_in": use[1]})
    foundation = []
    for r in RESULTS:
        t = NODES[r][3][0]
        for f in FOUNDATION:
            assert f in clo[t], (r, f)
            foundation.append({"result": r, "module": t, "imports": f,
                               "import_path": shortest_path(graph, t, f)})

    # dashed edges are not logical dependencies
    assert "CyclotomicClassification" not in clo["SignedShellDiscrepancy"]
    assert "JointPersistent" in clo["HigherOrderDiscrepancy"]
    joint_names = []
    for ns, n in sorted(decls["JointPersistent"]):
        users = [m for m in text if m != "JointPersistent" and uses(n, ns, "JointPersistent", m)]
        assert not users, (n, users)
        joint_names.append(n)
    historical = [{"edge": list(k), "justification": v} for k, v in HISTORY.items()]
    paper = [{"edge": list(k), "justification": v} for k, v in PAPER.items()]
    for src, dst, style, _ in EDGES:
        if style == "dashed":
            assert (src, dst) in HISTORY
        if style == "dotted":
            assert (src, dst) in PAPER
    return {"verified": verified, "foundation": foundation, "historical": historical,
            "paper": paper, "modules": len(graph),
            "joint_public_declarations_unused": joint_names}


def data_files(data):
    nodes = {k: {"column": c, "label": " ".join(l), "modules": m, "kind": kind}
             for k, (c, _y, l, m, kind) in NODES.items()}
    edges = [{"source": s, "target": t, "style": st} for s, t, st, _ in EDGES]
    out = {"description": ("Proof-dependency map. Solid edges are checked against the import graph "
                           "of NormalityChecker/**/*.lean: each source module is transitively "
                           "imported by a target module (shortest path recorded) and a public "
                           "declaration of the source is referenced on such a path. Dashed edges "
                           "are historical; dotted edges are paper-only inputs."),
           "modules_parsed": data["modules"], "foundation_modules": FOUNDATION,
           "nodes": nodes, "edges": edges, "verified_solid_edges": data["verified"],
           "foundation_imports": data["foundation"], "historical_edges": data["historical"],
           "paper_inputs": data["paper"],
           "joint_persistent_public_declarations_unused": data["joint_public_declarations_unused"]}
    return {"proof-dependency-map.json": json.dumps(out, indent=1, ensure_ascii=False) + "\n"}


# -- drawing ----------------------------------------------------------------------------

def arrow_right(s, x, y, colour):
    s.path(f"M{fmt(x)} {fmt(y)} l-7 -3.6 v7.2 z", fill=colour)


def arrow_left(s, x, y, colour):
    s.path(f"M{fmt(x)} {fmt(y)} l7 -3.6 v7.2 z", fill=colour)


def arrow_down(s, x, y, colour):
    s.path(f"M{fmt(x)} {fmt(y)} l-3.6 -7 h7.2 z", fill=colour)


DASH = {"solid": None, "dashed": "6 4", "dotted": "1.5 3.5"}


def draw_edge(s, t, src, dst, style, route):
    colour = t.ink2
    dash = DASH[style]
    sw = 1.6
    sx0, sy0, sx1, sy1 = box(src)
    tx0, ty0, tx1, ty1 = box(dst)
    if route[0] == "v":
        x = (max(sx0, tx0) + min(sx1, tx1)) / 2 if NODES[src][0] == NODES[dst][0] else sx1
        s.line(x, sy1, x, ty0 - 1, colour, sw=sw, dash=dash)
        arrow_down(s, x, ty0, colour)
        return
    if route[0] == "arc":
        off, ps, pt = route[1], route[2], route[3]
        y1 = (sy0 + sy1) / 2 + ps
        y2 = (ty0 + ty1) / 2 + pt
        xr = sx1 + off
        r = 8
        d = (f"M{fmt(sx1)} {fmt(y1)} H{fmt(xr - r)} Q{fmt(xr)} {fmt(y1)} {fmt(xr)} "
             f"{fmt(y1 + (r if y2 > y1 else -r))} V{fmt(y2 + (-r if y2 > y1 else r))} "
             f"Q{fmt(xr)} {fmt(y2)} {fmt(xr - r)} {fmt(y2)} H{fmt(tx1 + 6)}")
        s.path(d, stroke=colour, sw=sw, dash=dash)
        arrow_left(s, tx1, y2, colour)
        return
    ps, pt = route[1], route[2]
    y1 = (sy0 + sy1) / 2 + ps
    y2 = (ty0 + ty1) / 2 + pt
    x1, x2 = sx1, tx0
    if NODES[dst][0] - NODES[src][0] == 2:
        # cross the middle column horizontally, then bend in the right-hand gap
        xm = COLX[2][1] + 4
        gap = x2 - xm
        d = (f"M{fmt(x1)} {fmt(y1)} H{fmt(xm)} C{fmt(xm + gap * 0.55)} {fmt(y1)} "
             f"{fmt(x2 - gap * 0.55)} {fmt(y2)} {fmt(x2 - 6)} {fmt(y2)}")
    else:
        gap = x2 - x1
        d = (f"M{fmt(x1)} {fmt(y1)} C{fmt(x1 + gap * 0.55)} {fmt(y1)} "
             f"{fmt(x2 - gap * 0.55)} {fmt(y2)} {fmt(x2 - 6)} {fmt(y2)}")
    s.path(d, stroke=colour, sw=sw, dash=dash)
    arrow_right(s, x2, y2, colour)


def draw_node(s, t, node):
    col, cy, lines, _mods, kind = NODES[node]
    x0, y0, x1, y1 = box(node)
    if kind == "result":
        s.rect(x0, y0, x1 - x0, y1 - y0, fill=t.surface, stroke=t.ink, sw=1.6, rx=8)
        s.text(x0 + 10, cy - 4, node, size=13, weight="700")
        s.text(x0 + 60, cy - 4, lines[0], size=13)
        s.text(x0 + 60, cy + 13, lines[1], size=13)
        return
    extra = ""
    if kind == "historical":
        extra = ' stroke-dasharray="6 4"'
    elif kind == "paper":
        extra = ' stroke-dasharray="1.5 3.5"'
    sw = 1.4 if kind == "framework" else 1
    stroke = t.ink2 if kind == "framework" else t.rule
    if kind in ("historical", "paper"):
        stroke = t.ink2
    fill = t.panel if kind in ("technique", "framework") else t.surface
    s.rect(x0, y0, x1 - x0, y1 - y0, fill=fill, stroke=stroke, sw=sw, rx=6, extra=extra)
    ink = t.ink if kind in ("technique", "framework") else t.ink2
    s.text(x0 + 10, cy - 4, lines[0], size=13, fill=ink)
    s.text(x0 + 10, cy + 13, lines[1], size=13, fill=ink)


def render(data, t):
    s = Svg(W, H, t, META["title"], META["alt"])
    s.heading("Proof-dependency map", "Which common techniques support the principal theorems")
    s.badge("exact", y=20)
    for col, label in ((1, "Techniques"), (2, "Frameworks"), (3, "Principal results")):
        s.text(COLX[col][0], 102, label, size=13, weight="600", fill=t.ink2)
    for col in (1, 2, 3):
        s.line(COLX[col][0], 110, COLX[col][1], 110, t.rule)

    for src, dst, style, route in EDGES:
        draw_edge(s, t, src, dst, style, route)
    for node in NODES:
        draw_node(s, t, node)

    # foundation band
    fy = 744
    s.rect(24, fy, W - 48, 40, fill=t.panel, stroke=t.rule, rx=6)
    s.text(36, fy + 17, "Imported by all eight theorem modules:", size=13, weight="600")
    s.text(36, fy + 33, "definition of normality, Weyl's criterion, Fourier test of normality",
           size=13, fill=t.ink2)

    # legend
    ly = H - 20
    items = [("solid", "dependency, verified in Lean imports"),
             ("dashed", "historical, not logical"),
             ("dotted", "paper-only input")]
    x = 24
    widths = (300, 200, 160)
    for (style, label), w in zip(items, widths):
        s.line(x, ly - 4, x + 26, ly - 4, t.ink2, sw=1.8, dash=DASH[style])
        s.text(x + 32, ly + 1, label, size=13, fill=t.ink2)
        x += w
    return s.done()
