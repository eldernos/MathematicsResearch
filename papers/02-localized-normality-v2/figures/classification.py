"""Render selected cases of the unsigned classification. Requires pycairo."""
from pathlib import Path
import csv

import cairo


HERE = Path(__file__).resolve().parent
SUPPORTS = [(), (2,), (3,), (5,), (2, 3), (2, 5), (3, 5), (2, 3, 5)]
BASES = [2, 3, 5, 6, 10, 15, 30]
WIDTH, HEIGHT = 440, 206


def limit(base, support):
    return int(all(base % p == 0 for p in support))


def support_label(support):
    return "{" + ", ".join(map(str, support)) + "}" if support else "∅"


def draw(surface):
    ctx = cairo.Context(surface)
    ctx.set_source_rgb(1, 1, 1)
    ctx.paint()
    ctx.select_font_face("DejaVu Sans")

    def label(x, y, text, size, color=(0.10, 0.15, 0.18)):
        ctx.set_font_size(size)
        _, _, width, _, _, _ = ctx.text_extents(text)
        ctx.set_source_rgb(*color)
        ctx.move_to(x - width / 2, y)
        ctx.show_text(text)

    label(42, 17, "Support", 10)
    label(257, 13, "Radix", 10)
    left, top, w, h = 77, 36, 50, 20
    for j, base in enumerate(BASES):
        label(left + (j + 0.5) * w, top - 5, str(base), 10)
    for i, support in enumerate(SUPPORTS):
        y = top + i * h
        label(42, y + 14, support_label(support), 10)
        for j, base in enumerate(BASES):
            value = limit(base, support)
            x = left + j * w
            bg = (0.12, 0.31, 0.39) if value else (0.90, 0.94, 0.94)
            fg = (1, 1, 1) if value else (0.13, 0.27, 0.32)
            ctx.set_source_rgb(*bg)
            ctx.rectangle(x, y, w - 1, h - 1)
            ctx.fill()
            label(x + w / 2, y + 14, str(value), 11, fg)
    surface.finish()


if __name__ == "__main__":
    with (HERE / "classification.csv").open("w", newline="") as out:
        writer = csv.writer(out, lineterminator="\n")
        writer.writerow(["support", *BASES])
        for support in SUPPORTS:
            writer.writerow([support_label(support), *(limit(b, support) for b in BASES)])
    pdf = cairo.PDFSurface(str(HERE / "classification.pdf"), WIDTH, HEIGHT)
    pdf.set_metadata(cairo.PDF_METADATA_TITLE, "Finite-support interval discrepancy limits")
    pdf.set_metadata(cairo.PDF_METADATA_CREATE_DATE, "2026-11-24T00:00:00Z")
    draw(pdf)
    draw(cairo.SVGSurface(str(HERE / "classification.svg"), WIDTH, HEIGHT))
