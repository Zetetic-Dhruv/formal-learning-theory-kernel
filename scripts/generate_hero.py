#!/usr/bin/env python3
"""
Generate the two-panel hero SVG for the README.

Left panel: Fundamental theorem pentagon (what the kernel formalizes)
Right panel: Measurability arc (what the kernel discovered)

The right panel is derived from the measurability arc table in Section V.
Metrics line auto-generated from scripts/metrics.sh output.

Usage:
    python3 scripts/generate_hero.py
    # Outputs: premise/hero.svg
"""

import json
import subprocess
import os

REPO_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))


def get_metrics():
    """Run metrics.sh and parse output."""
    result = subprocess.run(
        ['bash', os.path.join(REPO_ROOT, 'scripts', 'metrics.sh')],
        capture_output=True, text=True, cwd=REPO_ROOT
    )
    return json.loads(result.stdout)


# The measurability arc steps -- the only manually curated data.
# Add new rows here when new results are proved.
ARC_STEPS = [
    ("Correction", "NullMeasurableSet suffices", "Weakens FTSL hypothesis"),
    ("Separation", "Borel-analytic gap is strict", "Witness: singleton class"),
    ("Prediction", "VersionSpace is MBL", "Non-neural RL policy gate"),
    ("Descent", "Interpolation weakens to NullMeas", "Spatial composition"),
    ("Amalgamation", "Evidential composition preserves", "Interpolation as corollary"),
    ("Closure", "MBL closed under 4 operations", "Measurable learner monad"),
]


def generate_svg(metrics):
    W = 1100
    H = 580
    MID = 480  # vertical divider x

    lines = []
    lines.append(f'<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 {W} {H}" font-family="\'Times New Roman\',serif">')
    lines.append('  <style>text{font-family:\'Times New Roman\',serif}</style>')
    lines.append(f'  <rect width="{W}" height="{H}" fill="#fff"/>')

    # ============================================================
    # LEFT PANEL: Pentagon
    # ============================================================
    cx, cy, r = 220, 220, 120
    import math
    # Pentagon vertices (top, upper-right, lower-right, lower-left, upper-left)
    verts = []
    for i in range(5):
        angle = -math.pi/2 + 2*math.pi*i/5
        verts.append((cx + r*math.cos(angle), cy + r*math.sin(angle)))

    # Title
    lines.append('  <text x="220" y="42" font-size="17" font-weight="bold" fill="#000" text-anchor="middle">Known Theory, Machine-Checked</text>')

    # Pentagon edges (solid except compression edge which is dashed)
    for i in range(5):
        x1, y1 = verts[i]
        x2, y2 = verts[(i+1) % 5]
        dash = ' stroke-dasharray="5 3"' if i == 3 or i == 4 else ''
        lines.append(f'  <line x1="{x1:.0f}" y1="{y1:.0f}" x2="{x2:.0f}" y2="{y2:.0f}" stroke="#000" stroke-width="1.2"{dash}/>')

    # Vertex dots
    for i, (vx, vy) in enumerate(verts):
        if i == 4:  # compression: open circle
            lines.append(f'  <circle cx="{vx:.0f}" cy="{vy:.0f}" r="3" fill="none" stroke="#000" stroke-width="1"/>')
        else:
            lines.append(f'  <circle cx="{vx:.0f}" cy="{vy:.0f}" r="3.5" fill="#000"/>')

    # Center label
    lines.append(f'  <text x="{cx}" y="{cy+5}" font-size="14" font-weight="bold" fill="#000" text-anchor="middle">VCDim(C) &lt; &#x221E;</text>')

    # Vertex labels
    labels = [
        ("PAC Learnable  \u2713", 0, -20, "middle"),
        ("Rademacher\nvanishes  \u2713", 30, -5, "start"),
        ("Growth \u2264\nSauer-Shelah  \u2713", 20, 20, "start"),
        ("Sample\ncomplexity  \u2713", -20, 20, "end"),
        ("Compression\nscheme  \u25CA", -30, -5, "end"),
    ]
    for i, (label, dx, dy, anchor) in enumerate(labels):
        vx, vy = verts[i]
        sublabels = label.split('\n')
        for j, sub in enumerate(sublabels):
            lines.append(f'  <text x="{vx+dx:.0f}" y="{vy+dy+j*14:.0f}" font-size="11" fill="#000" text-anchor="{anchor}">{sub}</text>')

    # Equivalence note
    lines.append(f'  <text x="{cx}" y="370" font-size="11" fill="#000" text-anchor="middle" font-style="italic">4/5 conjuncts proved, sorry-free</text>')

    # ============================================================
    # FIRST FORMALIZATIONS: flowing box list below pentagon
    # ============================================================
    FORMALIZATIONS = [
        "Littlestone char.",
        "Gold's theorem",
        "Mind change char.",
        "PAC-Bayes",
        "Baxter multi-task",
        "Choquet capacity",
        "Analytic measurability",
        "Paradigm separations",
        "NFL (infinite X)",
        "Symmetrization chain",
    ]

    lines.append(f'  <text x="{cx}" y="400" font-size="12" font-weight="bold" fill="#000" text-anchor="middle">First Formalizations</text>')

    # ============================================================
    # RIGHT PANEL: Measurability Arc (compute layout first to get bottom Y)
    # ============================================================
    rx = MID + 40
    lines.append(f'  <text x="{rx + 260}" y="42" font-size="17" font-weight="bold" fill="#000" text-anchor="middle">New Mathematics, Machine-Checked</text>')

    step_y_start = 80
    step_box_h = 30
    step_w = 520
    name_col_w = 120
    n_steps = len(ARC_STEPS)

    # Compute step_h so the bottom of the last arc box aligns with the
    # bottom of the formalization flow area. We target the arc bottom to
    # land around y=480 (leaving room for summary text + metrics).
    arc_target_bottom = H - 110  # leave room for fixed summary box at H-70
    step_h = (arc_target_bottom - step_y_start - step_box_h) / max(n_steps - 1, 1)

    # Now lay out the formalization flow boxes to fill from y=415 down to
    # the same arc_target_bottom, with row spacing matching step_h
    box_h = 20
    box_pad = 6
    gap_x = 5
    flow_x = 15
    flow_y = 415
    max_flow_x = MID - 15
    # Compute how many rows the flow uses, then set vertical gap to fill
    # available space. First pass: count rows.
    row_count = 1
    test_x = 15
    for label in FORMALIZATIONS:
        box_w = len(label) * 6.5 + box_pad * 2
        if test_x + box_w > max_flow_x:
            test_x = 15
            row_count += 1
        test_x += box_w + gap_x
    # Distribute rows evenly between flow_y and arc_target_bottom
    flow_total_h = arc_target_bottom - flow_y
    gap_y = (flow_total_h - row_count * box_h) / max(row_count - 1, 1) if row_count > 1 else 0
    gap_y = max(gap_y, 4)  # minimum gap

    # Second pass: actually draw
    cur_x = 15
    cur_y = flow_y
    for label in FORMALIZATIONS:
        box_w = len(label) * 6.5 + box_pad * 2
        if cur_x + box_w > max_flow_x:
            cur_x = 15
            cur_y += box_h + gap_y
        lines.append(f'  <rect x="{cur_x:.0f}" y="{cur_y:.0f}" width="{box_w:.0f}" height="{box_h}" fill="#fff" stroke="#000" stroke-width="0.5"/>')
        lines.append(f'  <text x="{cur_x + box_w/2:.0f}" y="{cur_y + 14:.0f}" font-size="9" fill="#000" text-anchor="middle">{label}</text>')
        cur_x += box_w + gap_x

    # ============================================================
    # DIVIDER (spans both panels)
    # ============================================================
    lines.append(f'  <line x1="{MID}" y1="60" x2="{MID}" y2="{H-50}" stroke="#000" stroke-width="0.4"/>')

    # ============================================================
    # RIGHT PANEL: Draw the arc steps
    # ============================================================
    for i, (name, result, detail) in enumerate(ARC_STEPS):
        y = step_y_start + i * step_h

        # Step box: sharp rectangle, white fill, black border
        lines.append(f'  <rect x="{rx}" y="{y}" width="{step_w}" height="30" fill="#fff" stroke="#000" stroke-width="0.8"/>')

        # Inner divider between name and description
        lines.append(f'  <line x1="{rx+name_col_w}" y1="{y}" x2="{rx+name_col_w}" y2="{y+30}" stroke="#000" stroke-width="0.4"/>')

        # Step name (bold, left cell)
        lines.append(f'  <text x="{rx+name_col_w//2}" y="{y+19}" font-size="11" font-weight="bold" fill="#000" text-anchor="middle">{name}</text>')

        # Result + detail (right cell, single line)
        # Result (left of right cell), detail (right-aligned, italic)
        lines.append(f'  <text x="{rx+name_col_w+10}" y="{y+19}" font-size="11" fill="#000">{result}</text>')
        lines.append(f'  <text x="{rx+step_w-10}" y="{y+19}" font-size="10" fill="#444" font-style="italic" text-anchor="end">{detail}</text>')

    # Fixed bottom item: pinned above metrics line, never pushed by arc steps
    summary_y = H - 60
    lines.append(f'  <text x="{rx + step_w//2}" y="{summary_y}" font-size="11" fill="#000" text-anchor="middle" font-style="italic">Infrastructure built for engineering. Produced mathematics. 3 open frontier questions remain.</text>')

    # ============================================================
    # BOTTOM: Metrics line
    # ============================================================
    m = metrics
    metrics_text = (f'{m["total_files"]} files  |  {m["total_lines"]:,} lines  |  '
                    f'{m["total_theorems"]} theorems  |  {m["sorry_tactics"]} sorry  |  Lean 4 + Mathlib4')
    lines.append(f'  <line x1="20" y1="{H-30}" x2="{W-20}" y2="{H-30}" stroke="#000" stroke-width="0.4"/>')
    lines.append(f'  <text x="{W//2}" y="{H-10}" font-size="12" fill="#000" font-style="italic" text-anchor="middle">{metrics_text}</text>')

    # Footnote
    lines.append(f'  <text x="20" y="{H-10}" font-size="10" fill="#000" font-style="italic">&#x25CA; = Moran-Yehudayoff 2016</text>')

    lines.append('</svg>')
    return '\n'.join(lines)


def main():
    metrics = get_metrics()
    svg = generate_svg(metrics)
    out = os.path.join(REPO_ROOT, 'premise', 'hero.svg')
    with open(out, 'w') as f:
        f.write(svg)
    print(f"Saved: {out}")
    print(f"Metrics: {metrics['total_files']} files, {metrics['total_lines']:,} LOC, "
          f"{metrics['total_theorems']} theorems, {metrics['sorry_tactics']} sorry")


if __name__ == "__main__":
    main()
