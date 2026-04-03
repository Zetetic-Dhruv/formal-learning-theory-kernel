#!/usr/bin/env python3
"""
Generate the premise blueprint pseudocode figure for Section IV.

Renders the two-phase premise design pipeline as structured pseudocode
with diagnostic gates as conditional branches and Phase 2 as a loop.
Data derived from assets/premise_blueprint.yaml.

Style matches world model figure: monospaced, grey section bands.
"""

import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
import os

REPO_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
ASSETS = os.path.join(REPO_ROOT, "assets")
os.makedirs(ASSETS, exist_ok=True)

# 2x2 grid: top-left, top-right, bottom-left, bottom-right
# Each quadrant is a list of (indent, text, style) lines

QUAD_TL = [  # Phase 1: Steps 1-4
    (0, "-- Phase 1: Premise Design (human)", "section"),
    (0, "", "blank"),
    (0, "step 1.  Identify paradigms + obstruction tags", "keyword"),
    (1, "-- List subfields. For each pair: shared proofs?", "comment"),
    (1, "-- Output: paradigm list + obstruction matrix", "comment"),
    (0, "", "blank"),
    (0, "step 2.  Identify domain crossings per paradigm", "keyword"),
    (1, "-- PAC: combinatorics x measure theory", "comment"),
    (1, "-- Online: combinatorics x game theory", "comment"),
    (1, "-- Gold: computability x topology", "comment"),
    (0, "", "blank"),
    (0, "step 3.  Assign dependency layers (L0-L7)", "keyword"),
    (1, "L0: computation   L1: base types", "code"),
    (1, "L2: data          L3: agents", "code"),
    (1, "L4: criteria      L5: complexity", "code"),
    (1, "L6: theorems      L7: processes", "code"),
    (0, "", "blank"),
    (0, "step 4.  Write definitions with sorry", "keyword"),
    (1, "-- The type signature IS the premise.", "comment"),
    (1, "-- lake build must succeed.", "comment"),
    (0, "", "blank"),
    (0, "=> Hand to AI for proof search.", "keyword"),
]

QUAD_TR = [  # Phase 1: Diagnostic gates
    (0, "-- Diagnostic Gates (fail => return to step 4)", "section"),
    (0, "", "blank"),
    (0, "gate 5.  Failure taxonomy", "keyword"),
    (1, "unintended witnesses   => false theorem", "code"),
    (1, "  fix: restrict quantifier scope", "code"),
    (1, "existential leak       => vacuous theorem", "code"),
    (1, "  fix: fixed construction", "code"),
    (1, "missing properties     => displaced proof", "code"),
    (1, "  fix: encode in definition", "code"),
    (0, "", "blank"),
    (0, "gate 6.  Domain boundary", "keyword"),
    (1, "false for some card.   => cardinality leak", "code"),
    (1, "  fix: [Infinite X] or [Fintype X]", "code"),
    (0, "", "blank"),
    (0, "gate 7.  Measurability", "keyword"),
    (1, "uncountable + integral => measurability gap", "code"),
    (1, "  fix: NullMeasurableSet + typeclasses", "code"),
    (0, "", "blank"),
    (0, "step 8.  Estimate infrastructure ratio", "keyword"),
    (1, "1 domain:  < 30%", "code"),
    (1, "2 domains: 40-60%", "code"),
    (1, "3 domains: > 60%", "code"),
]

QUAD_BL = [  # Phase 2: Discovery loop
    (0, "-- Phase 2: Refactoring for Discovery (human)", "section"),
    (0, "", "blank"),
    (0, "repeat", "keyword"),
    (1, "A.  Identify inlined infrastructure", "keyword"),
    (2, "-- >3 files => typeclass", "comment"),
    (2, "-- wrong domain => separate module", "comment"),
    (0, "", "blank"),
    (1, "B.  Extract to modules", "keyword"),
    (2, "-- field-independent => PureMath/", "comment"),
    (2, "-- field-specific => Complexity/", "comment"),
    (2, "-- must compile independently", "comment"),
    (0, "", "blank"),
    (1, "C.  Introduce typeclasses", "keyword"),
    (2, "-- each is a generality hypothesis", "comment"),
    (2, "-- unexpected instances => discovery", "comment"),
    (0, "", "blank"),
    (1, "D.  Test generality", "keyword"),
    (2, "-- new instances from other paradigm?", "comment"),
    (2, "-- composition weakens? => theorem", "comment"),
    (2, "-- new domain connection? => new math", "comment"),
    (0, "", "blank"),
    (0, "until no productive extractions remain", "keyword"),
]

QUAD_BR = [  # Discovery signals
    (0, "-- Discovery Signals", "section"),
    (0, "", "blank"),
    (0, "signal:", "keyword"),
    (1, "same hypothesis in >3 files", "code"),
    (1, "  => extract typeclass", "code"),
    (0, "", "blank"),
    (0, "signal:", "keyword"),
    (1, "typeclass has unexpected instances", "code"),
    (1, "  => prove them (discovery)", "code"),
    (0, "", "blank"),
    (0, "signal:", "keyword"),
    (1, "composed objects less well-behaved", "code"),
    (1, "  => structural theorem (publish)", "code"),
    (0, "", "blank"),
    (0, "signal:", "keyword"),
    (1, "module compiles independently", "code"),
    (1, "  => pure math (Mathlib?)", "code"),
    (0, "", "blank"),
    (0, "-- Each extraction is a hypothesis.", "comment"),
    (0, "-- Each typeclass is a hypothesis.", "comment"),
    (0, "-- Testing them is how formalization", "comment"),
    (0, "-- becomes discovery.", "comment"),
]

STYLES = {
    "section":  ("#000000", "#e8e8e8", True),
    "keyword":  ("#000000", None, True),
    "code":     ("#333333", None, False),
    "comment":  ("#666666", None, False),
    "blank":    ("#000000", None, False),
}


def draw_quadrant(ax, lines, x_base, y_top, line_h=0.45, indent_w=1.2):
    """Draw a list of pseudocode lines starting at (x_base, y_top)."""
    for i, (indent, text, style) in enumerate(lines):
        y = y_top - i * line_h
        x = x_base + indent * indent_w
        color, bg, bold = STYLES[style]

        if style == "blank":
            continue

        if bg:
            # Only shade within the quadrant's x range
            ax.axhspan(y - line_h * 0.4, y + line_h * 0.4,
                       color=bg, zorder=0)

        weight = 'bold' if bold else 'normal'
        fs = 11 if style == "comment" else 12

        ax.text(x, y, text, fontsize=fs, fontfamily='monospace',
                fontweight=weight, color=color, va='center', zorder=2)


def main():
    plt.rcParams['font.family'] = 'monospace'
    plt.rcParams['font.monospace'] = ['DejaVu Sans Mono', 'Courier New']

    line_h = 0.45
    col_w = 22  # width of each column in data units
    gap = 2     # gap between columns

    # Compute heights
    max_top = max(len(QUAD_TL), len(QUAD_TR))
    max_bot = max(len(QUAD_BL), len(QUAD_BR))
    row_gap = 2  # gap between top and bottom rows

    total_h = (max_top + max_bot) * line_h + row_gap + 4
    total_w = col_w * 2 + gap

    fig_w = total_w * 0.55  # scale to inches
    fig_h = total_h * 0.55

    fig, ax = plt.subplots(1, 1, figsize=(fig_w, fig_h))
    ax.set_title("Premise Design Blueprint",
                 fontsize=18, fontfamily='serif', fontweight='bold', pad=15)
    ax.axis('off')

    # Top-left: Phase 1 steps
    tl_y = total_h - 1
    draw_quadrant(ax, QUAD_TL, 0, tl_y, line_h)

    # Top-right: Diagnostic gates
    draw_quadrant(ax, QUAD_TR, col_w + gap, tl_y, line_h)

    # Divider between top and bottom
    mid_y = tl_y - max_top * line_h - row_gap / 2
    ax.plot([0, total_w], [mid_y, mid_y], color='#aaaaaa',
            linewidth=0.5, linestyle=':', zorder=0)

    # Bottom-left: Phase 2 loop
    bl_y = mid_y - row_gap / 2
    draw_quadrant(ax, QUAD_BL, 0, bl_y, line_h)

    # Bottom-right: Discovery signals
    draw_quadrant(ax, QUAD_BR, col_w + gap, bl_y, line_h)

    # Vertical divider between columns
    ax.plot([col_w + gap/2, col_w + gap/2], [0, total_h],
            color='#aaaaaa', linewidth=0.5, linestyle=':', zorder=0)

    ax.set_xlim(-1, total_w + 1)
    ax.set_ylim(-1, total_h + 1)
    plt.tight_layout()
    plt.savefig(os.path.join(ASSETS, 'premise_blueprint_flow.png'),
                dpi=150, bbox_inches='tight',
                facecolor='white', edgecolor='none')
    plt.close()
    print(f"Saved: {os.path.join(ASSETS, 'premise_blueprint_flow.png')}")


if __name__ == "__main__":
    main()
