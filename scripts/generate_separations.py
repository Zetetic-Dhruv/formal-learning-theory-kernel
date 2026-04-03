#!/usr/bin/env python3
"""
Generate the three separation diagrams for Section III.

1. threshold_separation.png -- PAC does not imply Online
2. gold_separation.png -- Gold does not imply PAC
3. borel_analytic_separation.png -- WellBehavedVC vs KrappWirth

Style: old school academic, sharp rectangles, serif fonts, 20pt base.
"""

import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from matplotlib.patches import FancyBboxPatch
import numpy as np
import os

REPO_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
ASSETS = os.path.join(REPO_ROOT, "assets")
os.makedirs(ASSETS, exist_ok=True)

FS = 20  # base font size in points
DARK_RED = '#8B0000'


def setup_fig(fig_w, fig_h, title):
    plt.rcParams['font.family'] = 'serif'
    plt.rcParams['font.serif'] = ['Times New Roman', 'DejaVu Serif']
    fig, ax = plt.subplots(1, 1, figsize=(fig_w, fig_h))
    ax.set_title(title, fontsize=FS * 1.3, fontfamily='serif',
                 fontweight='bold', pad=15)
    ax.set_aspect('equal')
    ax.axis('off')
    return fig, ax


def save_fig(fig, path):
    plt.tight_layout()
    plt.savefig(path, dpi=150, bbox_inches='tight',
                facecolor='white', edgecolor='none')
    plt.close()
    print(f"Saved: {path}")


def box(ax, x, y, w, h, label, fontsize=None, fill='white', edge='black', lw=0.8, zorder=3):
    fs = fontsize or FS
    ax.add_patch(FancyBboxPatch((x - w/2, y - h/2), w, h,
                 boxstyle="square,pad=0", facecolor=fill,
                 edgecolor=edge, linewidth=lw, zorder=zorder))
    ax.text(x, y, label, ha='center', va='center', fontsize=fs,
            fontfamily='serif', fontweight='bold', color='black', zorder=zorder+1)


def arrow(ax, x1, y1, x2, y2, label=None, fontsize=None, color='black'):
    fs = fontsize or FS * 0.7
    ax.annotate("", xy=(x2, y2), xytext=(x1, y1),
                arrowprops=dict(arrowstyle='->', color=color, linewidth=1.0),
                zorder=1)
    if label:
        mx, my = (x1+x2)/2, (y1+y2)/2
        ax.text(mx, my + 0.8, label, ha='center', va='bottom', fontsize=fs,
                fontfamily='serif', fontstyle='italic', color='#333333')


# ============================================================
# 1. Threshold separation: PAC does not imply Online
# ============================================================

def gen_threshold():
    fig_w, fig_h = 24, 14
    fig, ax = setup_fig(fig_w, fig_h, "PAC does not imply Online: Threshold class on N")

    # Left panel: VCDim = 1
    lx, ly = 2, 7
    line_len = 8

    ax.text(lx + line_len/2, ly + 5, "VCDim(C) = 1", ha='center', fontsize=FS,
            fontfamily='serif', fontweight='bold')
    ax.text(lx + line_len/2, ly + 3.8,
            r"C = { x $\mapsto$ (x $\leq$ n)  |  n : N }",
            ha='center', fontsize=FS*0.75, fontfamily='serif')

    # Number line
    ax.plot([lx, lx + line_len], [ly, ly], color='black', linewidth=1.2)
    for i in range(6):
        xi = lx + i * line_len / 5
        ax.plot([xi, xi], [ly - 0.2, ly + 0.2], color='black', linewidth=0.8)
        ax.text(xi, ly - 0.6, str(i), ha='center', fontsize=FS*0.6,
                fontfamily='serif')

    # Threshold at n=3
    thresh_x = lx + 3 * line_len / 5
    ax.fill_between([lx, thresh_x], [ly + 0.3, ly + 0.3], [ly + 1.8, ly + 1.8],
                    alpha=0.12, color='black')
    ax.text((lx + thresh_x)/2, ly + 1.0, "true", ha='center', fontsize=FS*0.6,
            fontfamily='serif', fontstyle='italic')
    ax.text((thresh_x + lx + line_len)/2, ly + 1.0, "false", ha='center',
            fontsize=FS*0.6, fontfamily='serif', fontstyle='italic')
    ax.plot([thresh_x, thresh_x], [ly, ly + 1.8], color='black',
            linewidth=1.5, linestyle='--')
    ax.text(thresh_x + 0.2, ly + 2.1, "n=3", ha='left', fontsize=FS*0.6,
            fontfamily='serif')

    # Singleton shattered
    k_x = lx + 2 * line_len / 5
    ax.plot(k_x, ly - 1.5, 'ko', markersize=5)
    ax.text(k_x + 0.3, ly - 1.5,
            r"{k}: shattered by thresholds k$-$1, k",
            ha='left', fontsize=FS*0.55, fontfamily='serif')

    # Pair not shattered
    a_x = lx + 1 * line_len / 5
    b_x = lx + 4 * line_len / 5
    ax.plot([a_x, b_x], [ly - 3, ly - 3], 'k-', linewidth=0.5)
    ax.plot(a_x, ly - 3, 'ko', markersize=5)
    ax.plot(b_x, ly - 3, 'ko', markersize=5)
    ax.text(a_x - 0.2, ly - 3, "a", ha='right', fontsize=FS*0.6, fontfamily='serif')
    ax.text(b_x + 0.2, ly - 3, "b", ha='left', fontsize=FS*0.6, fontfamily='serif')
    ax.text((a_x+b_x)/2, ly - 4,
            "a < b: labeling (false, true)\nrequires non-monotone function",
            ha='center', fontsize=FS*0.5, fontfamily='serif', fontstyle='italic')

    # Divider
    ax.plot([12, 12], [1, 13], color='#aaaaaa', linewidth=0.5, linestyle=':')

    # Right panel: LittlestoneDim = infinity
    rx, ry = 18, 10
    ax.text(rx, ry + 2.5, "LittlestoneDim(C) = infinity", ha='center',
            fontsize=FS, fontfamily='serif', fontweight='bold')
    ax.text(rx, ry + 1.3, "Adversary: binary search", ha='center',
            fontsize=FS*0.65, fontfamily='serif', fontstyle='italic')

    # Binary search tree
    tree_nodes = [(rx, ry, "mid")]
    levels = 3
    for d in range(1, levels + 1):
        spread = 3.5 / (1.4 ** d)
        new_nodes = []
        for px, py, _ in tree_nodes[-(2**(d-1)):]:
            for sign, lbl in [(-1, "1 mistake"), (1, "1 mistake")]:
                nx = px + sign * spread
                ny = py - 2.5
                new_nodes.append((nx, ny, ""))
                ax.plot([px, nx], [py - 0.3, ny + 0.3], color='black', linewidth=0.7)
                rot = 15 * sign
                ax.text((px+nx)/2 + sign*0.3, (py+ny)/2, lbl,
                        fontsize=FS*0.35, fontfamily='serif', fontstyle='italic',
                        color='#555555', rotation=rot, ha='center')
        tree_nodes.extend(new_nodes)

    for nx, ny, label in tree_nodes:
        ax.plot(nx, ny, 'ko', markersize=4, zorder=3)
        if label:
            ax.text(nx, ny + 0.5, label, ha='center', fontsize=FS*0.5,
                    fontfamily='serif')

    ax.text(rx, ry - levels * 2.5 - 1, "... (arbitrary depth)", ha='center',
            fontsize=FS*0.6, fontfamily='serif')

    ax.set_xlim(-1, 24)
    ax.set_ylim(-1, 14)
    save_fig(fig, os.path.join(ASSETS, 'threshold_separation.png'))


# ============================================================
# 2. Gold separation: Gold does not imply PAC
# ============================================================

def gen_gold():
    fig_w, fig_h = 24, 12
    fig, ax = setup_fig(fig_w, fig_h, "Gold does not imply PAC: Finite-subset indicators on N")

    # Left panel
    ax.text(6, 10.5, "EX-learnable: converges", ha='center', fontsize=FS,
            fontfamily='serif', fontweight='bold')
    ax.text(6, 9.3, r"C = { x $\mapsto$ (x $\in$ S) | S : Finset N }",
            ha='center', fontsize=FS*0.7, fontfamily='serif')

    ty = 7
    steps = [
        ("t=1", "sees 2", "{2}"),
        ("t=2", "sees 5", "{2,5}"),
        ("t=3", "sees 7", "{2,5,7}"),
    ]
    for i, (t, obs, conj) in enumerate(steps):
        x = 2 + i * 3.2
        ax.text(x, ty + 1.2, t, ha='center', fontsize=FS*0.6,
                fontfamily='serif', fontweight='bold')
        ax.text(x, ty + 0.5, obs, ha='center', fontsize=FS*0.5,
                fontfamily='serif', fontstyle='italic')
        box(ax, x, ty - 0.6, 2.6, 0.9, conj, FS*0.55)
        if i < len(steps) - 1:
            arrow(ax, x + 1.3, ty - 0.6, x + 1.9, ty - 0.6)

    ax.text(9.8, ty - 0.6, "= target. Stabilizes.", ha='left', fontsize=FS*0.6,
            fontfamily='serif', fontweight='bold')

    ax.text(6, ty - 3, "After finitely many observations,\nthe learner stabilizes.",
            ha='center', fontsize=FS*0.5, fontfamily='serif', fontstyle='italic')

    # Divider
    ax.plot([12, 12], [1, 11], color='#aaaaaa', linewidth=0.5, linestyle=':')

    # Right panel
    rx = 18
    ax.text(rx, 10.5, "VCDim(C) = infinity", ha='center', fontsize=FS,
            fontfamily='serif', fontweight='bold')
    ax.text(rx, 9.3, "Every finite set is shattered", ha='center',
            fontsize=FS*0.65, fontfamily='serif')

    labelings = [
        ("{a,b}", True, True),
        ("{a}", True, False),
        ("{b}", False, True),
        ("empty", False, False),
    ]
    for i, (ind, a_val, b_val) in enumerate(labelings):
        y = 7.5 - i * 1.5
        ax.plot(rx - 2, y, 'ko' if a_val else 'o', markersize=6,
                markerfacecolor='black' if a_val else 'white',
                markeredgecolor='black', zorder=3)
        ax.plot(rx, y, 'ko' if b_val else 'o', markersize=6,
                markerfacecolor='black' if b_val else 'white',
                markeredgecolor='black', zorder=3)
        ax.text(rx - 2, y - 0.5, "a", ha='center', fontsize=FS*0.4,
                fontfamily='serif')
        ax.text(rx, y - 0.5, "b", ha='center', fontsize=FS*0.4,
                fontfamily='serif')
        ax.text(rx + 1.5, y, f"realized by 1_{{{ind}}}",
                ha='left', fontsize=FS*0.5, fontfamily='serif')

    ax.text(rx, 1.5, r"All $2^k$ labelings of any k-set realized",
            ha='center', fontsize=FS*0.55, fontfamily='serif', fontstyle='italic')

    ax.set_xlim(-1, 24)
    ax.set_ylim(0, 12)
    save_fig(fig, os.path.join(ASSETS, 'gold_separation.png'))


# ============================================================
# 3. Borel-analytic separation
# ============================================================

def gen_borel_analytic():
    fig_w, fig_h = 28, 20
    fig, ax = setup_fig(fig_w, fig_h,
        "Borel-analytic separation: NullMeasurableSet is strictly weaker than MeasurableSet")

    # Top panel: Witness class
    ax.text(14, 18.5, "Witness: singletonClassOn(A)", ha='center',
            fontsize=FS, fontfamily='serif', fontweight='bold')
    ax.text(14, 18.2, r"A $\subseteq$ R, analytic, non-Borel (Suslin 1917)",
            ha='center', fontsize=FS*0.65, fontfamily='serif', fontstyle='italic')

    # Real line
    rl_y = 16
    ax.plot([2, 26], [rl_y, rl_y], color='black', linewidth=1.2)
    ax.text(26.5, rl_y, "R", fontsize=FS*0.7, fontfamily='serif', fontstyle='italic')

    ax.fill_between([6, 22], [rl_y - 0.1, rl_y - 0.1],
                    [rl_y + 0.1, rl_y + 0.1], alpha=0.3, color='gray')
    ax.text(14, rl_y + 0.5, "A", ha='center', fontsize=FS*0.7,
            fontfamily='serif', fontweight='bold')

    # zeroConcept
    ax.plot([2, 26], [rl_y - 1.5, rl_y - 1.5], color='black', linewidth=0.5)
    ax.text(1.5, rl_y - 1.5, r"zeroConcept: x $\mapsto$ false",
            ha='right', fontsize=FS*0.4, fontfamily='serif', fontstyle='italic')

    # Spikes
    for xp, ai in [(8, r"$a_1$"), (14, r"$a_2$"), (20, r"$a_3$")]:
        ax.plot([xp, xp], [rl_y, rl_y + 1.5], color='black', linewidth=1.0)
        ax.plot(xp, rl_y + 1.5, 'ko', markersize=4)
        ax.text(xp, rl_y + 1.8, f"singletonConcept({ai})",
                ha='center', fontsize=FS*0.35, fontfamily='serif')

    # Divider
    ax.plot([2, 26], [rl_y - 2.5, rl_y - 2.5], color='#aaaaaa',
            linewidth=0.4, linestyle=':')

    # Middle panel: Proof chains
    # Positive path
    pos_y = 11
    ax.text(14, pos_y + 2.2, "Positive path", ha='center',
            fontsize=FS*0.8, fontfamily='serif', fontweight='bold')

    box(ax, 4, pos_y, 5.5, 1.8,
        r"Bad event" + "\n" + r"$\exists$ h $\in$ C, gap $\geq$ $\epsilon$/2",
        FS*0.5)
    box(ax, 14, pos_y, 5.5, 1.8,
        r"Analytic ($\Sigma^1_1$)" + "\n" + "Suslin projection",
        FS*0.5)
    box(ax, 24, pos_y, 5.5, 1.8,
        "NullMeasurableSet" + "\n" + "Choquet (Kechris 30.13)",
        FS*0.5)

    arrow(ax, 6.8, pos_y, 11.2, pos_y, "project", FS*0.5)
    arrow(ax, 16.8, pos_y, 21.2, pos_y, "capacitability", FS*0.5)

    # Negative path
    neg_y = 7
    ax.text(14, neg_y + 2.2, "Negative path", ha='center',
            fontsize=FS*0.8, fontfamily='serif', fontweight='bold', color=DARK_RED)

    box(ax, 4, neg_y, 5.5, 1.8,
        "Assume\nMeasurableSet (Borel)", FS*0.5, edge='#666666')
    box(ax, 14, neg_y, 5.5, 1.8,
        r"Preimage x $\mapsto$ ($a_0$, x)" + "\n" + "gives A is Borel",
        FS*0.5, edge='#666666')
    box(ax, 24, neg_y, 5.5, 1.8,
        "A is non-Borel\nby construction",
        FS*0.5, fill='#fde8e8', edge=DARK_RED)

    arrow(ax, 6.8, neg_y, 11.2, neg_y, "preimage", FS*0.5, color='#666666')
    arrow(ax, 16.8, neg_y, 21.2, neg_y, "contradiction", FS*0.5, color=DARK_RED)

    # Divider
    ax.plot([2, 26], [neg_y - 2, neg_y - 2], color='#aaaaaa',
            linewidth=0.4, linestyle=':')

    # Bottom panel: Result
    sep_y = 3
    ax.text(14, sep_y + 2, "Result", ha='center',
            fontsize=FS*0.8, fontfamily='serif', fontweight='bold')

    box(ax, 7, sep_y, 8, 1.8,
        "WellBehavedVC: HOLDS\n(NullMeasurableSet)", FS*0.55, fill='#e8e8e8')

    ax.text(14, sep_y, "strict gap", ha='center', fontsize=FS*0.65,
            fontfamily='serif', fontweight='bold')

    box(ax, 21, sep_y, 8, 1.8,
        "KrappWirth: FAILS\n(not MeasurableSet)", FS*0.55,
        fill='#fde8e8', edge=DARK_RED)

    ax.set_xlim(-1, 28)
    ax.set_ylim(0, 20)
    save_fig(fig, os.path.join(ASSETS, 'borel_analytic_separation.png'))


def main():
    gen_threshold()
    gen_gold()
    gen_borel_analytic()


if __name__ == "__main__":
    main()
