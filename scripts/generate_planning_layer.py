#!/usr/bin/env python3
"""
Generate the planning layer figure for Section VIII.

Shows the operational flow:
  World Model (TPG_FLT) --> Planning Layer (bridge_search) --> Closed proofs
  + Private Evidence (Mathlib API, human reasoning) feeds into planning

Style: 20pt base, sharp rectangles, serif, old school academic.
"""

import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from matplotlib.patches import FancyBboxPatch
import os

REPO_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
ASSETS = os.path.join(REPO_ROOT, "assets")
os.makedirs(ASSETS, exist_ok=True)

FS = 22


def box(ax, x, y, w, h, label, fontsize=None, fill='white', edge='black',
        lw=0.8, zorder=3, linestyle='solid'):
    fs = fontsize or FS
    ax.add_patch(FancyBboxPatch((x - w/2, y - h/2), w, h,
                 boxstyle="square,pad=0", facecolor=fill,
                 edgecolor=edge, linewidth=lw, linestyle=linestyle, zorder=zorder))
    ax.text(x, y, label, ha='center', va='center', fontsize=fs,
            fontfamily='serif', fontweight='bold', color='black', zorder=zorder+1)


def main():
    plt.rcParams['font.family'] = 'serif'
    plt.rcParams['font.serif'] = ['Times New Roman', 'DejaVu Serif']

    fig_w, fig_h = 28, 18
    fig, ax = plt.subplots(1, 1, figsize=(fig_w, fig_h))
    ax.set_title("From World Model to Closed Proofs",
                 fontsize=FS * 1.3, fontfamily='serif', fontweight='bold', pad=15)
    ax.set_aspect('equal')
    ax.axis('off')

    # ============================================================
    # Left: World Model (source of truth)
    # ============================================================
    wm_x, wm_y = 4, 9
    wm_w, wm_h = 7, 10

    ax.add_patch(FancyBboxPatch((wm_x - wm_w/2, wm_y - wm_h/2), wm_w, wm_h,
                 boxstyle="square,pad=0", facecolor='#f0f0f0',
                 edgecolor='black', linewidth=1.2, zorder=2))
    ax.text(wm_x, wm_y + wm_h/2 - 0.6, "World Model", ha='center',
            fontsize=FS * 0.9, fontfamily='serif', fontweight='bold', zorder=3)
    ax.text(wm_x, wm_y + wm_h/2 - 1.3, "TPG_FLT", ha='center',
            fontsize=FS * 0.6, fontfamily='serif', fontstyle='italic', zorder=3)

    # World model contents (compact)
    wm_items = [
        "17 Generators",
        "18 Interfaces",
        "7 Failure Rules",
        "6 Typed Pipelines",
        "GapSpec (ignorance)",
    ]
    for i, item in enumerate(wm_items):
        iy = wm_y + 1.5 - i * 1.2
        ax.text(wm_x, iy, item, ha='center', fontsize=FS * 0.5,
                fontfamily='monospace', color='black', zorder=3)

    # ============================================================
    # Center: Planning Layer
    # ============================================================
    pl_x, pl_y = 14, 9
    pl_w, pl_h = 7, 10

    ax.add_patch(FancyBboxPatch((pl_x - pl_w/2, pl_y - pl_h/2), pl_w, pl_h,
                 boxstyle="square,pad=0", facecolor='#e8e8e8',
                 edgecolor='black', linewidth=1.2, zorder=2))
    ax.text(pl_x, pl_y + pl_h/2 - 0.6, "Planning Layer", ha='center',
            fontsize=FS * 0.9, fontfamily='serif', fontweight='bold', zorder=3)
    ax.text(pl_x, pl_y + pl_h/2 - 1.3, "bridge_search", ha='center',
            fontsize=FS * 0.6, fontfamily='monospace', fontstyle='italic', zorder=3)

    # Planning steps
    pl_steps = [
        "1. Classify goal by paradigm",
        "2. Match against interfaces",
        "3. Select generator pipeline",
        "4. Check failure rules",
        "5. Apply or report GapSpec",
    ]
    for i, step in enumerate(pl_steps):
        iy = pl_y + 1.5 - i * 1.2
        ax.text(pl_x, iy, step, ha='center', fontsize=FS * 0.7,
                fontfamily='serif', color='black', zorder=3)

    # ============================================================
    # Top: Private Evidence (feeds into planning)
    # ============================================================
    ev_x, ev_y = 14, 16
    ev_w, ev_h = 10, 2

    ax.add_patch(FancyBboxPatch((ev_x - ev_w/2, ev_y - ev_h/2), ev_w, ev_h,
                 boxstyle="square,pad=0", facecolor='white',
                 edgecolor='#666666', linewidth=0.8, linestyle='dashed', zorder=2))
    ax.text(ev_x, ev_y + 0.3, "Private Evidence", ha='center',
            fontsize=FS * 0.75, fontfamily='serif', fontweight='bold', zorder=3)
    ax.text(ev_x, ev_y - 0.5, "Mathlib API   |   LLM reasoning   |   Proof sketches",
            ha='center', fontsize=FS * 0.45, fontfamily='serif',
            color='#222222', zorder=3)

    # Arrow: evidence down into planning
    ax.annotate("", xy=(pl_x, pl_y + pl_h/2), xytext=(ev_x, ev_y - ev_h/2),
                arrowprops=dict(arrowstyle='->', color='#555555',
                                linewidth=1.0, linestyle='dashed'),
                zorder=1)
    ax.text(ev_x + 3, (ev_y - ev_h/2 + pl_y + pl_h/2) / 2,
            "resolves unknowns", ha='left', fontsize=FS * 0.4,
            fontfamily='serif', fontstyle='italic', color='#333333')

    # ============================================================
    # Arrow: World Model -> Planning Layer
    # ============================================================
    ax.annotate("", xy=(pl_x - pl_w/2, pl_y),
                xytext=(wm_x + wm_w/2, wm_y),
                arrowprops=dict(arrowstyle='->', color='black', linewidth=1.2),
                zorder=1)
    ax.text((wm_x + wm_w/2 + pl_x - pl_w/2) / 2, wm_y + 0.5,
            "typed routing", ha='center', fontsize=FS * 0.45,
            fontfamily='serif', fontstyle='italic')

    # ============================================================
    # Right: Outputs
    # ============================================================
    out_x = 24

    # Success: closed proof
    box(ax, out_x, 12, 6, 2.5,
        "Closed Proof\nHasType verified", FS * 0.6, fill='#e8e8e8')

    # Failure: typed gap
    box(ax, out_x, 6, 6, 2.5,
        "Typed Gap\nGapSpec returned", FS * 0.6, fill='#f8f8f8',
        edge='#888888', linestyle='dashed')

    # Arrows: planning -> outputs
    ax.annotate("", xy=(out_x - 3, 12), xytext=(pl_x + pl_w/2, pl_y + 1),
                arrowprops=dict(arrowstyle='->', color='black', linewidth=1.0),
                zorder=1)
    ax.text(pl_x + pl_w/2 + 1, pl_y + 2, "success", ha='left',
            fontsize=FS * 0.4, fontfamily='serif', fontstyle='italic')

    ax.annotate("", xy=(out_x - 3, 6), xytext=(pl_x + pl_w/2, pl_y - 1),
                arrowprops=dict(arrowstyle='->', color='#888888', linewidth=1.0,
                                linestyle='dashed'),
                zorder=1)
    ax.text(pl_x + pl_w/2 + 1, pl_y - 2, "failure", ha='left',
            fontsize=FS * 0.4, fontfamily='serif', fontstyle='italic',
            color='#444444')

    # Feedback: gap back to world model (theory growth) -- downward swing
    ax.annotate("", xy=(wm_x + wm_w/2, wm_y - wm_h/2),
                xytext=(out_x - 3, 6 - 1.25),
                arrowprops=dict(arrowstyle='->', color='#555555', linewidth=1.0,
                                linestyle='dotted',
                                connectionstyle='arc3,rad=-0.4'),
                zorder=1)
    ax.text(14, 2.0, "gap feeds back: theory grows by filling typed holes",
            ha='center', fontsize=FS * 0.5, fontfamily='serif',
            fontstyle='italic', color='#333333')

    ax.set_xlim(-1, 28)
    ax.set_ylim(1, 18)
    save_fig(fig, os.path.join(ASSETS, 'planning_layer.png'))


def save_fig(fig, path):
    plt.tight_layout()
    plt.savefig(path, dpi=150, bbox_inches='tight',
                facecolor='white', edgecolor='none')
    plt.close()
    print(f"Saved: {path}")


if __name__ == "__main__":
    main()
