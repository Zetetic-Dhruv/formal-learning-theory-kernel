#!/usr/bin/env python3
"""
Generate the operad pipelines diagram for Section VIII.

Data auto-read from world_model/dag/generate_dag.py (GENERATORS, INTERFACES, PIPELINES).
Layout: horizontal pipelines stacked vertically, interfaces as boxes, generators as labeled arrows.
NT1 cross-paradigm impossibility marked with red X.

Style matches hypergraph: serif fonts, 18pt node text, computed paradigm greys.
"""

import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from matplotlib.patches import FancyBboxPatch, FancyArrowPatch
import numpy as np
import os
import sys

REPO_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
ASSETS = os.path.join(REPO_ROOT, "assets")
os.makedirs(ASSETS, exist_ok=True)

# Import data from generate_dag.py
sys.path.insert(0, os.path.join(REPO_ROOT, "world_model", "dag"))
from generate_dag import GENERATORS, INTERFACES, PIPELINES

# Paradigm grey fills (matching hypergraph)
PARADIGM_FILL = {
    "pac": "#e8e8e8",
    "online": "#d0d0d0",
    "gold": "#c0c0c0",
    "dst": "#b8b8b8",
    "bayes": "#a8a8a8",
    "separation": "#909090",
    "structural": "white",
}

PARADIGM_LABELS = {
    "PAC_characterization": ("PAC", "pac"),
    "DST_bridge": ("DST", "dst"),
    "Online_characterization": ("Online", "online"),
    "Gold_impossibility": ("Gold", "gold"),
    "Separation": ("Separation", "separation"),
    "PAC_Bayes": ("Bayesian", "bayes"),
}

# Pipeline order (top to bottom)
PIPELINE_ORDER = [
    "PAC_characterization",
    "DST_bridge",
    "Online_characterization",
    "Gold_impossibility",
    "Separation",
    "PAC_Bayes",
]

# NT1: the ill-typed cross-paradigm composition
NT1_FROM = "OnlineLearnable"  # output of TreePotential (Online)
NT1_TO = "HasUC"              # input of UCToPAC (PAC)


def resolve_pipeline(pipe_name):
    """Resolve a pipeline into a sequence of (interface, generator, interface, ...) nodes."""
    steps = PIPELINES[pipe_name]
    chain = []
    for i, gen_name in enumerate(steps):
        gen = GENERATORS[gen_name]
        level, inp, outs, paradigm = gen
        if i == 0:
            chain.append(("iface", inp))
        chain.append(("gen", gen_name))
        for out in outs:
            chain.append(("iface", out))
    return chain


def main():
    plt.rcParams['font.family'] = 'serif'
    plt.rcParams['font.serif'] = ['Times New Roman', 'DejaVu Serif']

    n_pipes = len(PIPELINE_ORDER)
    row_h = 7.0
    fig_h = n_pipes * row_h + 8
    fig_w = 52

    # Font sizing: higher ratio than hypergraph since this diagram is sparser
    FONT_RATIO = 0.55
    fs_node = fig_h * FONT_RATIO
    fs_gen = fig_h * FONT_RATIO * 0.8
    fs_title = fig_h * FONT_RATIO * 1.2
    fs_label = fig_h * FONT_RATIO

    fig, ax = plt.subplots(1, 1, figsize=(fig_w, fig_h))

    ax.set_title("Typed Proof Pipelines", fontsize=fs_title,
                 fontfamily='serif', fontweight='bold', pad=20)

    iface_positions = {}

    x_start = 7.0
    iface_w = 5.5
    iface_h = 2.0
    gen_gap = 6.0
    label_col_w = 6.0

    for row_idx, pipe_name in enumerate(PIPELINE_ORDER):
        chain = resolve_pipeline(pipe_name)
        label, paradigm = PARADIGM_LABELS[pipe_name]
        fill = PARADIGM_FILL.get(paradigm, 'white')

        y_center = (n_pipes - row_idx - 0.5) * row_h

        # Paradigm label on left
        ax.text(label_col_w / 2, y_center, label,
                ha='center', va='center', fontsize=fs_label,
                fontfamily='serif', fontweight='bold', color='black')

        # Draw chain
        x = x_start
        prev_iface_x = None

        # Group consecutive iface nodes (for multi-output generators)
        i = 0
        while i < len(chain):
            node_type, name = chain[i]

            if node_type == "iface":
                # Collect consecutive iface entries (multi-output case)
                iface_group = [name]
                while i + 1 < len(chain) and chain[i + 1][0] == "iface":
                    i += 1
                    iface_group.append(chain[i][1])

                if len(iface_group) == 1:
                    # Single interface box
                    bw = max(iface_w, len(name) * 0.32 + 0.8)
                    bx = x
                    by = y_center - iface_h / 2
                    ax.add_patch(FancyBboxPatch(
                        (bx, by), bw, iface_h,
                        boxstyle="square,pad=0",
                        facecolor=fill, edgecolor='black',
                        linewidth=0.8, zorder=3))
                    ax.text(bx + bw/2, y_center, name,
                            ha='center', va='center', fontsize=fs_node,
                            fontfamily='serif', fontweight='bold',
                            color='black', zorder=4)
                    iface_positions[name] = (bx + bw/2, y_center)
                    prev_iface_x = bx + bw
                    x = bx + bw + gen_gap
                else:
                    # Multiple outputs side by side with separator
                    total_x = x
                    for j, iname in enumerate(iface_group):
                        bw = max(iface_w, len(iname) * 0.32 + 0.8)
                        bx = total_x
                        by = y_center - iface_h / 2
                        ax.add_patch(FancyBboxPatch(
                            (bx, by), bw, iface_h,
                            boxstyle="square,pad=0",
                            facecolor=fill, edgecolor='black',
                            linewidth=0.8, zorder=3))
                        ax.text(bx + bw/2, y_center, iname,
                                ha='center', va='center', fontsize=fs_node,
                                fontfamily='serif', fontweight='bold',
                                color='black', zorder=4)
                        iface_positions[iname] = (bx + bw/2, y_center)
                        # Vertical separator between outputs
                        if j < len(iface_group) - 1:
                            sep_x = bx + bw + 0.3
                            ax.plot([sep_x, sep_x],
                                    [y_center - iface_h/2 - 0.3, y_center + iface_h/2 + 0.3],
                                    color='black', linewidth=0.6, zorder=3)
                        total_x = bx + bw + 0.6
                    prev_iface_x = total_x
                    x = total_x + gen_gap

            elif node_type == "gen":
                # Generator arrow between previous interface and next
                arrow_x_start = prev_iface_x + 0.3
                arrow_x_end = x - 0.3

                ax.annotate("", xy=(arrow_x_end, y_center),
                            xytext=(arrow_x_start, y_center),
                            arrowprops=dict(arrowstyle='->', color='black',
                                            linewidth=1.2),
                            zorder=2)
                mid_x = (arrow_x_start + arrow_x_end) / 2
                ax.text(mid_x, y_center + iface_h/2 + 0.4, name,
                        ha='center', va='bottom', fontsize=fs_gen,
                        fontfamily='serif', fontstyle='italic',
                        color='#333333', zorder=4)

            i += 1

    # NT1: Cross-paradigm impossibility (red dotted arc from center of nodes)
    if NT1_FROM in iface_positions and NT1_TO in iface_positions:
        x_from, y_from = iface_positions[NT1_FROM]
        x_to, y_to = iface_positions[NT1_TO]
        print(f"  NT1: {NT1_FROM}=({x_from:.1f},{y_from:.1f}) -> {NT1_TO}=({x_to:.1f},{y_to:.1f})")

        # Arc from center to center, swinging left
        ax.annotate("",
                    xy=(x_to, y_to),
                    xytext=(x_from, y_from),
                    arrowprops=dict(arrowstyle='->', color='red',
                                    linewidth=1.5, linestyle='dotted',
                                    connectionstyle='arc3,rad=-0.3'),
                    zorder=1)
    else:
        missing = []
        if NT1_FROM not in iface_positions:
            missing.append(NT1_FROM)
        if NT1_TO not in iface_positions:
            missing.append(NT1_TO)
        print(f"  NT1 WARNING: missing interfaces: {missing}")

    # Separator line between label column and pipelines
    ax.plot([label_col_w + 0.5, label_col_w + 0.5],
            [0, n_pipes * row_h],
            color='#aaaaaa', linewidth=0.5, linestyle=':', zorder=0)

    ax.set_xlim(-12, fig_w - 2)
    ax.set_ylim(-1.5, n_pipes * row_h + 1.5)
    ax.set_aspect('equal')
    ax.axis('off')
    plt.tight_layout()
    plt.savefig(os.path.join(ASSETS, 'operad_pipelines.png'),
                dpi=150, bbox_inches='tight',
                facecolor='white', edgecolor='none')
    plt.close()
    print(f"Saved: {os.path.join(ASSETS, 'operad_pipelines.png')}")


if __name__ == "__main__":
    main()
