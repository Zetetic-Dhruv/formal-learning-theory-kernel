#!/usr/bin/env python3
"""
Generate the discovery hypergraph for Section X.

Two-phase approach:
  1. Use graphviz dot for hierarchical layout (crossing minimization)
  2. Extract node positions, draw with matplotlib (hyperedge hulls as shaded regions)

Style: old school academia (black/white/grey, serif fonts, thin lines).
"""

import subprocess
import json
import os
import re

import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
import matplotlib.patches as mpatches
from matplotlib.patches import FancyBboxPatch
import numpy as np
from scipy.spatial import ConvexHull
from collections import defaultdict

REPO_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
ASSETS = os.path.join(REPO_ROOT, "assets")
os.makedirs(ASSETS, exist_ok=True)

# ============================================================
# Data
# ============================================================

MODULES = {
    "Basic": (0, "structural", "Basic"),
    "Computation": (0, "structural", "Computation"),
    "Data": (0, "structural", "Data"),
    "Learner.Core": (1, "structural", "Learner"),
    "Learner.Props": (1, "structural", "Properties"),
    "Learner.Active": (1, "pac", "Active"),
    "Learner.Bayesian": (1, "bayes", "Bayesian"),
    "Learner.VS": (1, "pac", "VersionSpace"),
    "Learner.Closure": (1, "pac", "Closure"),
    "Learner.Monad": (1, "pac", "Monad"),
    "Criterion.PAC": (2, "pac", "PAC Criterion"),
    "Criterion.Online": (2, "online", "Online Crit."),
    "Criterion.Gold": (2, "gold", "Gold Crit."),
    "Criterion.Ext": (2, "pac", "Extended"),
    "VCDimension": (3, "pac", "VCDim"),
    "Littlestone": (3, "online", "Littlestone"),
    "MindChange": (3, "gold", "MindChange"),
    "Ordinal": (3, "gold", "Ordinal"),
    "Generalization": (4, "pac", "Generalization"),
    "Symmetrization": (4, "pac", "Symmetrization"),
    "Rademacher": (4, "pac", "Rademacher"),
    "Structures": (4, "pac", "Structures"),
    "Measurability": (4, "pac", "Measurability"),
    "GameInfra": (4, "online", "GameInfra"),
    "BorelBridge": (4, "dst", "BorelBridge"),
    "Interpolation": (4, "dst", "Interpolation"),
    "Amalgamation": (4, "dst", "Amalgamation"),
    "Choquet": (5, "dst", "Choquet"),
    "AnalyticMeas": (5, "dst", "AnalyticMeas"),
    "Concentration": (5, "pac", "Concentration"),
    "Exchangeability": (5, "pac", "Exchangeability"),
    "KLDivergence": (5, "bayes", "KLDivergence"),
    "ReaderMonad": (5, "structural", "ReaderMonad"),
    "Thm.PAC": (6, "pac", "PAC Thm"),
    "Thm.Online": (6, "online", "Online Thm"),
    "Thm.Gold": (6, "gold", "Gold Thm"),
    "Thm.Separation": (6, "separation", "Separation"),
    "Thm.BorelAnalytic": (6, "dst", "Borel-Analytic"),
    "Thm.PACBayes": (6, "bayes", "PAC-Bayes"),
    "Thm.Extended": (6, "pac", "Extended Thm"),
    "Process": (7, "structural", "Process"),
    "Bridge": (7, "structural", "Bridge"),
}

EDGES = [
    ("Learner.Core", "Basic"), ("Learner.Props", "Learner.Core"),
    ("Learner.Active", "Learner.Core"), ("Learner.Bayesian", "Learner.Core"),
    ("Learner.VS", "Learner.Core"),
    ("Learner.Closure", "Learner.Core"), ("Learner.Closure", "Generalization"),
    ("Learner.Monad", "Learner.Closure"), ("Learner.Monad", "ReaderMonad"),
    ("Criterion.PAC", "Learner.Core"), ("Criterion.Online", "Learner.Core"),
    ("Criterion.Gold", "Learner.Core"), ("Criterion.Ext", "Criterion.PAC"),
    ("VCDimension", "Criterion.PAC"), ("Littlestone", "Criterion.Online"),
    ("MindChange", "Criterion.Gold"), ("Ordinal", "MindChange"),
    ("Generalization", "VCDimension"), ("Symmetrization", "Generalization"),
    ("Rademacher", "Symmetrization"), ("Structures", "VCDimension"),
    ("Measurability", "Structures"), ("GameInfra", "Littlestone"),
    ("BorelBridge", "Measurability"), ("BorelBridge", "AnalyticMeas"),
    ("Interpolation", "Measurability"),
    ("Amalgamation", "Interpolation"),
    ("Choquet", "Basic"), ("AnalyticMeas", "Choquet"),
    ("Concentration", "Basic"), ("Exchangeability", "Basic"),
    ("KLDivergence", "Basic"),
    ("Thm.PAC", "Generalization"), ("Thm.PAC", "Symmetrization"),
    ("Thm.PAC", "Concentration"),
    ("Thm.Online", "GameInfra"), ("Thm.Online", "Littlestone"),
    ("Thm.Gold", "MindChange"), ("Thm.Gold", "Ordinal"),
    ("Thm.Separation", "Measurability"), ("Thm.Separation", "Concentration"),
    ("Thm.BorelAnalytic", "BorelBridge"),
    ("Thm.PACBayes", "KLDivergence"),
    ("Thm.Extended", "Criterion.Ext"), ("Thm.Extended", "Generalization"),
    ("Process", "Thm.PAC"), ("Bridge", "Thm.PAC"),
]

HYPEREDGES = {
    "PAC chain": {
        "modules": ["VCDimension", "Generalization", "Symmetrization",
                     "Rademacher", "Concentration", "Exchangeability",
                     "Measurability", "Thm.PAC"],
        "color": (0.85, 0.85, 0.85),
    },
    "Borel-analytic\nbridge": {
        "modules": ["Choquet", "AnalyticMeas", "BorelBridge",
                     "Thm.BorelAnalytic", "Measurability"],
        "color": (0.78, 0.78, 0.78),
    },
    "Online\npotential": {
        "modules": ["Littlestone", "GameInfra", "Thm.Online"],
        "color": (0.82, 0.82, 0.82),
    },
    "Gold\nlocking": {
        "modules": ["MindChange", "Ordinal", "Thm.Gold"],
        "color": (0.80, 0.80, 0.80),
    },
    "PAC-Bayes": {
        "modules": ["KLDivergence", "Thm.PACBayes"],
        "color": (0.88, 0.88, 0.88),
    },
    "Composition\nclosure": {
        "modules": ["Interpolation", "Amalgamation", "Learner.Closure",
                     "Learner.Monad", "Learner.VS", "ReaderMonad"],
        "color": (0.90, 0.90, 0.90),
    },
}

PARADIGM_FILL = {
    "structural": "white",
    "pac": "#f0f0f0",
    "online": "#e0e0e0",
    "gold": "#d0d0d0",
    "dst": "#c8c8c8",
    "bayes": "#c0c0c0",
    "separation": "#b8b8b8",
}


def get_dot_layout(modules, edges):
    """Use graphviz dot to compute node positions."""
    # Build DOT source
    lines = ['digraph G {', '  rankdir=TB;', '  nodesep=0.3;', '  ranksep=0.7;',
             '  node [width=0.8, height=0.3];']

    # Same-rank constraints per layer
    layers = defaultdict(list)
    for mod, (layer, _, _) in modules.items():
        layers[layer].append(mod)

    for layer_idx in sorted(layers.keys()):
        mods = layers[layer_idx]
        quoted = '; '.join('"' + m + '"' for m in mods)
        lines.append(f'  {{ rank=same; {quoted}; }}')

    # Nodes
    for mod, (_, _, label) in modules.items():
        safe_id = mod.replace('.', '_')
        lines.append(f'  "{mod}" [label="{label}"];')

    # Edges
    for src, dst in edges:
        lines.append(f'  "{src}" -> "{dst}";')

    lines.append('}')
    dot_src = '\n'.join(lines)

    # Run dot with JSON output
    result = subprocess.run(['dot', '-Tjson'], input=dot_src,
                           capture_output=True, text=True)
    data = json.loads(result.stdout)

    # Extract positions (flip Y so L0 is at top)
    raw_coords = {}
    for obj in data.get('objects', []):
        name = obj.get('name', '')
        if name in modules and 'pos' in obj:
            x, y = obj['pos'].split(',')
            raw_coords[name] = (float(x), float(y))

    if not raw_coords:
        return {}

    max_y = max(c[1] for c in raw_coords.values())
    min_x = min(c[0] for c in raw_coords.values())
    max_x = max(c[0] for c in raw_coords.values())
    x_range = max(max_x - min_x, 1)
    y_range = max(max_y, 1)

    # Compress X to make the graph taller than wide (target ~0.85 aspect ratio)
    x_scale = (y_range * 0.85) / x_range if x_range > 0 else 1.0
    x_scale = min(x_scale, 1.0)  # Don't stretch, only compress

    coords = {}
    for name, (x, y) in raw_coords.items():
        nx = (x - min_x) * x_scale
        ny = max_y - y
        coords[name] = (nx, ny)

    return coords


def draw_hull(ax, coords, module_list, color, label, alpha=0.30):
    """Draw a convex hull around modules."""
    points = np.array([coords[m] for m in module_list if m in coords])
    if len(points) < 2:
        return

    if len(points) == 2:
        cx, cy = points.mean(axis=0)
        dx = abs(points[1][0] - points[0][0]) + 60
        dy = abs(points[1][1] - points[0][1]) + 40
        ellipse = mpatches.Ellipse((cx, cy), dx, dy,
                                    facecolor=color, edgecolor='#555555',
                                    alpha=alpha, linewidth=0.7,
                                    linestyle='--')
        ax.add_patch(ellipse)
        ax.text(cx, cy - dy/2 - 8, label,
                ha='center', va='top', fontsize=7,
                fontfamily='serif', fontstyle='italic', color='#333333')
        return

    # Pad points outward from centroid
    cx, cy = points.mean(axis=0)
    padded = []
    pad = 25
    for px, py in points:
        dx, dy = px - cx, py - cy
        dist = max(np.sqrt(dx**2 + dy**2), 1)
        padded.append((px + pad * dx/dist, py + pad * dy/dist))
    padded = np.array(padded)

    try:
        hull = ConvexHull(padded)
        verts = padded[hull.vertices]
        verts = np.vstack([verts, verts[0]])
        ax.fill(verts[:, 0], verts[:, 1],
                facecolor=color, edgecolor='#555555',
                alpha=alpha, linewidth=0.7, linestyle='--')
        ly = verts[:, 1].min() - 8
        lx = verts[:, 0].mean()
        ax.text(lx, ly, label,
                ha='center', va='top', fontsize=7,
                fontfamily='serif', fontstyle='italic', color='#333333')
    except Exception:
        pass


def draw_graph(modules, edges, hyperedges, coords, output_path, title=None,
               figsize=(14, 24)):
    """Draw the graph using matplotlib with dot-computed positions."""
    plt.rcParams['font.family'] = 'serif'
    plt.rcParams['font.serif'] = ['Times New Roman', 'DejaVu Serif']
    fig, ax = plt.subplots(1, 1, figsize=figsize)

    # Draw hyperedge hulls first (background)
    for he_name, he_data in hyperedges.items():
        mods = [m for m in he_data["modules"] if m in coords]
        if len(mods) >= 2:
            draw_hull(ax, coords, mods, he_data["color"], he_name)

    # Draw edges
    for src, dst in edges:
        if src in coords and dst in coords:
            x0, y0 = coords[src]
            x1, y1 = coords[dst]
            ax.annotate("", xy=(x1, y1), xytext=(x0, y0),
                        arrowprops=dict(arrowstyle='->', color='#444444',
                                        linewidth=0.5,
                                        connectionstyle='arc3,rad=0.02'))

    # Draw nodes
    for mod, (layer, paradigm, label) in modules.items():
        if mod not in coords:
            continue
        x, y = coords[mod]
        fill = PARADIGM_FILL.get(paradigm, 'white')
        bw = max(30, len(label) * 4.5 + 8)
        bh = 14
        bbox = FancyBboxPatch((x - bw/2, y - bh/2), bw, bh,
                               boxstyle="round,pad=2",
                               facecolor=fill, edgecolor='black',
                               linewidth=0.7, zorder=3)
        ax.add_patch(bbox)
        ax.text(x, y, label, ha='center', va='center',
                fontsize=6.5, fontfamily='serif', zorder=4)

    # Layer labels
    if coords:
        layers_y = defaultdict(list)
        for mod, (layer, _, _) in modules.items():
            if mod in coords:
                layers_y[layer].append(coords[mod][1])
        max_x = max(c[0] for c in coords.values()) + 60
        for layer_idx, ys in sorted(layers_y.items()):
            avg_y = np.mean(ys)
            ax.text(max_x, avg_y, f'L{layer_idx}',
                    ha='left', va='center', fontsize=10,
                    fontfamily='serif', fontweight='bold', color='#333333')

    if title:
        ax.set_title(title, fontsize=13, fontfamily='serif',
                     fontweight='bold', pad=15)

    ax.set_aspect('equal')
    ax.axis('off')
    ax.autoscale()
    plt.tight_layout()
    plt.savefig(output_path, dpi=200, bbox_inches='tight',
                facecolor='white', edgecolor='none')
    plt.close()
    print(f"Saved: {output_path}")


def main():
    # Overview
    coords = get_dot_layout(MODULES, EDGES)
    draw_graph(MODULES, EDGES, HYPEREDGES, coords,
               os.path.join(ASSETS, 'hypergraph_overview.png'),
               title='Kernel Structure with Proof Method Regions')

    # PAC detail
    pac = {"Basic", "Learner.Core", "Learner.Props", "Learner.Active",
           "Learner.VS", "Learner.Closure", "Learner.Monad",
           "Criterion.PAC", "Criterion.Ext",
           "VCDimension", "Generalization", "Symmetrization",
           "Rademacher", "Structures", "Measurability",
           "Concentration", "Exchangeability",
           "Thm.PAC", "Thm.Extended", "Thm.Separation"}
    pac_edges = [(s, d) for s, d in EDGES if s in pac and d in pac]
    pac_mods = {k: v for k, v in MODULES.items() if k in pac}
    pac_coords = get_dot_layout(pac_mods, pac_edges)
    draw_graph(pac_mods, pac_edges, {}, pac_coords,
               os.path.join(ASSETS, 'hypergraph_pac.png'),
               title='PAC Paradigm', figsize=(12, 14))

    # Online + Gold
    og = {"Basic", "Learner.Core", "Criterion.Online", "Criterion.Gold",
          "Littlestone", "MindChange", "Ordinal", "GameInfra",
          "Thm.Online", "Thm.Gold"}
    og_edges = [(s, d) for s, d in EDGES if s in og and d in og]
    og_mods = {k: v for k, v in MODULES.items() if k in og}
    og_coords = get_dot_layout(og_mods, og_edges)
    draw_graph(og_mods, og_edges, {}, og_coords,
               os.path.join(ASSETS, 'hypergraph_online_gold.png'),
               title='Online + Gold Paradigms', figsize=(10, 12))

    # DST + Composition
    dst = {"Basic", "Measurability", "Structures", "BorelBridge",
           "Interpolation", "Amalgamation", "Choquet", "AnalyticMeas",
           "Learner.Closure", "Learner.Monad", "Learner.VS",
           "Learner.Core", "ReaderMonad",
           "Thm.BorelAnalytic", "Thm.Separation"}
    dst_edges = [(s, d) for s, d in EDGES if s in dst and d in dst]
    dst_mods = {k: v for k, v in MODULES.items() if k in dst}
    dst_coords = get_dot_layout(dst_mods, dst_edges)
    draw_graph(dst_mods, dst_edges, {}, dst_coords,
               os.path.join(ASSETS, 'hypergraph_dst.png'),
               title='DST + Composition Closure', figsize=(12, 14))


if __name__ == "__main__":
    main()
