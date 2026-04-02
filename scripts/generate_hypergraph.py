#!/usr/bin/env python3
"""
Generate the discovery hypergraph for Section X.

Two-scale composite:
  1. Overview: module-level nodes with metaprogram hyperedges (colored hulls)
  2. Detail panels: per-paradigm theorem-cluster views

Layout algorithm: Sugiyama framework (Sugiyama, Tagawa, Toda 1981)
  - Layer assignment: manual (L0-L7 from premise architecture)
  - Crossing reduction: barycenter heuristic (best practical performance,
    per Kocurova's thesis Section 5, referencing [121])
  - Coordinate assignment: integer grid with uniform spacing

Style: old school academia (black/white, Times New Roman, thin lines,
       serif labels, no color except paradigm-coded hull shading in grey tones)

Usage:
    python3 generate_hypergraph.py
    # Produces: hypergraph_overview.png, hypergraph_pac.png,
    #           hypergraph_online_gold.png, hypergraph_dst.png
"""

import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
import matplotlib.patches as mpatches
from matplotlib.patches import FancyBboxPatch
import numpy as np
from collections import defaultdict
from scipy.spatial import ConvexHull

# ============================================================
# Data: Module-level nodes with layer assignments
# ============================================================

# Layer assignment from premise architecture (L0-L7)
# Format: name -> (layer, paradigm, short_label)
MODULES = {
    # L0: Foundation
    "Basic":            (0, "structural", "Basic"),
    "Computation":      (0, "structural", "Computation"),
    "Data":             (0, "structural", "Data"),
    # L1: Learner
    "Learner.Core":     (1, "structural", "Learner"),
    "Learner.Props":    (1, "structural", "Properties"),
    "Learner.Active":   (1, "pac", "Active"),
    "Learner.Bayesian": (1, "bayes", "Bayesian"),
    "Learner.VS":       (1, "pac", "VersionSpace"),
    "Learner.Closure":  (1, "pac", "Closure"),
    "Learner.Monad":    (1, "pac", "Monad"),
    # L2: Criterion
    "Criterion.PAC":    (2, "pac", "PAC Criterion"),
    "Criterion.Online": (2, "online", "Online Criterion"),
    "Criterion.Gold":   (2, "gold", "Gold Criterion"),
    "Criterion.Ext":    (2, "pac", "Extended"),
    # L3: Complexity measures
    "VCDimension":      (3, "pac", "VCDim"),
    "Littlestone":      (3, "online", "Littlestone"),
    "MindChange":       (3, "gold", "MindChange"),
    "Ordinal":          (3, "gold", "Ordinal"),
    # L4: Infrastructure
    "Generalization":   (4, "pac", "Generalization"),
    "Symmetrization":   (4, "pac", "Symmetrization"),
    "Rademacher":       (4, "pac", "Rademacher"),
    "Structures":       (4, "pac", "Structures"),
    "Measurability":    (4, "pac", "Measurability"),
    "GameInfra":        (4, "online", "GameInfra"),
    "BorelBridge":      (4, "dst", "BorelBridge"),
    "Interpolation":    (4, "dst", "Interpolation"),
    "Amalgamation":     (4, "dst", "Amalgamation"),
    # L5: Pure Math
    "Choquet":          (5, "dst", "Choquet"),
    "AnalyticMeas":     (5, "dst", "AnalyticMeas"),
    "Concentration":    (5, "pac", "Concentration"),
    "Exchangeability":  (5, "pac", "Exchangeability"),
    "KLDivergence":     (5, "bayes", "KLDivergence"),
    "ReaderMonad":      (5, "structural", "ReaderMonad"),
    # L6: Theorems
    "Thm.PAC":          (6, "pac", "PAC Thm"),
    "Thm.Online":       (6, "online", "Online Thm"),
    "Thm.Gold":         (6, "gold", "Gold Thm"),
    "Thm.Separation":   (6, "separation", "Separation"),
    "Thm.BorelAnalytic":(6, "dst", "Borel-Analytic"),
    "Thm.PACBayes":     (6, "bayes", "PAC-Bayes"),
    "Thm.Extended":     (6, "pac", "Extended Thm"),
    # L7: Process / Bridge
    "Process":          (7, "structural", "Process"),
    "Bridge":           (7, "structural", "Bridge"),
}

# Edges: module -> module (import dependencies)
EDGES = [
    ("Learner.Core", "Basic"), ("Learner.Props", "Learner.Core"),
    ("Learner.Active", "Learner.Core"), ("Learner.Bayesian", "Learner.Core"),
    ("Learner.VS", "Learner.Core"),
    ("Criterion.PAC", "Learner.Core"), ("Criterion.Online", "Learner.Core"),
    ("Criterion.Gold", "Learner.Core"), ("Criterion.Ext", "Criterion.PAC"),
    ("VCDimension", "Criterion.PAC"), ("Littlestone", "Criterion.Online"),
    ("MindChange", "Criterion.Gold"), ("Ordinal", "MindChange"),
    ("Generalization", "VCDimension"), ("Symmetrization", "Generalization"),
    ("Rademacher", "Symmetrization"), ("Structures", "VCDimension"),
    ("Measurability", "Structures"), ("GameInfra", "Littlestone"),
    ("BorelBridge", "Measurability"), ("BorelBridge", "AnalyticMeas"),
    ("Interpolation", "Measurability"),
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
    ("Amalgamation", "Interpolation"),
    ("Learner.Closure", "Learner.Core"), ("Learner.Closure", "Generalization"),
    ("Learner.Monad", "Learner.Closure"), ("Learner.Monad", "ReaderMonad"),
    ("Process", "Thm.PAC"), ("Bridge", "Thm.PAC"),
]

# Metaprogram hyperedges: name -> list of modules involved
HYPEREDGES = {
    "PAC chain\n(MP1-MP5)": {
        "modules": ["VCDimension", "Generalization", "Symmetrization",
                     "Rademacher", "Concentration", "Exchangeability",
                     "Measurability", "Thm.PAC"],
        "grey": 0.90,
    },
    "Borel-analytic\nbridge (MP17,20)": {
        "modules": ["Choquet", "AnalyticMeas", "BorelBridge",
                     "Thm.BorelAnalytic", "Measurability"],
        "grey": 0.82,
    },
    "Online potential\n(MP9-MP11)": {
        "modules": ["Littlestone", "GameInfra", "Thm.Online"],
        "grey": 0.88,
    },
    "Gold locking\n(MP12)": {
        "modules": ["MindChange", "Ordinal", "Thm.Gold"],
        "grey": 0.85,
    },
    "PAC-Bayes\n(MP21)": {
        "modules": ["KLDivergence", "Thm.PACBayes"],
        "grey": 0.92,
    },
    "Separation\nwitness (MP14,19)": {
        "modules": ["Measurability", "Thm.Separation",
                     "Thm.BorelAnalytic", "Structures"],
        "grey": 0.87,
    },
    "Composition\nclosure": {
        "modules": ["Interpolation", "Amalgamation", "Learner.Closure",
                     "Learner.Monad", "Learner.VS", "ReaderMonad"],
        "grey": 0.94,
    },
}

# Paradigm colors (grey shades for old school academic)
PARADIGM_MARKERS = {
    "structural": {"fill": "white", "edge": "black"},
    "pac":        {"fill": "#e8e8e8", "edge": "black"},
    "online":     {"fill": "#d0d0d0", "edge": "black"},
    "gold":       {"fill": "#c0c0c0", "edge": "black"},
    "dst":        {"fill": "#b0b0b0", "edge": "black"},
    "bayes":      {"fill": "#a0a0a0", "edge": "black"},
    "separation": {"fill": "#909090", "edge": "black"},
}


# ============================================================
# Sugiyama layout: barycenter heuristic for crossing reduction
# ============================================================

def barycenter_ordering(modules, edges, n_iterations=20):
    """
    Barycenter heuristic for crossing reduction (Sugiyama et al. 1981).

    For each layer (top to bottom, then bottom to top), reorder nodes
    by the average x-position of their neighbors in the adjacent fixed layer.
    Repeat for n_iterations sweeps.
    """
    # Group modules by layer
    layers = defaultdict(list)
    for name, (layer, _, _) in modules.items():
        layers[layer].append(name)

    # Build adjacency
    adj = defaultdict(set)
    for src, dst in edges:
        adj[src].add(dst)
        adj[dst].add(src)

    # Initial ordering: alphabetical within each layer
    for layer in layers:
        layers[layer].sort()

    # Assign initial x positions
    positions = {}
    for layer_idx in sorted(layers.keys()):
        nodes = layers[layer_idx]
        for i, node in enumerate(nodes):
            positions[node] = (i, layer_idx)

    # Barycenter sweep
    for iteration in range(n_iterations):
        # Top-down sweep
        for layer_idx in sorted(layers.keys()):
            nodes = layers[layer_idx]
            barycenters = {}
            for node in nodes:
                neighbors_above = [n for n in adj[node]
                                   if modules[n][0] < layer_idx]
                neighbors_below = [n for n in adj[node]
                                   if modules[n][0] > layer_idx]
                all_neighbors = neighbors_above + neighbors_below
                if all_neighbors:
                    barycenters[node] = np.mean([positions[n][0]
                                                 for n in all_neighbors])
                else:
                    barycenters[node] = positions[node][0]

            # Sort by barycenter
            nodes.sort(key=lambda n: barycenters[n])
            layers[layer_idx] = nodes

            # Update positions
            for i, node in enumerate(nodes):
                positions[node] = (i, layer_idx)

    return layers, positions


def compute_node_coordinates(layers, positions, x_spacing=2.0, y_spacing=2.5):
    """Convert layer/position indices to actual coordinates.
    Center each layer horizontally."""
    coords = {}
    max_layer = max(layers.keys())

    for layer_idx, nodes in layers.items():
        n = len(nodes)
        x_offset = -(n - 1) * x_spacing / 2  # Center the layer
        for i, node in enumerate(nodes):
            x = x_offset + i * x_spacing
            y = (max_layer - layer_idx) * y_spacing  # Top layer at top
            coords[node] = (x, y)

    return coords


# ============================================================
# Drawing functions
# ============================================================

def draw_hyperedge_hull(ax, coords, module_list, color, label, alpha=0.15):
    """Draw a convex hull around a set of modules as a shaded region."""
    points = np.array([coords[m] for m in module_list if m in coords])
    if len(points) < 3:
        # For 2 points, draw an ellipse
        if len(points) == 2:
            cx, cy = points.mean(axis=0)
            dx = abs(points[1][0] - points[0][0]) + 1.5
            dy = abs(points[1][1] - points[0][1]) + 1.2
            ellipse = mpatches.Ellipse((cx, cy), dx, dy,
                                        facecolor=color, edgecolor='black',
                                        alpha=alpha, linewidth=0.8,
                                        linestyle='--')
            ax.add_patch(ellipse)
            ax.text(cx, cy - dy/2 - 0.3, label,
                    ha='center', va='top', fontsize=7,
                    fontfamily='serif', fontstyle='italic')
        return

    # Add padding around points for hull
    padded = []
    cx, cy = points.mean(axis=0)
    for px, py in points:
        dx, dy = px - cx, py - cy
        dist = np.sqrt(dx**2 + dy**2)
        if dist > 0:
            padded.append((px + 0.6 * dx/dist, py + 0.6 * dy/dist))
        else:
            padded.append((px + 0.6, py + 0.6))
            padded.append((px - 0.6, py - 0.6))
    padded = np.array(padded)

    try:
        hull = ConvexHull(padded)
        hull_points = padded[hull.vertices]
        # Close the polygon
        hull_points = np.vstack([hull_points, hull_points[0]])
        ax.fill(hull_points[:, 0], hull_points[:, 1],
                facecolor=color, edgecolor='black',
                alpha=alpha, linewidth=0.8, linestyle='--')
        # Label at bottom of hull
        label_y = hull_points[:, 1].min() - 0.3
        label_x = hull_points[:, 0].mean()
        ax.text(label_x, label_y, label,
                ha='center', va='top', fontsize=7,
                fontfamily='serif', fontstyle='italic')
    except Exception:
        pass


def draw_overview(modules, edges, hyperedges, output_path):
    """Draw the overview hypergraph: modules as nodes, metaprograms as hulls."""
    plt.rcParams['font.family'] = 'serif'
    plt.rcParams['font.serif'] = ['Times New Roman', 'DejaVu Serif']
    fig, ax = plt.subplots(1, 1, figsize=(18, 24))

    # Sugiyama layout
    layers, positions = barycenter_ordering(modules, edges)
    coords = compute_node_coordinates(layers, positions,
                                       x_spacing=2.8, y_spacing=3.2)

    # Draw hyperedge hulls FIRST (background)
    for he_name, he_data in hyperedges.items():
        grey_val = he_data["grey"]
        color = (grey_val, grey_val, grey_val)
        draw_hyperedge_hull(ax, coords, he_data["modules"],
                           color=color, label=he_name, alpha=0.35)

    # Draw edges
    for src, dst in edges:
        if src in coords and dst in coords:
            x0, y0 = coords[src]
            x1, y1 = coords[dst]
            ax.annotate("", xy=(x1, y1), xytext=(x0, y0),
                        arrowprops=dict(arrowstyle='->', color='#333333',
                                        linewidth=0.7, connectionstyle='arc3,rad=0.03'))

    # Draw nodes
    for name, (layer, paradigm, label) in modules.items():
        if name not in coords:
            continue
        x, y = coords[name]
        style = PARADIGM_MARKERS.get(paradigm, PARADIGM_MARKERS["structural"])

        # Node box -- width proportional to label length
        box_w = max(1.8, len(label) * 0.16 + 0.6)
        bbox = FancyBboxPatch((x - box_w/2, y - 0.3), box_w, 0.6,
                               boxstyle="round,pad=0.1",
                               facecolor=style["fill"],
                               edgecolor=style["edge"],
                               linewidth=0.9)
        ax.add_patch(bbox)
        ax.text(x, y, label, ha='center', va='center',
                fontsize=8, fontfamily='serif', fontweight='normal')

    # Layer labels on right margin
    max_x = max(c[0] for c in coords.values()) + 2.5
    for layer_idx in sorted(layers.keys()):
        y = (max(layers.keys()) - layer_idx) * 3.0
        ax.text(max_x, y, f"L{layer_idx}",
                ha='left', va='center', fontsize=9,
                fontfamily='serif', fontweight='bold',
                color='#333333')

    # Title
    ax.set_title("Discovery Hypergraph: Metaprograms over Module Dependencies",
                 fontsize=14, fontfamily='serif', fontweight='bold', pad=20)

    # Legend
    legend_elements = []
    for paradigm, style in PARADIGM_MARKERS.items():
        if paradigm == "structural":
            continue
        legend_elements.append(mpatches.Patch(
            facecolor=style["fill"], edgecolor='black',
            label=paradigm.upper()))
    ax.legend(handles=legend_elements, loc='lower right',
              fontsize=8, frameon=True, fancybox=False,
              edgecolor='black', prop={'family': 'serif'})

    ax.set_xlim(min(c[0] for c in coords.values()) - 2,
                max(c[0] for c in coords.values()) + 4)
    ax.set_ylim(min(c[1] for c in coords.values()) - 2,
                max(c[1] for c in coords.values()) + 2)
    ax.set_aspect('equal')
    ax.axis('off')

    plt.tight_layout()
    plt.savefig(output_path, dpi=200, bbox_inches='tight',
                facecolor='white', edgecolor='none')
    plt.close()
    print(f"Saved: {output_path}")


# ============================================================
# Detail panels: per-paradigm theorem-cluster views
# ============================================================

def draw_paradigm_detail(paradigm_name, module_subset, edge_subset,
                          hyperedge_subset, output_path):
    """Draw a detail panel for a single paradigm."""
    fig, ax = plt.subplots(1, 1, figsize=(10, 12))

    # Filter modules
    filtered_modules = {k: v for k, v in MODULES.items() if k in module_subset}

    # Sugiyama layout
    layers, positions = barycenter_ordering(filtered_modules, edge_subset)
    coords = compute_node_coordinates(layers, positions,
                                       x_spacing=2.5, y_spacing=3.5)

    # Hyperedge hulls
    for he_name, he_data in hyperedge_subset.items():
        grey_val = he_data["grey"]
        color = (grey_val, grey_val, grey_val)
        mods = [m for m in he_data["modules"] if m in coords]
        if len(mods) >= 2:
            draw_hyperedge_hull(ax, coords, mods,
                               color=color, label=he_name, alpha=0.25)

    # Edges
    for src, dst in edge_subset:
        if src in coords and dst in coords:
            x0, y0 = coords[src]
            x1, y1 = coords[dst]
            ax.annotate("", xy=(x1, y1), xytext=(x0, y0),
                        arrowprops=dict(arrowstyle='->',
                                        color='#555555', linewidth=0.8))

    # Nodes
    for name in module_subset:
        if name not in coords or name not in MODULES:
            continue
        x, y = coords[name]
        layer, paradigm, label = MODULES[name]
        style = PARADIGM_MARKERS.get(paradigm, PARADIGM_MARKERS["structural"])
        bbox = FancyBboxPatch((x - 0.9, y - 0.3), 1.8, 0.6,
                               boxstyle="round,pad=0.1",
                               facecolor=style["fill"],
                               edgecolor=style["edge"],
                               linewidth=1.0)
        ax.add_patch(bbox)
        ax.text(x, y, label, ha='center', va='center',
                fontsize=8, fontfamily='serif')

    ax.set_title(f"Detail: {paradigm_name} Paradigm",
                 fontsize=12, fontfamily='serif', fontweight='bold', pad=15)
    ax.set_aspect('equal')
    ax.axis('off')
    plt.tight_layout()
    plt.savefig(output_path, dpi=200, bbox_inches='tight',
                facecolor='white', edgecolor='none')
    plt.close()
    print(f"Saved: {output_path}")


# ============================================================
# Main
# ============================================================

def main():
    import os
    repo_root = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
    assets_dir = os.path.join(repo_root, "assets")
    os.makedirs(assets_dir, exist_ok=True)

    # Overview
    draw_overview(MODULES, EDGES, HYPEREDGES,
                  os.path.join(assets_dir, "hypergraph_overview.png"))

    # PAC detail
    pac_modules = {"Basic", "Learner.Core", "Learner.Props", "Learner.Active",
                   "Learner.VS", "Criterion.PAC", "Criterion.Ext",
                   "VCDimension", "Generalization", "Symmetrization",
                   "Rademacher", "Structures", "Measurability",
                   "Concentration", "Exchangeability",
                   "Thm.PAC", "Thm.Extended", "Thm.Separation"}
    pac_edges = [(s, d) for s, d in EDGES
                 if s in pac_modules and d in pac_modules]
    pac_he = {k: v for k, v in HYPEREDGES.items()
              if any(m in pac_modules for m in v["modules"])}
    draw_paradigm_detail("PAC", pac_modules, pac_edges, pac_he,
                         os.path.join(assets_dir, "hypergraph_pac.png"))

    # Online + Gold detail
    og_modules = {"Basic", "Learner.Core", "Criterion.Online", "Criterion.Gold",
                  "Littlestone", "MindChange", "Ordinal", "GameInfra",
                  "Thm.Online", "Thm.Gold"}
    og_edges = [(s, d) for s, d in EDGES
                if s in og_modules and d in og_modules]
    og_he = {k: v for k, v in HYPEREDGES.items()
             if any(m in og_modules for m in v["modules"])}
    draw_paradigm_detail("Online + Gold", og_modules, og_edges, og_he,
                         os.path.join(assets_dir, "hypergraph_online_gold.png"))

    # DST detail
    dst_modules = {"Basic", "Measurability", "Structures", "BorelBridge",
                   "Interpolation", "Choquet", "AnalyticMeas",
                   "Thm.BorelAnalytic", "Thm.Separation"}
    dst_edges = [(s, d) for s, d in EDGES
                 if s in dst_modules and d in dst_modules]
    dst_he = {k: v for k, v in HYPEREDGES.items()
              if any(m in dst_modules for m in v["modules"])}
    draw_paradigm_detail("Descriptive Set Theory", dst_modules, dst_edges,
                         dst_he, os.path.join(assets_dir, "hypergraph_dst.png"))


if __name__ == "__main__":
    main()
