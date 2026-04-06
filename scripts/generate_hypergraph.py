#!/usr/bin/env python3
"""
Generate the discovery hypergraph for Section X.

ALL data is machine-derived:
  - Nodes: every .lean file in FLT_Proofs/ (excluding hub re-export files)
  - Edges: every 'import FLT_Proofs.X' statement
  - Layers: topological depth from import DAG
  - Hyperedges: metaprogram groupings (manually curated, the only non-derived data)

Layout: Sugiyama with barycenter heuristic.
Rendering: matplotlib. Edges behind nodes (zorder separation).
Style: old school academia.
"""

import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
import matplotlib.patches as mpatches
from matplotlib.patches import FancyBboxPatch
import numpy as np
from collections import defaultdict
from scipy.spatial import ConvexHull
import os
import re

REPO_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
FLT_DIR = os.path.join(REPO_ROOT, "FLT_Proofs")
ASSETS = os.path.join(REPO_ROOT, "assets")
os.makedirs(ASSETS, exist_ok=True)

# Hub files that just re-export (skip as nodes)
HUBS = {"Learner", "Criterion", "Complexity", "Theorem"}

# PureMath / MathLib modules: rendered as separate right-side column
PUREMATH_PREFIXES = ("PureMath.", "MathLib.")


# ============================================================
# 1. Machine-derive nodes and edges from the codebase
# ============================================================

def scan_imports():
    """Scan FLT_Proofs/ for all .lean files and their imports."""
    imports = defaultdict(set)  # module -> set of dependencies
    all_modules = set()

    for root, dirs, files in os.walk(FLT_DIR):
        for f in files:
            if not f.endswith('.lean'):
                continue
            path = os.path.join(root, f)
            mod = path.replace(FLT_DIR + '/', '', 1).replace('.lean', '').replace('/', '.')
            all_modules.add(mod)
            with open(path) as fh:
                for line in fh:
                    m = re.match(r'^import FLT_Proofs\.(.+)', line.strip())
                    if m:
                        dep = m.group(1)
                        imports[mod].add(dep)

    # Remove hubs
    all_modules -= HUBS
    return all_modules, imports


def compute_layers(all_modules, imports):
    """Compute topological depth for each module."""
    depth = {}

    # Seed: modules with no deps (or only hub deps)
    for mod in all_modules:
        deps = (imports.get(mod, set()) - HUBS) & all_modules
        if not deps:
            depth[mod] = 0

    changed = True
    while changed:
        changed = False
        for mod in all_modules:
            if mod in depth:
                continue
            deps = (imports.get(mod, set()) - HUBS) & all_modules
            resolved = deps & set(depth.keys())
            if resolved == deps:
                d = max(depth[dep] for dep in deps) + 1
                depth[mod] = d
                changed = True

    return depth


def is_puremath(mod):
    return any(mod.startswith(p) for p in PUREMATH_PREFIXES)


def derive_graph_data():
    """Derive all nodes, edges, and layers from the codebase.

    Returns:
        kernel_modules: dict of non-PureMath modules {name: (layer, label)}
        kernel_edges: list of (src, dst) between kernel modules
        puremath_modules: dict of PureMath/MathLib modules {name: label}
        puremath_edges: list of (puremath_mod, kernel_consumer) -- horizontal edges
    """
    all_modules, imports = scan_imports()

    # Separate PureMath from kernel
    kernel_mods = {m for m in all_modules if not is_puremath(m)}
    pm_mods = {m for m in all_modules if is_puremath(m)}

    # Compute layers only for kernel modules
    # Remove PureMath deps before computing depth (they're lateral, not vertical)
    kernel_imports = {}
    for mod in kernel_mods:
        deps = (imports.get(mod, set()) - HUBS) & kernel_mods
        kernel_imports[mod] = deps

    depth = {}
    for mod in kernel_mods:
        if not kernel_imports.get(mod):
            depth[mod] = 0
    changed = True
    while changed:
        changed = False
        for mod in kernel_mods:
            if mod in depth:
                continue
            deps = kernel_imports.get(mod, set())
            resolved = deps & set(depth.keys())
            if resolved == deps and deps:
                depth[mod] = max(depth[d] for d in deps) + 1
                changed = True

    # Kernel edges
    kernel_edges = []
    for mod, deps in imports.items():
        if mod in HUBS or mod not in depth:
            continue
        for dep in deps:
            if dep in HUBS or dep not in depth or is_puremath(dep):
                continue
            kernel_edges.append((mod, dep))

    # Kernel module data
    kernel_modules = {}
    for mod in sorted(depth.keys()):
        label = mod.split('.')[-1]
        kernel_modules[mod] = (depth[mod], label)

    # PureMath module data
    puremath_modules = {}
    for mod in sorted(pm_mods):
        label = mod.split('.')[-1]
        puremath_modules[mod] = label

    # PureMath -> kernel consumer edges (horizontal)
    puremath_edges = []
    for mod, deps in imports.items():
        if mod in HUBS or mod not in depth:
            continue
        for dep in deps:
            if is_puremath(dep) and dep in pm_mods:
                puremath_edges.append((dep, mod))

    # Also internal PureMath edges (e.g., AnalyticMeas -> Choquet)
    puremath_internal = []
    for mod in pm_mods:
        for dep in imports.get(mod, set()):
            if dep in pm_mods:
                puremath_internal.append((mod, dep))

    return kernel_modules, kernel_edges, puremath_modules, puremath_edges, puremath_internal


# ============================================================
# 2. Hyperedge definitions (the only manually curated data)
# ============================================================

HYPEREDGES = {
    "PAC chain": {
        "modules": ["Complexity.VCDimension", "Complexity.Generalization",
                     "Complexity.Symmetrization", "Complexity.Rademacher",
                     "PureMath.Concentration", "PureMath.Exchangeability",
                     "Complexity.Measurability", "Theorem.PAC"],
    },
    "Borel-analytic\nbridge": {
        "modules": ["PureMath.ChoquetCapacity", "PureMath.AnalyticMeasurability",
                     "Complexity.BorelAnalyticBridge",
                     "Theorem.BorelAnalyticSeparation", "Complexity.Measurability"],
    },
    "Online\npotential": {
        "modules": ["Complexity.Littlestone", "Complexity.GameInfra",
                     "Theorem.Online"],
    },
    "Gold\nlocking": {
        "modules": ["Complexity.MindChange", "Complexity.Ordinal",
                     "Theorem.Gold"],
    },
    "PAC-Bayes": {
        "modules": ["PureMath.KLDivergence", "Theorem.PACBayes"],
    },
    "Composition\nclosure": {
        "modules": ["Complexity.Interpolation", "Complexity.Amalgamation",
                     "Learner.Closure", "Learner.Monad",
                     "Learner.VersionSpace", "PureMath.ReaderMonad"],
    },
    "Compression": {
        "modules": ["Complexity.Compression", "Complexity.FiniteSupportUC",
                     "Complexity.DualVC", "PureMath.ApproxMinimax",
                     "PureMath.FiniteVCApprox", "PureMath.BinaryMatrix"],
    },
}


# ============================================================
# 3. Grey assignment by connectivity
# ============================================================

def assign_hyperedge_greys(hyperedges):
    sizes = {name: len(data["modules"]) for name, data in hyperedges.items()}
    min_s, max_s = min(sizes.values()), max(sizes.values())
    spread = max(max_s - min_s, 1)
    return {name: 0.65 + ((size - min_s) / spread) * 0.27
            for name, size in sizes.items()}


def build_node_to_hyperedge(hyperedges):
    node_he = {}
    for he_name, he_data in hyperedges.items():
        for mod in he_data["modules"]:
            if mod not in node_he:
                node_he[mod] = he_name
    return node_he


# ============================================================
# 4. Barycenter layout
# ============================================================

def barycenter_ordering(modules, edges, n_iterations=30):
    layers = defaultdict(list)
    for name, (layer, _) in modules.items():
        layers[layer].append(name)

    adj = defaultdict(set)
    for src, dst in edges:
        if src in modules and dst in modules:
            adj[src].add(dst)
            adj[dst].add(src)

    for layer in layers:
        layers[layer].sort()

    positions = {}
    for li in sorted(layers.keys()):
        for i, node in enumerate(layers[li]):
            positions[node] = (i, li)

    for _ in range(n_iterations):
        for li in sorted(layers.keys()):
            nodes = layers[li]
            bary = {}
            for node in nodes:
                nbrs = [n for n in adj[node] if n in positions]
                bary[node] = np.mean([positions[n][0] for n in nbrs]) if nbrs else positions[node][0]
            nodes.sort(key=lambda n: bary[n])
            layers[li] = nodes
            for i, node in enumerate(nodes):
                positions[node] = (i, li)

        for li in reversed(sorted(layers.keys())):
            nodes = layers[li]
            bary = {}
            for node in nodes:
                nbrs = [n for n in adj[node] if n in positions]
                bary[node] = np.mean([positions[n][0] for n in nbrs]) if nbrs else positions[node][0]
            nodes.sort(key=lambda n: bary[n])
            layers[li] = nodes
            for i, node in enumerate(nodes):
                positions[node] = (i, li)

    return layers, positions


def compute_coords(layers, x_spacing=6.5, y_spacing=4.5):
    coords = {}
    max_layer = max(layers.keys())
    for li, nodes in layers.items():
        n = len(nodes)
        x_off = -(n - 1) * x_spacing / 2
        for i, node in enumerate(nodes):
            coords[node] = (x_off + i * x_spacing, (max_layer - li) * y_spacing)
    return coords


# ============================================================
# 5. Drawing
# ============================================================

# Font sizing: 0.36 pt per inch of figure height (shared constant across all diagrams)
FONT_RATIO = 0.36

# Fixed node width; height grows for long labels
NODE_W = 3.8
NODE_H = 0.9


def _wrap_label(label, max_chars=12):
    """Wrap long labels onto two lines."""
    if len(label) <= max_chars:
        return label
    # Try splitting at capital letter boundaries
    parts = re.findall(r'[A-Z][a-z]*|[a-z]+', label)
    if len(parts) >= 2:
        mid = len(parts) // 2
        return ''.join(parts[:mid]) + '\n' + ''.join(parts[mid:])
    # Fallback: split at midpoint
    mid = len(label) // 2
    return label[:mid] + '-\n' + label[mid:]


def draw_hull(ax, coords, module_list, color, label, alpha=0.22):
    """Draw hull using node box corners as vertices.
    Each node generates 4 corner points (box corners), then convex hull wraps them."""
    members = [m for m in module_list if m in coords]
    if len(members) < 2:
        return

    # Generate corner points from each node's bounding box
    pad = 0.3  # small padding beyond box edge
    corners = []
    for m in members:
        x, y = coords[m]
        hw = NODE_W / 2 + pad
        hh = NODE_H / 2 + pad
        corners.extend([
            (x - hw, y - hh),
            (x + hw, y - hh),
            (x - hw, y + hh),
            (x + hw, y + hh),
        ])
    corners = np.array(corners)
    cx, cy = np.mean([coords[m] for m in members], axis=0)

    if len(corners) < 3:
        return

    try:
        hull = ConvexHull(corners)
        verts = corners[hull.vertices]
        verts = np.vstack([verts, verts[0]])
        ax.fill(verts[:, 0], verts[:, 1], facecolor=color, edgecolor='#555555',
                alpha=alpha, linewidth=0.6, linestyle='--', zorder=0)
        ax.text(cx, cy, label, ha='center', va='center',
                fontsize=13, fontfamily='serif', fontstyle='italic',
                color='#222222', alpha=0.7, zorder=0)
    except Exception:
        pass


def draw_graph(modules, edges, hyperedges, output_path,
               puremath_modules=None, puremath_edges=None, puremath_internal=None,
               title=None, figsize=(36, 50), x_spacing=6.5, y_spacing=4.5):
    plt.rcParams['font.family'] = 'serif'
    plt.rcParams['font.serif'] = ['Times New Roman', 'DejaVu Serif']
    fig, ax = plt.subplots(1, 1, figsize=figsize)

    layers, positions = barycenter_ordering(modules, edges)
    coords = compute_coords(layers, x_spacing=x_spacing, y_spacing=y_spacing)

    he_greys = assign_hyperedge_greys(hyperedges) if hyperedges else {}
    node_he = build_node_to_hyperedge(hyperedges) if hyperedges else {}

    # ---- PureMath column on the right ----
    pm_coords = {}
    if puremath_modules and puremath_edges:
        max_kernel_x = max(c[0] for c in coords.values())
        pm_base_x = max_kernel_x + x_spacing * 2.5

        # Find consumer Y for each PM module
        pm_y = {}
        for pm_mod, consumer in puremath_edges:
            if consumer in coords and pm_mod not in pm_y:
                pm_y[pm_mod] = coords[consumer][1]

        # Group PM modules by Y level to spread horizontally
        y_groups = defaultdict(list)
        for pm_mod in puremath_modules:
            if pm_mod in pm_y:
                y_groups[pm_y[pm_mod]].append(pm_mod)

        for y_val, mods in y_groups.items():
            n = len(mods)
            x_start = pm_base_x - (n - 1) * x_spacing / 2
            for i, pm_mod in enumerate(sorted(mods)):
                pm_coords[pm_mod] = (x_start + i * x_spacing, y_val)

        # Column header
        if pm_coords:
            all_pm_xs = [c[0] for c in pm_coords.values()]
            all_pm_ys = [c[1] for c in pm_coords.values()]
            center_x = np.mean(all_pm_xs)
            top_y = max(all_pm_ys) + y_spacing * 0.8
            ax.text(center_x, top_y, "PureMath", ha='center', va='bottom',
                    fontsize=20, fontfamily='serif', fontweight='bold',
                    color='#4a5d8a', fontstyle='italic')
            # Vertical separator line
            sep_x = pm_base_x - x_spacing * 1.2
            ax.plot([sep_x, sep_x],
                    [min(all_pm_ys) - 1.5, max(all_pm_ys) + 1.5],
                    color='#8899bb', linewidth=0.8, linestyle=':', zorder=0)

    # Merge coords for hull computation
    all_coords = {**coords, **pm_coords}

    # 1. Hulls (zorder=0)
    for he_name, he_data in hyperedges.items():
        g = he_greys[he_name]
        draw_hull(ax, all_coords, he_data["modules"], color=(g, g, g), label=he_name)

    # 2. Kernel edges (zorder=1, vertical)
    for src, dst in edges:
        if src in coords and dst in coords:
            x0, y0 = coords[src]
            x1, y1 = coords[dst]
            src_he = node_he.get(src)
            dst_he = node_he.get(dst)
            if src_he and src_he == dst_he:
                g = he_greys[src_he]
                ec = (g * 0.6, g * 0.6, g * 0.6)
                ew = 0.8
            else:
                ec = '#888888'
                ew = 0.4
            ax.annotate("", xy=(x1, y1), xytext=(x0, y0),
                        arrowprops=dict(arrowstyle='->', color=ec,
                                        linewidth=ew,
                                        connectionstyle='arc3,rad=0.04'),
                        zorder=1)

    # 3. PureMath -> kernel edges (zorder=1, horizontal, slate blue)
    if puremath_edges:
        for pm_mod, consumer in puremath_edges:
            if pm_mod in pm_coords and consumer in coords:
                x0, y0 = pm_coords[pm_mod]
                x1, y1 = coords[consumer]
                ax.annotate("", xy=(x1, y1), xytext=(x0, y0),
                            arrowprops=dict(arrowstyle='->',
                                            color='#4a5d8a',
                                            linewidth=0.8,
                                            linestyle='dashed',
                                            connectionstyle='arc3,rad=0.0'),
                            zorder=1)

    # 4. PureMath internal edges (zorder=1, vertical within column, slate blue)
    if puremath_internal:
        for src, dst in puremath_internal:
            if src in pm_coords and dst in pm_coords:
                x0, y0 = pm_coords[src]
                x1, y1 = pm_coords[dst]
                ax.annotate("", xy=(x1, y1), xytext=(x0, y0),
                            arrowprops=dict(arrowstyle='->',
                                            color='#4a5d8a',
                                            linewidth=0.7,
                                            connectionstyle='arc3,rad=0.0'),
                            zorder=1)

    # 5. Kernel nodes (zorder=3, fixed width, variable height)
    for name, (layer, label) in modules.items():
        if name not in coords:
            continue
        x, y = coords[name]
        he = node_he.get(name)
        fill = (he_greys[he], he_greys[he], he_greys[he]) if he else 'white'
        bh = NODE_H + max(0, (len(label) - 10) * 0.08)
        wrapped = _wrap_label(label)
        if '\n' in wrapped:
            bh += 0.5
        ax.add_patch(FancyBboxPatch((x - NODE_W/2, y - bh/2), NODE_W, bh,
                     boxstyle="round,pad=0.08", facecolor=fill,
                     edgecolor='black', linewidth=0.8, zorder=3))
        ax.text(x, y, wrapped, ha='center', va='center',
                fontsize=18, fontfamily='serif', fontweight='bold',
                color='black', zorder=4)

    # 6. PureMath nodes (zorder=3, computed greys like kernel nodes)
    for name, label in (puremath_modules or {}).items():
        if name not in pm_coords:
            continue
        x, y = pm_coords[name]
        he = node_he.get(name)
        fill = (he_greys[he], he_greys[he], he_greys[he]) if he else 'white'
        bh = NODE_H + max(0, (len(label) - 10) * 0.08)
        wrapped = _wrap_label(label)
        if '\n' in wrapped:
            bh += 0.5
        ax.add_patch(FancyBboxPatch((x - NODE_W/2, y - bh/2), NODE_W, bh,
                     boxstyle="round,pad=0.08", facecolor=fill,
                     edgecolor='black', linewidth=0.8,
                     zorder=3))
        ax.text(x, y, wrapped, ha='center', va='center',
                fontsize=18, fontfamily='serif', fontweight='bold',
                color='black', zorder=4)

    # 7. Layer labels (left side)
    min_x = min(c[0] for c in coords.values()) - 3.0
    layer_ys = defaultdict(list)
    for mod, (layer, _) in modules.items():
        if mod in coords:
            layer_ys[layer].append(coords[mod][1])
    for li, ys in sorted(layer_ys.items()):
        ax.text(min_x, np.mean(ys), f'L{li}', ha='right', va='center',
                fontsize=18, fontfamily='serif', fontweight='bold', color='black')

    if title:
        ax.set_title(title, fontsize=22, fontfamily='serif',
                     fontweight='bold', pad=20)

    ax.set_aspect('equal')
    ax.axis('off')
    plt.tight_layout()
    plt.savefig(output_path, dpi=150, bbox_inches='tight',
                facecolor='white', edgecolor='none')
    plt.close()
    print(f"Saved: {output_path}")


# ============================================================
# 6. Detail panels
# ============================================================

def filter_graph(modules, edges, keep):
    filt_mods = {k: v for k, v in modules.items() if k in keep}
    filt_edges = [(s, d) for s, d in edges if s in keep and d in keep]
    return filt_mods, filt_edges


def main():
    km, ke, pm, pe, pi = derive_graph_data()
    print(f"Derived: {len(km)} kernel modules, {len(ke)} kernel edges, "
          f"{len(pm)} PureMath modules, {len(pe)} cross edges, "
          f"{max(v[0] for v in km.values())+1} layers")

    # Overview
    draw_graph(km, ke, HYPEREDGES,
               os.path.join(ASSETS, 'hypergraph_overview.png'),
               puremath_modules=pm, puremath_edges=pe, puremath_internal=pi,
               title='Kernel Structure with Proof Method Regions',
               figsize=(42, 50), x_spacing=6.5, y_spacing=4.5)

    # PAC detail
    pac_keep = set()
    for he in ["PAC chain"]:
        pac_keep.update(HYPEREDGES[he]["modules"])
    dep_set = set()
    for mod in pac_keep:
        for s, d in ke:
            if s == mod: dep_set.add(d)
            if d == mod: dep_set.add(s)
    pac_keep |= dep_set
    pac_km, pac_ke = filter_graph(km, ke, pac_keep)
    pac_he = {k: v for k, v in HYPEREDGES.items()
              if any(m in pac_keep for m in v["modules"])}
    # Filter PM edges relevant to this view
    pac_pm = {k: v for k, v in pm.items() if any(c in pac_keep for p, c in pe if p == k)}
    pac_pe = [(p, c) for p, c in pe if c in pac_keep]
    pac_pi = [(s, d) for s, d in pi if s in pac_pm and d in pac_pm]
    draw_graph(pac_km, pac_ke, pac_he,
               os.path.join(ASSETS, 'hypergraph_pac.png'),
               puremath_modules=pac_pm, puremath_edges=pac_pe, puremath_internal=pac_pi,
               title='PAC Paradigm', figsize=(32, 40),
               x_spacing=5.5, y_spacing=4.5)

    # Online + Gold
    og_keep = set()
    for he in ["Online\npotential", "Gold\nlocking"]:
        og_keep.update(HYPEREDGES[he]["modules"])
    dep_set = set()
    for mod in og_keep:
        for s, d in ke:
            if s == mod: dep_set.add(d)
    og_keep |= dep_set
    og_km, og_ke = filter_graph(km, ke, og_keep)
    og_he = {k: v for k, v in HYPEREDGES.items()
             if any(m in og_keep for m in v["modules"])}
    draw_graph(og_km, og_ke, og_he,
               os.path.join(ASSETS, 'hypergraph_online_gold.png'),
               title='Online + Gold Paradigms', figsize=(20, 30),
               x_spacing=5.0, y_spacing=4.5)

    # DST + Composition
    dst_keep = set()
    for he in ["Borel-analytic\nbridge", "Composition\nclosure"]:
        dst_keep.update(HYPEREDGES[he]["modules"])
    dep_set = set()
    for mod in dst_keep:
        for s, d in ke:
            if s == mod: dep_set.add(d)
    dst_keep |= dep_set
    dst_km, dst_ke = filter_graph(km, ke, dst_keep)
    dst_he = {k: v for k, v in HYPEREDGES.items()
              if any(m in dst_keep for m in v["modules"])}
    dst_pm = {k: v for k, v in pm.items() if any(c in dst_keep for p, c in pe if p == k)}
    dst_pe = [(p, c) for p, c in pe if c in dst_keep]
    dst_pi = [(s, d) for s, d in pi if s in dst_pm and d in dst_pm]
    draw_graph(dst_km, dst_ke, dst_he,
               os.path.join(ASSETS, 'hypergraph_dst.png'),
               puremath_modules=dst_pm, puremath_edges=dst_pe, puremath_internal=dst_pi,
               title='DST + Composition Closure', figsize=(28, 36),
               x_spacing=5.5, y_spacing=4.5)


if __name__ == "__main__":
    main()
