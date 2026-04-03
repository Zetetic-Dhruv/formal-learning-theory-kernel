#!/usr/bin/env python3
"""
Generate the world model figure for Section VIII.

NOT a graph. A Lean-style pseudocode listing showing the proof operad
as a typed metaprogram with 4 layers:
  1. Types (Paradigm, Interface, Generator)
  2. Syntax (Plan)
  3. Typing judgment (HasType, admissible, FailureRule)
  4. Theory growth (GapSpec, extension_sound)

Rendered as a monospaced code block with comments and structure.
"""

import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
import os

REPO_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
ASSETS = os.path.join(REPO_ROOT, "assets")
os.makedirs(ASSETS, exist_ok=True)

# The pseudocode as structured lines: (indent, text, style)
# style: 'comment' | 'keyword' | 'type' | 'code' | 'theorem' | 'section'
LINES = [
    # Layer 1: Types
    (0, "-- Layer 1: The vocabulary of proof obligations", "section"),
    (0, "", "blank"),
    (0, "inductive Paradigm := pac | online | gold | dst | bayes | separation", "keyword"),
    (0, "", "blank"),
    (0, "structure Interface where", "keyword"),
    (1, "name     : String", "code"),
    (1, "locks    : List Paradigm      -- which paradigms can touch this", "code"),
    (1, "premises : List String        -- required hypotheses", "code"),
    (1, "targetTag : String            -- goal shape", "code"),
    (0, "", "blank"),
    (0, "structure Generator where", "keyword"),
    (1, "name    : String", "code"),
    (1, "level   : structural | domain              -- stratification", "code"),
    (1, "input   : Interface                        -- one obligation in", "code"),
    (1, "outputs : List Interface                   -- many obligations out (operad)", "code"),
    (1, "tacticPattern : String                     -- tactic sequence template", "code"),
    (1, "paradigm : List Paradigm                   -- paradigm lock", "code"),
    (0, "", "blank"),
    (0, "-- 17 generators: 5 structural + 12 domain", "comment"),
    (0, "-- 18 interfaces across 7 paradigms", "comment"),
    (0, "", "blank"),

    # Layer 2: Syntax
    (0, "-- Layer 2: The syntax of proof plans", "section"),
    (0, "", "blank"),
    (0, "inductive Plan where", "keyword"),
    (1, "| atom g            -- apply generator g", "code"),
    (1, "| seq p q           -- sequential: p then q on each subgoal", "code"),
    (1, "| par ps            -- parallel: all subgoals simultaneously", "code"),
    (1, "| guard lock p      -- paradigm-guarded execution", "code"),
    (1, "| choose alts       -- backtracking over alternatives", "code"),
    (1, "| extend gapName    -- typed theory extension point", "code"),
    (0, "", "blank"),

    # Layer 3: Typing judgment
    (0, "-- Layer 3: When is a plan well-typed?", "section"),
    (0, "", "blank"),
    (0, "def admissible (Sigma : Theory) (I : Interface) (g : Generator)", "keyword"),
    (2, ": Except RejectReason Unit :=", "code"),
    (1, "check paradigm lock     -- g.paradigm must appear in I.locks", "code"),
    (1, "check premises          -- g.input.premises must appear in I", "code"),
    (1, "check failure rules     -- no FailureRule blocks g on I", "code"),
    (0, "", "blank"),
    (0, "inductive HasType (Sigma) : Plan -> Interface -> List Interface -> Prop", "keyword"),
    (1, "| atom g  : g in Sigma, g.input = I, admissible I g", "code"),
    (1, "              => HasType (atom g) I g.outputs", "code"),
    (1, "| seq p q : HasType p I Js, (forall J in Js, HasType q J Ks)", "code"),
    (1, "              => HasType (seq p q) I Ks", "code"),
    (1, "| guard   : lock in I.locks, HasType p I Os", "code"),
    (1, "              => HasType (guard lock p) I Os", "code"),
    (0, "", "blank"),
    (0, "-- Negative typing: failure IS a derivation, not absence of one", "comment"),
    (0, "structure FailureRule where", "keyword"),
    (1, "onInput : Interface -> Bool    -- when does this rule fire?", "code"),
    (1, "blocks  : String -> Bool       -- which generators are blocked?", "code"),
    (1, "reason  : RejectReason         -- paradigmMismatch | missingPremise | ...", "code"),
    (0, "", "blank"),
    (0, "-- 7 failure rules: FD1 (Fintype blocks symmetrization) ... FD7", "comment"),
    (0, "", "blank"),

    # Layer 4: Theory growth
    (0, "-- Layer 4: Structured ignorance and theory extension", "section"),
    (0, "", "blank"),
    (0, "structure GapSpec where        -- what the theory needs but doesn't have", "keyword"),
    (1, "source  : Interface            -- the untypeable obligation", "code"),
    (1, "needed  : Interface            -- what would solve it", "code"),
    (1, "because : RejectReason         -- why it failed", "code"),
    (0, "", "blank"),
    (0, "structure Theory where", "keyword"),
    (1, "generators : List Generator", "code"),
    (1, "failures   : List FailureRule", "code"),
    (1, "gaps       : List GapSpec      -- the theory's articulated ignorance", "code"),
    (0, "", "blank"),
    (0, "theorem extension_sound :", "theorem"),
    (1, "g.input = gap.source, g.outputs = [gap.needed], admissible gap.source g", "code"),
    (1, "=> HasType (Sigma + g) (atom g) gap.source [gap.needed]", "code"),
    (0, "", "blank"),
    (0, "-- Adding a generator that solves a gap yields a well-typed plan.", "comment"),
    (0, "-- The gap tells you what you don't know. Precisely.", "comment"),
    (0, "", "blank"),

    # Results
    (0, "-- Machine-checked results (0 sorry, 27/27 tests pass)", "section"),
    (0, "", "blank"),
    (0, "theorem corpus_relative_completeness :", "theorem"),
    (1, "all 6 major pipelines (PAC, DST, Online, Gold, Separation, Bayes)", "code"),
    (1, "type-check under fltTheory", "code"),
    (0, "", "blank"),
    (0, "theorem no_universal_generator :", "theorem"),
    (1, "no generator in fltTheory spans PAC + Online + Gold simultaneously", "code"),
    (0, "", "blank"),
    (0, "theorem nt1_cross_paradigm_impossible :", "theorem"),
    (1, "seq TreePotential UCToPAC is provably ill-typed at composition level", "code"),
]

# Style -> (font color, background, is_bold)
STYLES = {
    "section":  ("#000000", "#e8e8e8", True),
    "keyword":  ("#000000", None, True),
    "type":     ("#333333", None, False),
    "code":     ("#333333", None, False),
    "comment":  ("#666666", None, False),
    "theorem":  ("#000000", "#f0f0f0", True),
    "blank":    ("#000000", None, False),
}


def main():
    plt.rcParams['font.family'] = 'monospace'
    plt.rcParams['font.monospace'] = ['DejaVu Sans Mono', 'Courier New']

    line_h = 0.45
    indent_w = 1.5
    fig_h = len(LINES) * line_h + 3
    fig_w = 28

    fig, ax = plt.subplots(1, 1, figsize=(fig_w, fig_h))
    ax.set_title("TPG_FLT: Typed Proof Operad (1,170 LOC, 0 sorry)",
                 fontsize=18, fontfamily='serif', fontweight='bold', pad=15)
    ax.axis('off')

    x_base = 0.5
    y_top = len(LINES) * line_h + 0.5

    for i, (indent, text, style) in enumerate(LINES):
        y = y_top - i * line_h
        x = x_base + indent * indent_w
        color, bg, bold = STYLES[style]

        if style == "blank":
            continue

        # Background highlight for section headers and theorems
        if bg:
            ax.axhspan(y - line_h * 0.4, y + line_h * 0.4,
                       color=bg, zorder=0)

        weight = 'bold' if bold else 'normal'
        fs = 11 if style == "comment" else 12

        ax.text(x, y, text, fontsize=fs, fontfamily='monospace',
                fontweight=weight, color=color, va='center', zorder=2)

    ax.set_xlim(-0.5, fig_w)
    ax.set_ylim(-0.5, y_top + 1.5)
    plt.tight_layout()
    plt.savefig(os.path.join(ASSETS, 'world_model_layers.png'),
                dpi=150, bbox_inches='tight',
                facecolor='white', edgecolor='none')
    plt.close()
    print(f"Saved: {os.path.join(ASSETS, 'world_model_layers.png')}")


if __name__ == "__main__":
    main()
