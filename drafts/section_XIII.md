# Section XIII -- FINAL DRAFT

---

## XIII. Building

```bash
lake build              # Kernel (43 files, ~2 min cached, ~20 min clean)
lake build WorldModel   # Proof operad (8 files, <2 min)
```

Lean `v4.29.0-rc6` | Mathlib4 from `master` | See [`test/ARTIFACT_CHECKLIST.md`](test/ARTIFACT_CHECKLIST.md) for full reproducibility details.

Figures:

```bash
python3 scripts/generate_hypergraph.py   # Outputs to assets/hypergraph_*.png
bash scripts/generate_theorem_index.sh   # Outputs to drafts/theorem_index.md
bash scripts/metrics.sh                  # Canonical metrics (JSON)
```

Requires `elan` for Lean4. Figure generation requires Python 3 with `matplotlib`, `numpy`, `scipy`.
