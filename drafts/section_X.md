# Section X -- FINAL DRAFT

---

## X. The Kernel at a Glance

The full dependency structure of the kernel, with proof methods overlaid as shaded regions:

![Kernel structure with proof method regions](assets/hypergraph_overview.png)

The diagram encodes 35 modules across 8 layers (L0-L7), 278 theorems, and the 6 major proof pipelines from Section VIII. Each shaded region groups the modules that participate in a single proof method. The regions do not overlap across paradigm boundaries. No proof method spans PAC, Online, and Gold simultaneously.

### Kernel summary

**PAC dominates the infrastructure.** The PAC proof pipeline spans 4 layers (L3 through L6) and wraps 8 modules. The Online and Gold pipelines span 3 layers each with 3 modules. This asymmetry is not a design choice. It reflects the mathematical fact that PAC learning requires symmetrization, concentration, exchangeability, and measurability infrastructure that Online and Gold learning do not. 56% of the kernel's codebase serves the PAC characterization.

**Measurability connects the paradigms.** The Measurability module (L4) appears inside three proof method regions: the PAC chain, the Borel-analytic bridge, and the Separation witness. It is the only module shared across regions. The measurability typeclasses (Section V) were introduced as engineering cleanup. They became the structural bridge between combinatorial learning theory and descriptive set theory.

**Online and Gold are self-contained.** The Online potential region and Gold locking region are isolated. No shared infrastructure between them, and no shared infrastructure with PAC except through the foundation layers (L0-L1). The proof methods are disjoint at the module level, not just at the tactic level.

### Per-paradigm structure

<details>
<summary><strong>PAC paradigm</strong></summary>

![PAC detail](assets/hypergraph_pac.png)

VCDimension -> Generalization -> Symmetrization -> Rademacher -> Concentration/Exchangeability -> Thm.PAC. Each step requires its own mathematical machinery (Sauer-Shelah, ghost samples, Hoeffding, NullMeasurableSet). The Separation witness region shares Measurability and Structures with the PAC chain.

</details>

<details>
<summary><strong>Online + Gold paradigms</strong></summary>

![Online + Gold detail](assets/hypergraph_online_gold.png)

Two isolated regions. Online: Littlestone -> GameInfra -> Thm.Online. Gold: MindChange -> Ordinal -> Thm.Gold. GameInfra (219 lines) is the only Online-specific infrastructure module extracted during refactoring.

</details>

<details>
<summary><strong>Descriptive set theory</strong></summary>

![DST detail](assets/hypergraph_dst.png)

The 526-line pipeline from Section IX: Choquet -> AnalyticMeas -> BorelBridge -> Thm.BorelAnalytic. Interpolation sits outside the pipeline -- a standalone result connecting to the measurability hub but not participating in any proof chain.

</details>

### Dead branches

Five proof routes were explored and killed. Each killed route shaped the kernel that remains.

| Dead branch | Discovery | Consequence |
|------------|-----------|-------------|
| NFL for finite X | VCDim(Set.univ) = \|X\|; memorizer learns Set.univ | All NFL theorems require `[Infinite X]` |
| BranchWise Littlestone | const_true/const_false gives LDim = infinity for a 1-mistake class | Path-wise `LTree.isShattered` replaces branchwise |
| Direct union bound | Produces 2^{2m}, not GrowthFunction(C, 2m) | Symmetrization infrastructure (3,027 lines) exists because this shortcut fails |
| UC without regularity | Bad event not measurable for uncountable C | `WellBehavedVC` regularity hypothesis in every measure-theoretic theorem |
| PAC with existential Dm | Existential Dm depends on target c via memorizer | `Measure.pi` (distribution-free) replaces existential construction |

The direct union bound is the most consequential dead branch. Had it worked, the symmetrization infrastructure -- ghost samples, exchangeability, double-sample measure, Rademacher complexity -- would not exist. More than half the kernel's codebase exists because one obvious proof route was provably blocked.

### Open boundary

Two theorems carry sorry:

- **Compression characterization** (forward direction): blocked by Moran-Yehudayoff 2016 construction absent from Mathlib.
- **Universal trichotomy** (middle branch): blocked by BHMZ STOC 2021 construction absent from Mathlib.

Both are extended results, not core. The PAC, Online, and Gold characterization theorems and all four separations are sorry-free.

<details>
<summary><strong>Regeneration</strong></summary>

All figures are machine-generated:

```bash
python3 scripts/generate_hypergraph.py
```

Outputs to `assets/hypergraph_*.png`. Requires `matplotlib`, `numpy`, `scipy`.

</details>
