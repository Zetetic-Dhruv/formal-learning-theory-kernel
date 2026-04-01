# Section X — FINAL DRAFT

---

## X. The Discovery DAG

The dependency structure of the kernel is encoded in the Mermaid diagram below. Solid edges are proved dependencies. Dashed nodes are counterfactual branches: proof routes that were explored and killed. Each dead branch records a specific discovery: a definition that was provably inadequate, a proof route that was provably blocked, or a setting boundary that was provably strict.

The counterfactual branches collectively explain why the kernel has the shape it does.

```mermaid
flowchart TB
    classDef typ fill:#1e293b,stroke:#475569,color:#e2e8f0
    classDef meas fill:#1e3a5f,stroke:#3b82f6,color:#e2e8f0
    classDef infra fill:#1e3a5f,stroke:#3b82f6,color:#e2e8f0
    classDef bridge fill:#2563eb,stroke:#60a5fa,color:#fff
    classDef thm fill:#1e3a5f,stroke:#3b82f6,color:#e2e8f0
    classDef summit fill:#2563eb,stroke:#60a5fa,color:#fff
    classDef sorry fill:#7f1d1d,stroke:#dc2626,color:#fca5a5
    classDef dead fill:#374151,stroke:#6b7280,color:#9ca3af,stroke-dasharray:5 5

    CC["ConceptClass"]:::typ
    BL[BatchLearner]:::typ
    OL[OnlineLearner]:::typ
    GL[GoldLearner]:::typ

    VCD["VCDim < inf"]:::meas
    LD["LittlestoneDim < inf"]:::meas
    MCO[MindChangeOrd.]:::meas

    SS[Sauer-Shelah]:::bridge
    SYM["Symmetrization\n3,027 lines"]:::infra
    UC["Uniform Conv."]:::infra
    RAD["Rademacher"]:::infra
    NFL["NFL counting"]:::infra
    MEAS["Measurability\ntypeclasses"]:::infra
    BAB["Borel-Analytic\nBridge"]:::infra

    VCC["vc_characterization"]:::summit
    LC["littlestone_char."]:::thm
    GT["gold_theorem"]:::thm
    PB["pac_bayes"]:::thm
    BAS["Borel-analytic\nseparation"]:::thm
    INTERP["interpolation\ndescent"]:::thm
    VSM["version space\nmeasurability"]:::thm

    COMP["vcdim_finite_imp\n_compression"]:::sorry
    BHMZ["bhmz_middle\n_branch"]:::sorry

    CF1["x NFL finite X"]:::dead
    CF2["x BranchWise LDim"]:::dead
    CF3["x Direct union bound"]:::dead
    CF4["x UC without regularity"]:::dead
    CF5["x PAC existential Dm"]:::dead

    CC --> VCD & LD & MCO
    BL --> VCC
    OL --> LC
    GL --> GT

    VCD --> SS --> SYM --> UC
    UC --> VCC
    VCD --> RAD
    VCD --> COMP
    LD --> LC
    MCO --> GT

    MEAS --> BAB --> BAS
    MEAS --> INTERP
    MEAS --> VSM

    RAD --> VCC
    NFL --> VCC
    PB --> VCC

    COMP --> VCC
    BHMZ -.-> LC

    CF1 -.-> NFL
    CF2 -.-> LC
    CF3 -.-> UC
    CF4 -.-> SYM
    CF5 -.-> VCC
```

### Reading the counterfactual branches

| Dead branch | What was discovered | Effect on the kernel |
|------------|--------------------|--------------------|
| NFL for finite X | VCDim(Set.univ) = \|X\| for finite X; memorizer learns Set.univ | All NFL theorems require `[Infinite X]` |
| BranchWise Littlestone | const_true/const_false gives LDim = infinity for a 1-mistake class | `Theorem/Online.lean` defines path-wise `LTree.isShattered` |
| Direct union bound | Produces 2^{2m}, not GrowthFunction(C, 2m) | 56% of the codebase is symmetrization infrastructure |
| UC without regularity | Bad event not measurable for uncountable C | `WellBehavedVC` regularity hypothesis in every measure-theoretic theorem |
| PAC with existential Dm | Existential Dm depends on target c via memorizer | `Measure.pi` (distribution-free) in the PACLearnable definition |
