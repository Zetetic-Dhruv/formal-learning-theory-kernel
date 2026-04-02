# Section XI -- FINAL DRAFT

---

## Part IV: Apparatus

## XI. Methodology

### The method at five levels

This kernel was built in 9 days (March 18-25 for proof discovery, March 28-30 for measurability infrastructure and new mathematics) by a single human using Claude Opus 4.6 (Anthropic) via Claude Code. The method operates at five levels. Each level has a distinct function.

**Level 1: Premise design.** The human writes a typed premise: a hierarchical DAG of type definitions with placeholder proofs (`sorry`) organized across dependency layers (L0-L7). The premise encodes the mathematical structure of the target theory before any proof is attempted. The 42 concept nodes, 8 dependency layers, and 67 proof obligations of the learning theory premise were derived from an existing textbook and concept graph (`premise/origin.json`). The premise compiles. The types are checked. The proofs are empty.

<!-- FIGURE: methodology_process.svg
     Style: black/white, Times New Roman, old school academic
     Vertical flow diagram showing the 5 levels as stacked phases:
     Level 1 (Premise Design) -> Level 2 (Proof Search) -> Level 3 (Failure Diagnosis)
     -> Level 4 (Refactoring) -> Level 5 (World Model)
     Left column: HUMAN actions at each level
     Right column: AI actions at each level
     Feedback arrows: Level 3 feeds back to Level 2, Level 4 feeds back to Level 1
     The ablation split shown as a fork at Level 2: "with framework" vs "without"
     Caption: "Five-level methodology. Human provides structure; AI provides execution."
-->

**Level 2: Proof search.** The AI operates in bypass mode: given a `sorry` and its type signature, it searches for tactic sequences that close the goal. The human does not write proofs. The human selects which `sorry` to attack, chooses the proof strategy when multiple routes exist, and redirects the AI when it enters a failure mode. The AI writes tactics, navigates Mathlib, and executes the mechanical work of elaboration and type-checking.

**Level 3: Failure diagnosis.** When the AI fails, the failure is classified. Six failure modes were observed:

| Failure mode | Description | Resolution |
|-------------|-------------|------------|
| Re-derivation waste | Agent re-derives a known dead end (e.g., direct union bound gives 2^{2m}) | Redirect with explicit prohibition |
| Measurability spiral | AI hits unknown measurability requirement, proposes increasingly complex workarounds | Surface the mathematical question, provide evidence |
| Content-dropping | AI proposes "simplifications" that weaken the mathematical result | Reject via completeness constraint |
| Context exhaustion | Agent consumes token budget on deliberation before writing the proof | Split research agents from proof-writing agents |
| Instance synthesis failure | AI patches symptoms (wrong API) instead of diagnosing root cause | Provide private evidence after N failed attempts |
| Concurrent file conflict | Parallel agents overwrite each other's work | Git worktree isolation per agent |

**Level 4: Refactoring for discovery.** After proof search closes the initial `sorry` count, the human refactors the kernel: extracts shared infrastructure into typeclasses, renames modules, reorganizes dependency layers. This is Phase 2 of the premise design blueprint (`assets/premise_blueprint.yaml`). The refactoring is engineering. The discovery is not. The measurability typeclass extraction (Section V) was an engineering cleanup that produced three original mathematical results and five precisely-stated open questions. The discovery was not planned. It emerged from the type obligations that refactoring exposed.

**Level 5: World model construction.** The proof methods used during search are extracted, classified, and formalized into a typed proof operad (Section VIII). The operad is the method reflecting on itself: which proof strategies worked, which failed, and why the failures are paradigm-locked. The world model is both a record of this project and a routing table for future proof search in the same domain.

### The ablation

In an autonomous session without the framework, the AI was given the same type-checked premise (67 placeholder `sorry` statements) and instructed to close all proofs. The result: the `sorry` count grew from 67 to 187. The AI added 120 new `sorry` statements. Each plausible-looking tactic that failed to elaborate was replaced by a new `sorry`, and each `sorry` generated downstream obligations that themselves required `sorry`. The last errorless build state contained 8 correctly proved theorems and 12 vacuously true statements -- all in computation files, the easiest targets. After this point, no build succeeded.

With the framework, 65 of 67 were closed. The remaining 2 are blocked by constructions absent from Mathlib (Moran-Yehudayoff 2016, BHMZ STOC 2021), not by AI capability. The measurability premise extension then produced 54 additional theorems including new mathematics, with 0 new `sorry`.

Across 14 proof tasks in the framework-guided sessions, the correlation between pre-proof articulation of unknowns and first-attempt success is exact:

| | Framework forces articulation of unknowns | No articulation |
|---|---|---|
| First-attempt success | 87.5% (7/8) | 0% (0/6) |

Every task where the AI wrote code without first stating what it did not know produced at least one mistake. No exceptions.

### What the human contributes

The framework forces the AI to articulate what it does not know before writing any code. The human then intervenes to resolve the hard unknowns -- all the way from finding the right Mathlib API name to providing a complete proof sketch for the Borel-analytic separation. Three mechanisms:

**1. Resolving unknowns before proof.** Before each proof task, the AI states what it needs but does not have. The human resolves these -- by Mathlib search, by mathematical argument, or by providing private evidence the AI cannot access. When the Interpolation proof was specified, three unknowns were identified (router parameter space, file location, patchEval framing) and resolved in advance. The agent closed the proof in one attempt. Without that resolution, the agent would have guessed wrong on at least one entry and spiraled.

**2. Architectural corrections at type level.** The proof operad was initially designed with generators typed as `input -> output`. The correct typing is `input -> List output` because one goal maps to many subgoals -- this is an operad, not a category. The correction changed the entire `Generator` structure and prevented a type error that would have propagated through all four construction phases. These corrections operate at the type level. They cannot be made by an agent that does not understand the mathematical objects being formalized.

**3. Directing discovery.** The instruction to build the `VersionSpaceLearner` came with a precise mathematical argument: Kuratowski-Ryll-Nardzewski is absent from Mathlib, therefore use countable enumeration via `Nat.find`. That framing made the proof tractable. Without it, the AI would have attempted the uncountable case, hit missing infrastructure, and either added a `sorry` or abandoned the direction.

The human never writes a proof line. The human decides which proofs to write, in what order, via what strategy, and with what preconditions resolved.

### The operational principle

The method's core mechanism is a single ordering constraint: the AI must articulate what it does not know before writing any proof, and the human resolves the difficult unknowns before the AI proceeds.

Without this ordering, the AI writes proofs against imagined infrastructure and retrofits when reality disagrees. Each retrofit generates a new `sorry`. Each `sorry` generates downstream obligations. The `sorry` count grows exponentially. This is the 67 -> 187 phenomenon.

With this ordering, each proof begins only after its unknowns have been stated and resolved -- by the AI for routine queries (Mathlib API names, type signatures), by the human for hard ones (proof strategies, missing infrastructure, mathematical arguments). The AI writes only against verified preconditions. The `sorry` count monotonically decreases.

### Comparison to existing approaches

| System | Approach | Premise source | Scale |
|--------|----------|---------------|-------|
| AlphaProof (DeepMind) | RL + Lean verifier | None (autonomous) | 4/6 IMO 2024 |
| Lean Copilot | LLM tactic suggestion | Interactive copilot | 74.2% of Mathlib steps |
| COPRA | GPT-4 + backtracking | None (in-context) | miniF2F (244 problems) |
| ReProver | Supervised + retrieval | Auto-retrieved | 51.2% Mathlib random split |
| Draft-Sketch-Prove | Informal proof -> formal sketch | Informal proof as guide | 39.3% miniF2F-test |
| **This work** | **Human premise + LLM execution** | **Typed premise (human)** | **278 theorems, 17,956 LOC** |

The existing approaches assign proof strategy to the AI (via RL, beam search, or in-context reasoning). This method assigns proof strategy to the human and tactic execution to the AI. The inversion explains the scale: no existing system has produced a coherent theory-scale kernel because no existing system delegates the type structure to a human who understands the mathematics. The tradeoff is that this method requires a human who CAN design the typed premise.

### Limitations

The method requires a human who can write a type-checked premise for the target domain. For learning theory, this took one week of reading and one day of typing. For an unfamiliar domain, the cost is higher and the risk of structural errors in the premise is the dominant failure mode.

The method has been tested across near-orthogonal domains: mathematical discovery (this kernel), empirical AI benchmarking ([First-Proof-Benchmark-Results](https://github.com/Zetetic-Dhruv/First-Proof-Benchmark-Results)), and production knowledge modeling. The premise design blueprint (`assets/premise_blueprint.yaml`) is abstracted from these applications. Whether domain-specific structural phenomena (paradigm locking, measurability bridges, definition sensitivity) recur in other mathematical domains is an open question; the method itself transfers.

The AI driver is a frontier LLM, not a specialized prover. Its Mathlib navigation works by name-guessing and type-matching, not by indexed retrieval. A specialized tool (DiscrTree-based search, as prototyped in the bridge tactic of Section VIII) would improve tactic-level efficiency without changing the method's architecture.