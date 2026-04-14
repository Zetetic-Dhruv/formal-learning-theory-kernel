# Discovery URS: Comparator CI + Verification Pipeline

## A — Axioms (Identity)

### A1: Task Identity

**PROBLEM:** Build the gold-standard verification pipeline for `formal-learning-theory-kernel`: generate `Challenge.lean` + `Solution.lean` from the premise documents, wire `comparator` + `lean4checker` into GitHub Actions CI, and store verification artifacts in `test/`.

**WHY:** The Lean formalization community (per Lean Language Reference, Section "Validating a Lean Proof") defines three escalating trust levels:
1. Blue check marks (lake build succeeds) — DONE
2. `#print axioms` + `lean4checker --fresh` — DONE (locally, not in CI)
3. **Comparator** (sandbox + independent kernel replay + challenge-file matching) — NOT YET DONE

AI-assisted code is treated on par with malicious code by community policy. Level 3 is required for credibility. The kernel has already passed Level 2 locally — this task promotes it to Level 3 in CI.

### A2: Scope Constraints

- Do NOT modify any `.lean` proof file in `FLT_Proofs/`
- The Challenge file contains STATEMENTS ONLY (theorem signatures with `sorry`)
- The Solution file imports the kernel and provides the proofs by delegation
- CI runs on GitHub Actions Linux runners (where `landrun` works)
- The `merely-true` PR (https://github.com/merely-true/merely-true/pull/36) is separate — do not conflate

### A3: Repository Location

```
Repo: github.com/Zetetic-Dhruv/formal-learning-theory-kernel
Branch: main (current sorry-free state)
New branch: verification-pipeline (for this work)
Toolchain: leanprover/lean4:v4.29.0-rc6
```

---

## M — Mechanisms

### M1: Challenge.lean Generation

**Source:** `premise/final.json` → `theorem_names` list + kernel `.lean` files

**Method:** For each public theorem in the kernel's theorem index, extract the STATEMENT (signature + type) and emit it with `sorry` as the proof body. The Challenge file defines what the kernel CLAIMS to prove.

**Key theorems to include (from PAC.lean + Compression.lean + others):**

```
-- From Theorem/PAC.lean (15 public theorems):
fundamental_theorem
fundamental_vc_compression
fundamental_rademacher
vc_characterization
pac_imp_vcdim_finite
vcdim_finite_imp_pac
sauer_shelah
sauer_shelah_quantitative
pac_lower_bound
pac_sample_complexity_sandwich
sample_complexity_upper_of_pac_witness
vcdim_univ_infinite
nfl_theorem_infinite
nfl_fixed_sample
occam_algorithm

-- From Complexity/Compression.lean (6 public theorems):
vcdim_finite_imp_proper_finite_support_learner
roundtrip_blockHyp_eq_rep
vcdim_finite_imp_compression_with_info
compress_with_info_injective_on_labelings
compression_with_info_imp_vcdim_finite
fundamental_vc_compression_with_info

-- From other files (key separations, characterizations):
online_imp_pac
littlestone_characterization
gold_theorem
mwu_approx_minimax
finite_support_vc_approx
sauer_shelah (Bridge.lean version if different)
```

**Format:**
```lean
-- Challenge.lean: theorem statements only
import FLT_Proofs.Theorem.PAC
import FLT_Proofs.Complexity.Compression

theorem challenge_fundamental_theorem ... := sorry
theorem challenge_vc_characterization ... := sorry
-- etc.
```

Actually, comparator's design is simpler: Challenge.lean contains the theorem with `sorry`, Solution.lean contains the same theorem with a real proof (or delegates to the kernel). Both must have the SAME statement.

### M2: Solution.lean Generation

**Method:** For each theorem in Challenge.lean, provide the proof by importing the kernel module and using `exact kernel_theorem_name`.

```lean
-- Solution.lean: proofs by delegation
import FLT_Proofs.Theorem.PAC
import FLT_Proofs.Complexity.Compression

theorem challenge_fundamental_theorem ... := fundamental_theorem ...
theorem challenge_vc_characterization ... := vc_characterization ...
-- etc.
```

### M3: Comparator CI Workflow

**Dependencies (Linux-only):**
- `landrun` — https://github.com/Zouuup/landrun (Linux namespace sandbox)
- `lean4export` — https://github.com/leanprover/lean4export (version-matched to v4.29.0-rc6)
- `comparator` — https://github.com/leanprover/comparator
- `nanoda` (optional) — https://github.com/ammkrn/nanoda_lib/

**Config file (`comparator/config.json`):**
```json
{
  "challenge_module": "Challenge",
  "solution_module": "Solution",
  "theorem_names": ["challenge_fundamental_theorem", ...],
  "permitted_axioms": ["propext", "Quot.sound", "Classical.choice"],
  "enable_nanoda": false
}
```

**CI workflow (`.github/workflows/comparator.yml`):**
1. Checkout repo
2. Install Lean via elan
3. Install landrun, lean4export, comparator (from source or pre-built)
4. `lake build` (build the kernel)
5. `lean4checker --fresh` on key modules (already know this works)
6. Build Challenge.lean and Solution.lean
7. Run `comparator config.json`
8. Store results in `test/comparator_results.txt`
9. Upload as CI artifact

### M4: lean4checker CI Integration

Simpler than comparator — just needs the kernel built and lean4checker binary.

**CI step:**
```yaml
- name: lean4checker verification
  run: |
    for module in FLT_Proofs.Theorem.PAC FLT_Proofs.Complexity.Compression ...; do
      lean4checker --fresh $module
    done
```

### M5: Verification Artifacts in test/

Store all results:
```
test/
  ARTIFACT_CHECKLIST.md        (existing)
  comparator_results.txt       (new — comparator output)
  lean4checker_results.txt     (new — lean4checker output)
  print_axioms_results.txt     (new — #print axioms output)
  verification_summary.json    (new — machine-readable summary)
```

---

## R — Representations

### R1: Current Kernel State (all KK — established facts)

**Repository:** `github.com/Zetetic-Dhruv/formal-learning-theory-kernel`
**Latest commit:** `fe1504b` (Update premise/final.json to v3.2)
**Build:** 3027 jobs, 0 errors, 0 sorrys, 0 warnings
**Toolchain:** `leanprover/lean4:v4.29.0-rc6`

**Metrics:**
- 53 Lean files, 21,728 LOC
- 354 theorems (248 public, 106 private), 257 definitions, 59 structures
- 0 sorry, 0 axiom, 0 native_decide, 0 unsafe, 0 implemented_by
- 7 set_option (all maxHeartbeats — safe)

**Key theorems (the crown jewels to verify):**
| Theorem | File | What it proves |
|---------|------|---------------|
| `fundamental_theorem` | Theorem/PAC.lean:293 | 5-way equivalence (PAC + VC + compression + Rademacher + growth) |
| `fundamental_vc_compression_with_info` | Compression.lean:1321 | VCDim < top iff compression with side info (Moran-Yehudayoff) |
| `vc_characterization` | Theorem/PAC.lean:127 | PAC iff VCDim < top |
| `sauer_shelah` | Theorem/PAC.lean:153 | Sauer-Shelah-Perles lemma |
| `mwu_approx_minimax` | PureMath/ApproxMinimax.lean:597 | MWU approximate minimax |
| `finite_support_vc_approx` | Complexity/FiniteSupportUC.lean:91 | Finite-support VC approximation |
| `roundtrip_blockHyp_eq_rep` | Compression.lean:462 | Generic encode/decode roundtrip |
| `online_imp_pac` | Theorem/Separation.lean | Online implies PAC |

**Verification already completed (locally, not in CI):**
- `lean4checker --fresh` on 13 modules — all exit 0
- `#print axioms` on 15 theorems — all `[propext, Classical.choice, Quot.sound]` only
- grep for sorry/axiom/native_decide/unsafe/etc — all clean

### R2: Premise Documents (the methodology)

**`premise/origin.json`** (March 18) — pre-proof type architecture:
- 139 concept nodes across 7 layers (L0-L7)
- 5 paradigm joints (PAC/Online, PAC/Gold, Online/Gold, FiniteDim/OrdinalDim, Frequentist/Bayesian)
- 7 break points (BP1-BP7) identified before any proof
- 5 compilation constraints predicted
- Initial state: 2,912 LOC, 69 sorrys, 0 errors

**`premise/final.json`** (April 14, v3.2) — post-proof state:
- 354 theorems, 0 sorrys
- All break points confirmed or dissolved
- 3 versions of new mathematics discovered during proof search
- Verification section documents lean4checker + #print axioms results

**`world_model/proof_world_model.json`** — 21 extracted metaprograms (MP1-MP21):
- Each is a reusable tactic composition pattern (TacticM DAG)
- Extracted from actual proof sequences in the kernel
- Used to guide agent proof search

**The pipeline:** `origin.json` (type the domain) → proof search (AI closes sorrys) → `final.json` (record results) → world model (extract reusable patterns). The premise IS the Challenge file source.

### R3: Existing CI (.github/workflows/)

- `ci.yml` — lake build + zero-sorry enforcement + metrics verification
- `blueprint.yml` — LaTeX PDF build and gh-pages deployment
- `docs.yml` — Lean4 API doc generation

The new `comparator.yml` and `lean4checker.yml` will be ADDED, not replace existing CI.

### R4: Community Context

**Lean Zulip thread (AI authored projects > De Giorgi-Nash-Moser, April 14 2026):**
- Mathlib will NOT accept AI-assisted code regardless of quality (community policy)
- `merely-true` (github.com/merely-true/merely-true) is the accepted landing spot
- Multiple leaders (Buzzard, Gouëzel, Avigad, Kim Morrison) support AI-assisted formalization
- The key missing piece: verification infrastructure. Armstrong's DGNM project has 739 warnings and no independent verification. This kernel has 0 warnings, lean4checker passes, and will have comparator.
- PR #36 submitted to merely-true (pending toolchain update from v4.24.0 to v4.29.0+)

**Prof. Siddhartha Gadgil's response:**
- Pointed to comparator as the gold standard
- Won't review the math (not his area)
- Pointed to merely-true as the correct venue

**The methodology paper angle:** The premise-driven pipeline (origin.json → proof search → final.json → comparator) IS the methodology contribution. The paper is about this pipeline, not just the theorems.

### R5: Key Files for the Next Session to Read

```
/formal-learning-theory-kernel/
  premise/origin.json                    — pre-proof type architecture
  premise/final.json                     — post-proof state (v3.2, sorry-free)
  premise/URS_comparator_CI.md           — THIS FILE
  world_model/proof_world_model.json     — 21 metaprograms
  assets/premise_blueprint.yaml          — the method abstracted
  test/ARTIFACT_CHECKLIST.md             — verification checklist
  .github/workflows/ci.yml              — existing CI
  FLT_Proofs/Theorem/PAC.lean           — fundamental theorem (lines 293-329)
  FLT_Proofs/Complexity/Compression.lean — compression theorem
  README.md (Section XI: Methodology)   — the 5-level method description
```

---

## T — Traces

### gamma-ledger (discoveries from Session 10-11)

| # | Discovery | Evidence |
|---|-----------|---------|
| gamma1 | Moran-Yehudayoff compression theorem is sorry-free | lean4checker --fresh exit 0 on Compression.lean |
| gamma2 | The roundtrip (encode then decode = identity) requires FACTORED helpers, not inline proof | Agent D failed inline (65 LOC, 2 errors); Dhruv's factored patch (7 helpers) succeeded |
| gamma3 | `dsimp only [localLet]` works on GOALS but NOT hypotheses | Confirmed empirically; fix: unfold on goal first, then intro |
| gamma4 | `if_congr` bridges Decidable instance mismatches in if-rewrites | Used in Phase 2 sum rewriting |
| gamma5 | `convert ... using 3` proves vc_result.choose = mkReps definitionally | Pipeline shares Exists.choose chain |
| gamma6 | The entire kernel passes lean4checker --fresh on all 13 modules | Ran locally, all exit 0 |
| gamma7 | #print axioms on 15 theorems: all [propext, Classical.choice, Quot.sound] only | No sorry, no trustCompiler, no custom axioms |
| gamma8 | 149 lint warnings cleaned to 0 via 5 parallel agents | Symmetrization (46), Generalization (29), Rademacher (23), Extended (22), 8 small files |
| gamma9 | `sorry` inside `/-...-/` block comments triggers CI grep regex | Fixed by replacing with `pending_further_proof` |
| gamma10 | fundamental_theorem conjunct 2 updated from CompressionScheme to CompressionSchemeWithInfo0 | PAC.lean:298, delegates to fundamental_vc_compression_with_info |
| gamma11 | Kernel synced to merely-true as PR #36 (53 files, 22k LOC, pending toolchain update) | github.com/merely-true/merely-true/pull/36 |
| gamma12 | The premise documents (origin.json + final.json) ARE the Challenge file source | origin defines the claims, final records the state, comparator verifies the match |

### Gamma-ledger (inquiry actions)

| # | Action | Outcome |
|---|--------|---------|
| Gamma1 | Agent C: close hmajor via MWU+VC-approx | Partial success (helper + pipeline), failed roundtrip |
| Gamma2 | Agent D: inline roundtrip + universe fix | Universe fix correct, roundtrip had 2 bugs |
| Gamma3 | Agent E: apply Dhruv's factored patch | SUCCESS — 0 sorrys, 0 errors |
| Gamma4 | 5 parallel lint agents | 149 → 0 warnings |
| Gamma5 | Red-team: grep + #print axioms + lean4checker | Kernel is cryptographically clean |
| Gamma6 | Kernel sync to github (3 commits) | Pushed to main, CI passes |
| Gamma7 | merely-true PR #36 | Submitted, pending toolchain update |

---

## KK/KU Partition

### KK — Established

1. The kernel builds: 0 sorrys, 0 errors, 0 warnings (CI passes)
2. lean4checker --fresh passes on all 13 key modules (locally verified)
3. #print axioms: all theorems use only the 3 standard axioms
4. No dangerous constructs (axiom, native_decide, unsafe, implemented_by, etc.)
5. premise/final.json is up to date (v3.2)
6. merely-true PR #36 is submitted
7. comparator exists at github.com/leanprover/comparator
8. landrun is Linux-only (requires GitHub Actions runner)
9. lean4export must be version-matched to v4.29.0-rc6
10. The premise pipeline (origin → search → final) naturally generates Challenge/Solution files

### KU — Open (tasks for next session)

1. **KU1: Generate Challenge.lean** — extract all public theorem statements from kernel, emit with `sorry`. Source: premise/final.json theorem list + grep of kernel files.
2. **KU2: Generate Solution.lean** — for each Challenge theorem, delegate to kernel proof via `exact`.
3. **KU3: Write comparator config.json** — list theorem names, permitted axioms.
4. **KU4: Write `.github/workflows/lean4checker.yml`** — CI workflow that builds kernel + runs lean4checker --fresh on all modules.
5. **KU5: Write `.github/workflows/comparator.yml`** — CI workflow that installs landrun + lean4export + comparator, builds kernel, runs comparator on Challenge/Solution.
6. **KU6: Store verification artifacts in `test/`** — comparator output, lean4checker output, #print axioms output.
7. **KU7: Create `verification-pipeline` branch** — all new files on a branch, merge to main after CI passes.

### UK — Not Checked

- Whether comparator handles Mathlib-heavy dependencies gracefully (it may need the full .lake cache)
- Whether lean4export v4.29.0-rc6 binary is available or needs building from source
- Whether landrun works in GitHub Actions Ubuntu runners (should, but untested with this repo)
- Whether the Challenge/Solution format needs a separate lakefile or can share the kernel's
- Whether nanoda (alternative kernel) compiles against v4.29.0-rc6

### UU — Boundary

- Whether the comparator workflow generalizes to other AI-assisted Lean projects (it should, but the premise-to-challenge generation is specific to this methodology)
- Whether merely-true will adopt this verification infrastructure
- Whether the Lean formalization community will accept comparator-verified AI proofs as credible

---

## Measurements

### Pl (Plausibility)
- The pipeline (premise → challenge → solution → comparator) is architecturally sound. Each piece exists. The composition is untested. **Pl = TRUE** for the pipeline; **UNKNOWN** for the CI integration.

### Coh (Coherence)
- Challenge.lean is generated from the same premise that guided proof search. Solution.lean delegates to the kernel that was built from the premise. Comparator verifies the match. The pipeline is a closed loop. **Coh = TRUE**.

### Inv (Invariance)
- The pipeline survives toolchain bumps (Challenge/Solution are regenerated, comparator re-runs). It survives mathematical changes (new theorems = new Challenge entries). It survives AI model changes (the premise is human-authored, not AI-dependent). **Inv = HIGH**.

### Comp (Completeness)
- Before this task: lean4checker done locally, comparator not done. After: both in CI.
- **Comp = 0/7 KU items resolved. Target: 7/7.**

---

## Guardrails for Next Session

```
G1  NEVER run git checkout --, git restore, or any working-tree discard command.
G2  Do NOT modify any .lean file in FLT_Proofs/. The kernel is sorry-free and must stay that way.
G3  New files go in: comparator/, test/, .github/workflows/. Not in FLT_Proofs/.
G4  Build the kernel FIRST to verify it still compiles before any CI work.
G5  Test lean4checker locally before adding to CI.
G6  The Challenge.lean must contain ONLY theorem statements with sorry. No proofs.
G7  The Solution.lean must prove each Challenge theorem by delegating to the kernel.
G8  Do NOT submit to merely-true from this session. PR #36 is already open.
```
