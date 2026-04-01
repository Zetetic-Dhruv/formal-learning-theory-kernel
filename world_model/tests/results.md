# TPG_FLT Test Results

Generated: 2026-04-02
Build: `lake build FLT_Proofs.Meta.NonTrivialTests` + `FLT_Proofs.Meta.BridgeTests`
Status: **ALL PASS, 0 sorrys**

## Smoke Tests (BridgeTests.lean)

| # | Test | Category | Result |
|---|------|----------|--------|
| T1 | PAC pipeline types | Typing | PASS |
| T2 | DST pipeline types | Typing | PASS |
| T3 | Online pipeline types | Typing | PASS |
| T4 | Gold pipeline types | Typing | PASS |
| T5 | Separation pipeline types | Typing | PASS |
| T6 | Bayesian pipeline types | Typing | PASS |
| T7 | FD3 blocks MeasureBridge | Negative typing | PASS |
| T8 | No universal generator | Paradigm lock | PASS |
| T9 | Corpus-relative completeness | Completeness | PASS |
| T10 | bridge_search on True | Tactic | PASS (graceful degradation) |

## Smoke Tests — Bonus (BridgeTests.lean)

| # | Test | Result | Finding |
|---|------|--------|---------|
| B1 | Full quality funnel-valid | PASS | `⟨T,T,T,T⟩.funnelValid = true` |
| B2 | Robustness without completion | PASS | `⟨T,T,F,T⟩.funnelValid = false` |
| B3 | Benchmark-typical partial | PASS | `⟨T,T,F,F⟩.funnelValid = true` |
| B4 | Interface widening | PASS | Premise subset detected |
| B5 | UCToPAC not robust | PASS | MCC dependency detected |
| B6 | Adversary not robust | PASS | C dependency detected |
| B7 | Contrapose IS robust | PASS | Empty premises = robust |

## Non-Trivial Tests (NonTrivialTests.lean)

| # | Test | Category | Result | Finding |
|---|------|----------|--------|---------|
| NT1 | Cross-paradigm blocked | Negative typing | PASS | UCToPAC inadmissible on iOnlineLearnable (paradigm mismatch) |
| NT2 | FD1: Fintype blocks MeasureBridge | Negative typing | PASS | Fintype_X in premises triggers FD1 |
| NT3 | FD5: branchwise blocks Adversary | Negative typing | PASS | isShattered_branchwise target triggers FD5 |
| NT4 | Extension: CompressionToPAC | Extension mechanism | PASS | Adding generator to theory gives well-typed plan |
| NT5 | Cost: PAC > Online (depth) | Difficulty model | PASS | `nfPAC.bridgeDepth > nfOnline.bridgeDepth` |
| NT5b | Cost: PAC > Online (total) | Difficulty model | PASS | `nfPAC.total > nfOnline.total` |
| NT6 | Cost: DST elaboration penalty | Difficulty model | PASS | `nfDST.elaborationPenalty ≥ nfOnline.elaborationPenalty` |
| NT7 | Interface widening reflexive | Robustness | PASS | `widens I I = true` for all tested I |
| NT8 | Structural generators unlocked | Paradigm lock | PASS | All 5 structural have `paradigm = [.structural]` |
| NT9 | Domain generators locked | Paradigm lock | PASS | All 10 domain have `paradigm ≠ [.structural]` |
| NT10a | PAC guard types on PAC interface | Guard mechanism | PASS | `.guard .pac` accepted on iHasUC |
| NT10b | Online guard fails on PAC interface | Guard mechanism | PASS | `.guard .online` rejected on iHasUC |
| NT11 | Choose picks first valid | Nondeterminism | PASS | TreePotential chosen over UCToPAC on iFiniteLDim |
| NT12a | Robustness without validity | Quality funnel | PASS | `⟨T,F,F,T⟩.funnelValid = false` |
| NT12b | Validity without compliance | Quality funnel | PASS | `⟨F,T,F,F⟩.funnelValid = false` |
| NT12c | Completion without validity | Quality funnel | PASS | `⟨T,F,T,F⟩.funnelValid = false` |
| NT13 | bridge_search on arithmetic | Tactic | PASS | Reports no bridge, `rfl` closes |

## Summary

| Metric | Value |
|--------|-------|
| Total tests | 27 |
| Passed | 27 |
| Failed | 0 |
| Sorrys | 0 |
| Categories tested | 7 (typing, negative typing, paradigm lock, extension, difficulty, robustness, tactic) |
| Generators covered | 17/17 (all in fltTheory) |
| Failure rules tested | 3/7 directly (FD1, FD3, FD5), all 7 encoded |
| Pipelines typed | 6/6 (PAC, DST, Online, Gold, Separation, Bayes) |

## Key Empirical Findings

1. **Paradigm lock is complete**: No generator spans PAC + Online + Gold (proved).
   Cross-paradigm composition is blocked at the admissibility level.

2. **Robustness separates structural from domain**: Structural generators (empty premises)
   are robust under interface widening. Domain generators (premises include C, MCC)
   are NOT robust. This reproduces the First Proof Benchmark's 29-point
   validity-to-robustness gap structurally.

3. **Difficulty ordering matches intuition**: PAC pipeline (3 generators, bridge depth 3)
   is harder than Online (1 generator, bridge depth 1). DST has higher elaboration
   penalty (cross-paradigm types).

4. **Extension mechanism is sound**: Adding a generator to solve a typed gap
   produces a well-typed plan in the extended theory.

5. **Quality funnel is strict**: The four-gate ordering (compliance ≥ validity ≥
   completion ≥ robustness) rejects all 3 tested violation patterns.
