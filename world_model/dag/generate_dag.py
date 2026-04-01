#!/usr/bin/env python3
"""
Generate the premise DAG for the proof operad's generator layer.

Reads generator definitions from ProofOperadInstances.lean (or hardcoded below),
builds the interface-level dependency graph, and outputs JSON.

Usage:
    python3 generate_dag.py > generator_dag.json
"""

import json
from collections import defaultdict

# Generators: name -> (level, input_interface, output_interfaces, paradigm)
GENERATORS = {
    # Structural combinators
    "Contrapose":           ("structural", "Goal", ["Contradiction"], ["structural"]),
    "Extensionalize":       ("structural", "Goal", ["Goal", "Goal"], ["structural"]),
    "CaseSplit":            ("structural", "Goal", ["Goal", "Goal"], ["structural"]),
    "CalcChain":            ("structural", "Goal", ["Goal"], ["structural"]),
    "WitnessRefine":        ("structural", "Goal", ["Goal", "Goal"], ["structural"]),
    # Domain generators
    "GrowthConstruction":   ("domain", "FiniteVCDim", ["GrowthBound"], ["pac"]),
    "MeasureBridge":        ("domain", "GrowthBound", ["HasUC"], ["pac"]),
    "UCToPAC":              ("domain", "HasUC", ["PACLearnable"], ["pac"]),
    "TreePotential":        ("domain", "FiniteLDim", ["OnlineLearnable"], ["online"]),
    "Adversary":            ("domain", "FiniteLDim", ["AdversaryBound"], ["online"]),
    "Locking":              ("domain", "EXLearnable", ["Contradiction"], ["gold"]),
    "AnalyticProjection":   ("domain", "BorelParam", ["AnalyticBadEvent"], ["dst"]),
    "CompactApproximation": ("domain", "AnalyticBadEvent", ["NullMeasBadEvent"], ["dst"]),
    "WitnessSeparation":    ("domain", "MeasurableHyps", ["WBVCMeasTarget", "NotKrappWirth"], ["separation"]),
    "ComponentMeasurability": ("domain", "Goal", ["Goal"], ["pac", "separation"]),
    "RectangleDecomposition": ("domain", "Goal", ["Goal"], ["pac", "structural"]),
    "JensenChain":          ("domain", "PerHypBound", ["PACBayes"], ["bayes"]),
}

# Interfaces: name -> (paradigm_locks, premises, target_tag)
INTERFACES = {
    "FiniteVCDim":      (["pac"], ["C", "hC_vcdim", "MeasurableConceptClass"], "VCDim_lt_top"),
    "GrowthBound":      (["pac"], ["C", "hC_vcdim", "MeasurableConceptClass"], "GrowthFunction_le_poly"),
    "HasUC":            (["pac"], ["C", "MeasurableConceptClass"], "HasUniformConvergence"),
    "PACLearnable":     (["pac"], ["C"], "PACLearnable"),
    "FiniteLDim":       (["online"], ["C"], "LittlestoneDim_lt_top"),
    "OnlineLearnable":  (["online"], ["C"], "OnlineLearnable"),
    "AdversaryBound":   (["online"], ["C", "T"], "mistakes_ge_ldim"),
    "EXLearnable":      (["gold"], ["C"], "EXLearnable"),
    "BorelParam":       (["dst", "pac"], ["C", "e", "he"], "Measurable_eval"),
    "AnalyticBadEvent": (["dst"], ["C"], "AnalyticSet_badEvent"),
    "NullMeasBadEvent": (["dst", "pac"], ["C"], "NullMeasurableSet_badEvent"),
    "PerHypBound":      (["bayes"], ["P", "hs"], "per_hyp_tail_bound"),
    "PACBayes":         (["bayes"], ["P", "Q"], "pac_bayes_bound"),
    "MeasurableHyps":   (["separation"], ["C"], "MeasurableHypotheses"),
    "WBVCMeasTarget":   (["separation", "pac"], ["C"], "WellBehavedVCMeasTarget"),
    "NotKrappWirth":    (["separation"], ["C"], "not_KrappWirthWellBehaved"),
    "Goal":             (["structural"], [], "any"),
    "Contradiction":    (["structural"], [], "False"),
}

# Failure diagnostics
FAILURES = [
    {"id": "FD1", "name": "Fintype blocks symmetrization",
     "trigger": "Fintype_X in premises", "blocks": "MeasureBridge",
     "reason": "forbiddenInstance:Fintype_X"},
    {"id": "FD2", "name": "Uncountable blocks union bound",
     "trigger": "Fintype_C and Countable_C absent", "blocks": "UnionBound",
     "reason": "forbiddenInstance:uncountable_C"},
    {"id": "FD3", "name": "Missing MeasurableConceptClass",
     "trigger": "MeasurableConceptClass absent", "blocks": "MeasureBridge",
     "reason": "missingPremise:MeasurableConceptClass"},
    {"id": "FD4", "name": "Quantifier order",
     "trigger": "target=forall_D_exists_m0", "blocks": "UCToPAC",
     "reason": "elaborationDeadEnd:quantifier_order"},
    {"id": "FD5", "name": "Branchwise Littlestone",
     "trigger": "target=isShattered_branchwise", "blocks": "Adversary",
     "reason": "forbiddenInstance:branchwise_shattering"},
    {"id": "FD6", "name": "Existential Dm",
     "trigger": "target=PACLearnable_exists_Dm", "blocks": "UCToPAC",
     "reason": "nonconstructiveSelection"},
    {"id": "FD7", "name": "Nonconstructive selection",
     "trigger": "always", "blocks": "ClassicalChooseUncountable",
     "reason": "nonconstructiveSelection"},
]

# Named composition pipelines
PIPELINES = {
    "PAC_characterization": ["GrowthConstruction", "MeasureBridge", "UCToPAC"],
    "DST_bridge": ["AnalyticProjection", "CompactApproximation"],
    "Online_characterization": ["TreePotential"],
    "Gold_impossibility": ["Locking"],
    "Separation": ["WitnessSeparation"],
    "PAC_Bayes": ["JensenChain"],
}


def build_dag():
    """Build the premise DAG: edges from generator outputs to consumers."""
    # Map: interface_name -> list of generators that PRODUCE it
    producers = defaultdict(list)
    for gname, (level, inp, outs, paradigm) in GENERATORS.items():
        for out in outs:
            producers[out].append(gname)

    # Map: interface_name -> list of generators that CONSUME it
    consumers = defaultdict(list)
    for gname, (level, inp, outs, paradigm) in GENERATORS.items():
        consumers[inp].append(gname)

    # Edges: producer -> consumer (through shared interface)
    edges = []
    for iface in INTERFACES:
        for prod in producers.get(iface, []):
            for cons in consumers.get(iface, []):
                edges.append({
                    "from": prod,
                    "to": cons,
                    "interface": iface,
                    "interface_locks": INTERFACES[iface][0],
                })

    return edges


def main():
    edges = build_dag()

    dag = {
        "metadata": {
            "name": "FLT_proof_operad_premise_DAG",
            "description": "Machine-generated premise DAG for the generator layer of TPG_FLT. "
                           "Edges represent interface-mediated dependencies: generator A produces "
                           "interface I, generator B consumes interface I.",
            "generated_by": "generate_dag.py",
            "generator_count": len(GENERATORS),
            "interface_count": len(INTERFACES),
            "edge_count": len(edges),
            "pipeline_count": len(PIPELINES),
            "failure_count": len(FAILURES),
        },
        "generators": {
            name: {
                "level": level,
                "input": inp,
                "outputs": outs,
                "paradigm": paradigm,
            }
            for name, (level, inp, outs, paradigm) in GENERATORS.items()
        },
        "interfaces": {
            name: {
                "locks": locks,
                "premises": premises,
                "target_tag": tag,
            }
            for name, (locks, premises, tag) in INTERFACES.items()
        },
        "edges": edges,
        "pipelines": PIPELINES,
        "failures": FAILURES,
    }

    print(json.dumps(dag, indent=2))


if __name__ == "__main__":
    main()
