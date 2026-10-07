#!/usr/bin/env python3
"""Check Lean's axiom reports for the public LiebThirring theorems."""

import re
import subprocess
import sys
from pathlib import Path


THEOREMS = (
    "LiebThirring.stability_of_matter",
    "LiebThirring.stability_of_matter_real",
    "LiebThirring.kinetic_lieb_thirring",
    "LiebThirring.baxter",
    "LiebThirring.kineticEnergy_schwartz",
    "LiebThirring.electron_count_lt_of_atomic_binding",
    "LiebThirring.electron_count_lt_of_atomic_weak_ground_state",
    "LiebThirring.exists_unique_thermodynamic_energy_density",
    "LiebThirring.tendsto_electronicGroundStateEnergy_tf",
    "LiebThirring.tendsto_groundStateEnergy_tf",
    "LiebThirring.exists_unique_tfRelaxedMinimizer",
    "LiebThirring.tfEnergy_saturation_and_attainment",
)
MODULES = (
    "LiebThirring",
    "LiebThirring.Ionization.BindingBound",
    "LiebThirring.Ionization.WeakGroundStateBound",
    "LiebThirring.Thermodynamic.ThermodynamicLimit",
    "LiebThirring.ThomasFermi.MolecularLimit",
    "LiebThirring.ThomasFermi.TotalLimit",
    "LiebThirring.ThomasFermi.RelaxedMinimizer",
    "LiebThirring.ThomasFermi.Saturation",
)
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}


def main():
    root = Path(__file__).resolve().parents[2]
    source = "".join(f"import {module}\n" for module in MODULES) + "".join(
        f"#print axioms {name}\n" for name in THEOREMS
    )
    result = subprocess.run(
        ["lake", "env", "lean", "--stdin"],
        input=source,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        cwd=root,
        check=False,
    )
    print(result.stdout, end="")
    if result.returncode:
        return result.returncode
    reports = {}
    for match in re.finditer(r"'([^']+)' depends on axioms: \[([^\]]*)\]", result.stdout):
        name, axioms = match.groups()
        if name in reports:
            print(f"FAIL {name}: duplicate axiom report")
            return 1
        reports[name] = {a.strip() for a in axioms.split(",") if a.strip()}
    for match in re.finditer(r"'([^']+)' does not depend on any axioms", result.stdout):
        name = match.group(1)
        if name in reports:
            print(f"FAIL {name}: duplicate axiom report")
            return 1
        reports[name] = set()
    failed = set(reports) != set(THEOREMS)
    if failed:
        print(f"FAIL missing reports: {sorted(set(THEOREMS) - set(reports))}")
        print(f"FAIL unexpected reports: {sorted(set(reports) - set(THEOREMS))}")
    for name in THEOREMS:
        if name in reports and not reports[name] <= ALLOWED:
            print(f"FAIL {name}: unexpected axioms {sorted(reports[name] - ALLOWED)}")
            failed = True
    if not failed:
        print(f"PASS: all {len(THEOREMS)} theorems use only the permitted standard axioms")
    return int(failed)


if __name__ == "__main__":
    sys.exit(main())
