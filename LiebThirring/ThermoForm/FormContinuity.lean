/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.ThermoForm.CoulombContinuity
public import LiebThirring.ThermoForm.FormBounds

/-! # Continuity of the full joint quantum form

Argument thermodynamic confined form estimates. The pair Hardy bounds discharge every Coulomb
finiteness and continuity premise on the exact finite-kinetic carrier.
-/

public section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology

namespace LiebThirring

/-- Full quantum energy is continuous under convergence in the joint kinetic form norm. -/
theorem tendsto_quantumEnergy_of_difference {N M q : ℕ}
    {β : Type*} {l : Filter β} (z : ℕ) (m : {m : ℝ≥0 // 0 < m})
    (u : QuantumFormDomain N M q) (v : β → QuantumFormDomain N M q)
    (h0 : Tendsto (fun n => ‖(v n - u).val‖) l (𝓝 0))
    (he : Tendsto (fun n => (quantumElectronKineticEnergy (v n - u).val).toReal)
      l (𝓝 0))
    (hn : Tendsto (fun n => (quantumNuclearKineticEnergy (v n - u).val).toReal)
      l (𝓝 0)) :
    Tendsto (fun n => quantumEnergy z m (v n)) l (𝓝 (quantumEnergy z m u)) := by
  obtain ⟨C, hC, hbound⟩ := exists_quantumCoulomb_formBound N M q z
  have hfinite (w : QuantumFormDomain N M q) :
      C * (ENNReal.ofReal (‖w.val‖ ^ 2) + quantumElectronKineticEnergy w.val +
        quantumNuclearKineticEnergy w.val) < ⊤ := by
    exact ENNReal.mul_lt_top hC.lt_top (ENNReal.add_lt_top.mpr
      ⟨ENNReal.add_lt_top.mpr ⟨ENNReal.ofReal_lt_top, w.property.2.2.1⟩,
        w.property.2.2.2⟩)
  have hr := tendsto_zero_of_joint_kinetic_bound (quantumRepulsionEnergy z) C hC
    (fun ψ => (hbound ψ).1) (fun n => v n - u) h0 he hn
  have ha := tendsto_zero_of_joint_kinetic_bound (quantumAttractionEnergy z) C hC
    (fun ψ => (hbound ψ).2) (fun n => v n - u) h0 he hn
  exact tendsto_quantumEnergy_of_coulomb_differences z m u v
    (fun w => ((hbound w.val).1).trans_lt (hfinite w))
    (fun w => ((hbound w.val).2).trans_lt (hfinite w)) he hn hr ha

end LiebThirring

end
