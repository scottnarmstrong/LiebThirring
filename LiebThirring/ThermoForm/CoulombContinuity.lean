/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.ThermoForm.EnergyContinuity
public import LiebThirring.ThermoStability.CoulombFibres
public import LiebThirring.Assembly.Coulomb

/-! # Continuity of finite joint Coulomb expectations

The weighted quadratic estimate is applied to the exact positive repulsion and
attraction kernels of the joint form (the confined form estimates).
-/

public section

open MeasureTheory Filter WithLp
open scoped ENNReal NNReal Topology

namespace LiebThirring

theorem tendsto_quantumRepulsionEnergy_of_difference {N M q : ℕ}
    {β : Type*} {l : Filter β} (z : ℕ) (u : QuantumFormDomain N M q)
    (v : β → QuantumFormDomain N M q)
    (hu : quantumRepulsionEnergy z u.val < ⊤)
    (hv : ∀ n, quantumRepulsionEnergy z (v n).val < ⊤)
    (hd : ∀ n, quantumRepulsionEnergy z (v n - u).val < ⊤)
    (hlim : Tendsto (fun n => (quantumRepulsionEnergy z (v n - u).val).toReal)
      l (𝓝 0)) :
    Tendsto (fun n => (quantumRepulsionEnergy z (v n).val).toReal)
      l (𝓝 (quantumRepulsionEnergy z u.val).toReal) := by
  let p : QuantumConfiguration N M → ℝ≥0∞ := fun X =>
    electronRepulsion X.fst + nuclearRepulsion (fun _ : Fin M => (z : ℝ≥0))
      (fun k => particlePosition X.snd k)
  have hp : Measurable p :=
    (LiebThirring.Assembly.measurable_electronRepulsion.comp
      (continuous_fst.comp (WithLp.prod_continuous_ofLp ..)).measurable).add
        (ThermoStability.measurable_jointNuclearRepulsion N M z)
  have hsub (n : β) : (v n - u).val = (v n).val - u.val := rfl
  apply tendsto_lintegral_weight_sq_of_difference p hp u.val (fun n => (v n).val)
    hu hv
  · simpa only [quantumRepulsionEnergy, hsub, p] using hd
  · simpa only [quantumRepulsionEnergy, hsub, p] using hlim

theorem tendsto_quantumAttractionEnergy_of_difference {N M q : ℕ}
    {β : Type*} {l : Filter β} (z : ℕ) (u : QuantumFormDomain N M q)
    (v : β → QuantumFormDomain N M q)
    (hu : quantumAttractionEnergy z u.val < ⊤)
    (hv : ∀ n, quantumAttractionEnergy z (v n).val < ⊤)
    (hd : ∀ n, quantumAttractionEnergy z (v n - u).val < ⊤)
    (hlim : Tendsto (fun n => (quantumAttractionEnergy z (v n - u).val).toReal)
      l (𝓝 0)) :
    Tendsto (fun n => (quantumAttractionEnergy z (v n).val).toReal)
      l (𝓝 (quantumAttractionEnergy z u.val).toReal) := by
  have hsub (n : β) : (v n - u).val = (v n).val - u.val := rfl
  apply tendsto_lintegral_weight_sq_of_difference _
    (ThermoStability.measurable_jointAttraction N M z) u.val (fun n => (v n).val)
    hu hv
  · simpa only [quantumAttractionEnergy, hsub] using hd
  · simpa only [quantumAttractionEnergy, hsub] using hlim

/-- The signed energy converges when its four finite positive quadratic forms converge. -/
theorem tendsto_quantumEnergy_of_coulomb_differences {N M q : ℕ}
    {β : Type*} {l : Filter β} (z : ℕ) (m : {m : ℝ≥0 // 0 < m})
    (u : QuantumFormDomain N M q) (v : β → QuantumFormDomain N M q)
    (hrep : ∀ w : QuantumFormDomain N M q, quantumRepulsionEnergy z w.val < ⊤)
    (hattr : ∀ w : QuantumFormDomain N M q, quantumAttractionEnergy z w.val < ⊤)
    (he : Tendsto (fun n => (quantumElectronKineticEnergy (v n - u).val).toReal)
      l (𝓝 0))
    (hn : Tendsto (fun n => (quantumNuclearKineticEnergy (v n - u).val).toReal)
      l (𝓝 0))
    (hr : Tendsto (fun n => (quantumRepulsionEnergy z (v n - u).val).toReal)
      l (𝓝 0))
    (ha : Tendsto (fun n => (quantumAttractionEnergy z (v n - u).val).toReal)
      l (𝓝 0)) :
    Tendsto (fun n => quantumEnergy z m (v n)) l (𝓝 (quantumEnergy z m u)) := by
  have he' := tendsto_quantumElectronKineticEnergy_of_difference u v he
  have hn' := tendsto_quantumNuclearKineticEnergy_of_difference u v hn
  have hr' := tendsto_quantumRepulsionEnergy_of_difference z u v
    (hrep u) (fun n => hrep (v n)) (fun n => hrep (v n - u)) hr
  have ha' := tendsto_quantumAttractionEnergy_of_difference z u v
    (hattr u) (fun n => hattr (v n)) (fun n => hattr (v n - u)) ha
  exact (he'.add (hn'.const_mul (nuclearKineticCoefficient m : ℝ))).add (hr'.sub ha')

end LiebThirring

end
