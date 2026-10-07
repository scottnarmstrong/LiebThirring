/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.ThermoForm.SchwartzEnergy
public import LiebThirring.ThermoForm.Vacuum
import LiebThirring.Kinetic.Permutation

/-! # Smooth joint trials and their Dirichlet inclusion

Argument thermodynamic confined form estimates. Pointwise statistics descend through the
volume-preserving joint permutation actions. A compact smooth trial supported
in the confinement region belongs to the Dirichlet form domain.
-/

public section

open MeasureTheory WithLp
open scoped ENNReal NNReal SchwartzMap

namespace LiebThirring

theorem measurePreserving_quantum_electron_permutation {N M : ℕ}
    (σ : Equiv.Perm (Fin N)) :
    MeasurePreserving (fun X : QuantumConfiguration N M =>
      toLp 2 (permutePositions σ X.fst, X.snd)) volume volume := by
  convert (LinearIsometryEquiv.withLpProdCongr 2 (permutationLinearIsometryEquiv σ)
    (LinearIsometryEquiv.refl ℝ (Configuration M))).measurePreserving using 1
  ext X
  rfl

theorem measurePreserving_quantum_nuclear_permutation {N M : ℕ}
    (τ : Equiv.Perm (Fin M)) :
    MeasurePreserving (fun X : QuantumConfiguration N M =>
      toLp 2 (X.fst, permutePositions τ X.snd)) volume volume := by
  convert (LinearIsometryEquiv.withLpProdCongr 2
    (LinearIsometryEquiv.refl ℝ (Configuration N))
    (permutationLinearIsometryEquiv τ)).measurePreserving using 1
  ext X
  rfl

theorem quantum_antisymmetric_toLp_of_pointwise {N M q : ℕ}
    (f : 𝓢(QuantumConfiguration N M, SpinAmplitudes N q))
    (hf : ∀ (σ : Equiv.Perm (Fin N)) (X : QuantumConfiguration N M) (s : SpinLabels N q),
      f (toLp 2 (permutePositions σ X.fst, X.snd)) (permuteSpins σ s) =
        (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : ℂ) * f X s) :
    quantum_antisymmetric (f.toLp 2 volume) := by
  intro σ
  filter_upwards [f.coeFn_toLp 2 volume,
    (measurePreserving_quantum_electron_permutation σ).quasiMeasurePreserving.ae
      (f.coeFn_toLp 2 volume)] with X hX hσ
  intro s
  rw [hX, hσ]
  exact hf σ X s

theorem nuclear_symmetric_toLp_of_pointwise {N M q : ℕ}
    (f : 𝓢(QuantumConfiguration N M, SpinAmplitudes N q))
    (hf : ∀ (τ : Equiv.Perm (Fin M)) (X : QuantumConfiguration N M) (s : SpinLabels N q),
      f (toLp 2 (X.fst, permutePositions τ X.snd)) s = f X s) :
    nuclear_symmetric (f.toLp 2 volume) := by
  intro τ
  filter_upwards [f.coeFn_toLp 2 volume,
    (measurePreserving_quantum_nuclear_permutation τ).quasiMeasurePreserving.ae
      (f.coeFn_toLp 2 volume)] with X hX hτ
  intro s
  rw [hX, hτ]
  exact hf τ X s

theorem is_dirichlet_ball_of_schwartz {N M q : ℕ}
    (m : {m : ℝ≥0 // 0 < m}) (L : {L : ℝ // 0 < L})
    (f : 𝓢(QuantumConfiguration N M, SpinAmplitudes N q))
    (hc : IsCompact (tsupport f))
    (hL : tsupport f ⊆ {X | (∀ i : Fin N, particlePosition X.fst i ∈
      Metric.ball (0 : Position) L.val) ∧
      (∀ k : Fin M, particlePosition X.snd k ∈ Metric.ball (0 : Position) L.val)})
    (ha : quantum_antisymmetric (f.toLp 2 volume))
    (hn : nuclear_symmetric (f.toLp 2 volume)) :
    is_dirichlet_ball m L (f.toLp 2 volume) := by
  intro ε hε
  refine ⟨f, hc, hL, ha, hn, ?_⟩
  rw [sub_self, quantumElectronKineticEnergy_zero, quantumNuclearKineticEnergy_zero]
  simpa only [norm_zero, zero_pow (by decide : 2 ≠ 0), ENNReal.ofReal_zero,
    add_zero, mul_zero] using ENNReal.ofReal_pos.mpr hε

end LiebThirring

end
