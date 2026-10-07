/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.ThomasFermi.ElectronicGroundStateEnergy
public import LiebThirring.Variational.FormFinite
public import LiebThirring.Variational.TrialConstruction

/-! # The actual electronic form and its normalized trial carrier

The real form is exactly the electronic infimum's integrand, with
the nuclear constant omitted. Existing Hardy estimates prove both Coulomb
terms finite for every state in the literal form domain, without a
nuclear separation assumption. Nonemptiness reuses the proved compact trial
construction. Proof: quantum form-domain estimates; the electronic energy and dilation definitions;
the domain and infimum packaging is direct proof.
-/

public section
open MeasureTheory
open scoped ENNReal NNReal
namespace LiebThirring

/-- The literal normalized subtype used by the electronic infimum. -/
abbrev ElectronicTrial (N q : ℕ) :=
  {ψ : FormDomain N q // ‖(ψ : State N q)‖ = 1}

/-- The literal electronic quadratic form, with no nuclear-nuclear constant. -/
@[expose] noncomputable def electronicEnergy {N q M : ℕ}
    (z : Fin M → ℝ≥0) (R : Fin M → Position) (ψ : FormDomain N q) : ℝ :=
  (kineticEnergy (ψ : State N q)).toReal +
    (∫⁻ x : Configuration N,
      electronRepulsion x * (‖(ψ : State N q) x‖₊ : ℝ≥0∞) ^ 2).toReal -
    (∫⁻ x : Configuration N,
      attraction z R x * (‖(ψ : State N q) x‖₊ : ℝ≥0∞) ^ 2).toReal

/-- The packaged integrand is exactly the infimum, including empty sectors. -/
theorem electronicGroundStateEnergy_eq_iInf_electronicEnergy (N q M : ℕ)
    (z : Fin M → ℝ≥0) (R : Fin M → Position) :
    electronicGroundStateEnergy N q M z R =
      ⨅ ψ : ElectronicTrial N q, (electronicEnergy z R ψ.val : EReal) := rfl

/-- The existing compact Slater trial supplies a normalized electronic competitor at every N. -/
theorem nonempty_electronicTrial (q : ℕ) (hq : 1 ≤ q) (N : ℕ) :
    Nonempty (ElectronicTrial N q) := by
  obtain ⟨ψ, hψ⟩ := exists_normalized_formDomain_trial q hq N
  exact ⟨⟨ψ, hψ⟩⟩

/-- Hardy's infinitesimal attraction estimate gives a uniform electronic lower bound. -/
theorem electronicEnergy_lower_bound {N q M : ℕ}
    (z : Fin M → ℝ≥0) (R : Fin M → Position) (ψ : FormDomain N q)
    (hψ : ‖(ψ : State N q)‖ = 1) :
    -(N : ℝ) * (∑ k, (z k : ℝ)) ^ 2 ≤ electronicEnergy z R ψ := by
  have hA := lintegral_attraction_toReal_le z R ψ.val ψ.property.2
    (δ := 1) (by norm_num)
  rw [hψ] at hA
  simp only [one_mul, one_pow, div_one, mul_one] at hA
  have hB : 0 ≤ (∫⁻ x : Configuration N,
      electronRepulsion x * (‖(ψ : State N q) x‖₊ : ℝ≥0∞) ^ 2).toReal :=
    ENNReal.toReal_nonneg
  unfold electronicEnergy
  linarith only [hA, hB]

end LiebThirring
end
