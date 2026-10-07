/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFQuantum.ElectronicForm

/-! # Finiteness and variational properties of the quantum electronic infimum

All nuclear configurations and arbitrary nonnegative real charges are allowed:
the electronic form omits the singular nuclear-nuclear constant. Hardy gives
a uniform lower bound and the existing actual normalized compact trial gives
nonemptiness for positive spin multiplicity. The EReal infimum is
therefore finite, and comparison and near-minimizer properties follow without
an eigenfunction or minimizer premise. The proof uses Hardy estimates and normalized compact trials to control the infimum.
-/

public section
open MeasureTheory
open scoped ENNReal NNReal
namespace LiebThirring

/-- The genuine electronic variational infimum bounds every normalized form-domain trial. -/
theorem electronicGroundStateEnergy_le_electronicEnergy {N q M : ℕ}
    (z : Fin M → ℝ≥0) (R : Fin M → Position) (ψ : FormDomain N q)
    (hψ : ‖(ψ : State N q)‖ = 1) :
    electronicGroundStateEnergy N q M z R ≤ (electronicEnergy z R ψ : EReal) :=
  iInf_le (fun u : ElectronicTrial N q => (electronicEnergy z R u.val : EReal)) ⟨ψ, hψ⟩

/-- The actual electronic infimum has the source-derived Hardy lower bound, even in empty sectors. -/
theorem electronicGroundStateEnergy_lower_bound (N q M : ℕ)
    (z : Fin M → ℝ≥0) (R : Fin M → Position) :
    ((-(N : ℝ) * (∑ k, (z k : ℝ)) ^ 2 : ℝ) : EReal) ≤
      electronicGroundStateEnergy N q M z R := by
  apply le_iInf
  intro ψ
  exact EReal.coe_le_coe_iff.mpr (electronicEnergy_lower_bound z R ψ.val ψ.property)

/-- Negative infinity is excluded by Hardy, without nuclear separation or nonemptiness premises. -/
theorem electronicGroundStateEnergy_ne_bot (N q M : ℕ)
    (z : Fin M → ℝ≥0) (R : Fin M → Position) :
    electronicGroundStateEnergy N q M z R ≠ ⊥ :=
  ne_bot_of_le_ne_bot (EReal.coe_ne_bot _)
    (electronicGroundStateEnergy_lower_bound N q M z R)

/-- Every actual normalized trial excludes positive infinity. -/
theorem electronicGroundStateEnergy_ne_top_of_trial {N q M : ℕ}
    (z : Fin M → ℝ≥0) (R : Fin M → Position) (ψ : FormDomain N q)
    (hψ : ‖(ψ : State N q)‖ = 1) :
    electronicGroundStateEnergy N q M z R ≠ ⊤ :=
  (lt_of_le_of_lt (electronicGroundStateEnergy_le_electronicEnergy z R ψ hψ)
    (EReal.coe_lt_top _)).ne

/-- For positive spin multiplicity the electronic infimum is finite for every static data. -/
theorem electronicGroundStateEnergy_ne_top_ne_bot (q : ℕ) (hq : 1 ≤ q)
    (N M : ℕ) (z : Fin M → ℝ≥0) (R : Fin M → Position) :
    electronicGroundStateEnergy N q M z R ≠ ⊤ ∧
      electronicGroundStateEnergy N q M z R ≠ ⊥ := by
  obtain ⟨ψ⟩ := nonempty_electronicTrial q hq N
  exact ⟨electronicGroundStateEnergy_ne_top_of_trial z R ψ.val ψ.property,
    electronicGroundStateEnergy_ne_bot N q M z R⟩

end LiebThirring
end
