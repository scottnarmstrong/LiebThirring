/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFQuantum.ElectronicInfimum

/-! # The electronic/total energy bridge on the exact carriers

For unnormalized states the nuclear constant is multiplied by the squared
L² norm. On the literal normalized trial subtype it is a fixed finite real
number, which can be moved through the complete-order EReal infimum.
The proof moves the nuclear constant through the variational infimum.
-/

public section
open MeasureTheory
open scoped ENNReal NNReal
namespace LiebThirring

/-- The unnormalized total form has precisely the nuclear constant times the state mass. -/
theorem realEnergy_eq_electronicEnergy_add_nuclear {N q M : ℕ}
    (z : Fin M → ℝ≥0) (R : Fin M → Position) (hR : Function.Injective R)
    (ψ : FormDomain N q) :
    realEnergy z R hR ψ = electronicEnergy z R ψ +
      (nuclearRepulsion z R).toReal * ‖(ψ : State N q)‖ ^ 2 := by
  unfold realEnergy electronicEnergy
  ring

/-- Normalization removes the mass factor from the nuclear constant. -/
theorem realEnergy_eq_electronicEnergy_add_nuclear_of_normalized {N q M : ℕ}
    (z : Fin M → ℝ≥0) (R : Fin M → Position) (hR : Function.Injective R)
    (ψ : FormDomain N q) (hψ : ‖(ψ : State N q)‖ = 1) :
    realEnergy z R hR ψ = electronicEnergy z R ψ + (nuclearRepulsion z R).toReal := by
  rw [realEnergy_eq_electronicEnergy_add_nuclear, hψ, one_pow, mul_one]

private theorem iInf_add_real {ι : Type*} (f : ι → EReal) (c : ℝ) :
    (⨅ i, f i) + (c : EReal) = ⨅ i, f i + (c : EReal) := by
  apply le_antisymm
  · apply le_iInf
    intro i
    exact add_le_add (iInf_le f i) le_rfl
  · have h : (⨅ i, f i + (c : EReal)) - (c : EReal) ≤ ⨅ i, f i := by
      apply le_iInf
      intro i
      apply (EReal.addLECancellable_coe c).add_le_add_iff_right.mp
      rw [EReal.sub_add_cancel]
      exact iInf_le (fun i => f i + (c : EReal)) i
    have h' := add_le_add h (le_refl (c : EReal))
    rwa [EReal.sub_add_cancel] at h'

/-- Moving the finite nuclear constant through the infimum, including empty sectors. -/
theorem groundStateEnergy_eq_electronic_add_nuclear_all_spins (N q M : ℕ)
    (z : Fin M → ℝ≥0) (R : Fin M → Position) (hR : Function.Injective R) :
    groundStateEnergy N q M z R hR = electronicGroundStateEnergy N q M z R +
      ((nuclearRepulsion z R).toReal : EReal) := by
  unfold groundStateEnergy
  have he (ψ : ElectronicTrial N q) : (realEnergy z R hR ψ.val : EReal) =
      (electronicEnergy z R ψ.val : EReal) + ((nuclearRepulsion z R).toReal : EReal) := by
    rw [realEnergy_eq_electronicEnergy_add_nuclear_of_normalized z R hR ψ.val ψ.property]
    exact EReal.coe_add _ _
  simp_rw [he]
  exact (iInf_add_real _ _).symm

/-- The proposed positive-spin bridge, with exactly the electronic and total energies. -/
theorem groundStateEnergy_eq_electronic_add_nuclear (q : ℕ) (_hq : 1 ≤ q)
    (N M : ℕ) (z : Fin M → ℝ≥0) (R : Fin M → Position)
    (hR : Function.Injective R) :
    groundStateEnergy N q M z R hR = electronicGroundStateEnergy N q M z R +
      ((nuclearRepulsion z R).toReal : EReal) :=
  groundStateEnergy_eq_electronic_add_nuclear_all_spins N q M z R hR

end LiebThirring
end
