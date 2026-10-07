/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFUpper.SlaterBound

/-! # Appending orbital families and estimating their direct upper energy

The positive Coulomb algebra is used only for finite TF densities. The
nuclear attraction of the added family has favorable sign and is discarded.
direct proof.
-/

public section
open MeasureTheory
open scoped ENNReal NNReal
namespace LiebThirring.TFUpper

theorem slaterOrbitalDensity_addCases {n r q : ℕ}
    (u : Fin n → State 1 q) (v : Fin r → State 1 q) (x : Position) :
    slaterOrbitalDensity (Fin.addCases u v) x =
      slaterOrbitalDensity u x + slaterOrbitalDensity v x := by
  rw [slaterOrbitalDensity_eq_sum_norm_sq, Fin.sum_univ_add]
  simp only [Fin.addCases_left, Fin.addCases_right]
  rw [← slaterOrbitalDensity_eq_sum_norm_sq, ← slaterOrbitalDensity_eq_sum_norm_sq]

theorem orthonormal_addCases {n r q : ℕ}
    (u : Fin n → State 1 q) (v : Fin r → State 1 q)
    (hu : Orthonormal ℂ u) (hv : Orthonormal ℂ v)
    (hc : ∀ i j, inner ℂ (u i) (v j) = 0) :
    Orthonormal ℂ (Fin.addCases u v) := by
  rw [orthonormal_iff_ite]
  intro i j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;>
    refine Fin.addCases (fun j => ?_) (fun j => ?_) j
  · simpa only [Fin.addCases_left, Fin.castAdd_inj] using (orthonormal_iff_ite.mp hu i j)
  · have hij : Fin.castAdd r i ≠ Fin.natAdd n j := by
      intro h
      have hv := congrArg Fin.val h
      simp only [Fin.val_castAdd, Fin.val_natAdd] at hv
      omega
    simp only [Fin.addCases_left, Fin.addCases_right, hc, hij, ite_false]
  · have hij : Fin.natAdd n i ≠ Fin.castAdd r j := by
      intro h
      have hv := congrArg Fin.val h
      simp only [Fin.val_castAdd, Fin.val_natAdd] at hv
      omega
    simp only [Fin.addCases_left, Fin.addCases_right, hij, ite_false]
    rw [← inner_conj_symm (𝕜 := ℂ) (v i) (u j), hc, map_zero]
  · simpa only [Fin.addCases_right, Fin.natAdd_inj] using (orthonormal_iff_ite.mp hv i j)

theorem tfDensity_add_represents_append {n r q : ℕ}
    (u : Fin n → State 1 q) (v : Fin r → State 1 q) (d e : TFDensity)
    (hd : ∀ᵐ x : Position, d.val x = slaterOrbitalDensity u x)
    (he : ∀ᵐ x : Position, e.val x = slaterOrbitalDensity v x) :
    ∀ᵐ x : Position, (TFFunctional.tfDensityAdd d e).val x =
      slaterOrbitalDensity (Fin.addCases u v) x := by
  filter_upwards [TFFunctional.tfDensityAdd_coeFn d e, hd, he] with x ha hd he
  rw [ha, hd, he, slaterOrbitalDensity_addCases]

/-- Explicit cost of adding a remote family. No particle monotonicity is used. -/
theorem orbitalUpperEnergy_append_le {n r q M : ℕ}
    (α : ℝ≥0) (z : Fin M → ℝ≥0) (R : Fin M → Position)
    (u : Fin n → State 1 q) (v : Fin r → State 1 q) (d e : TFDensity)
    (hd : ∀ᵐ x : Position, d.val x = slaterOrbitalDensity u x)
    (he : ∀ᵐ x : Position, e.val x = slaterOrbitalDensity v x) :
    orbitalUpperEnergy α z R (Fin.addCases u v) ≤ orbitalUpperEnergy α z R u +
      (α : ℝ) ^ (-(5 : ℝ) / 3) * ∑ i, (kineticEnergy (v i)).toReal +
      (α : ℝ) ^ (-(2 : ℝ)) * (2 * tfCoulombEnergy d e + tfCoulombEnergy e e) := by
  have hA {k : ℕ} (w : TFDensity) (f : Fin k → State 1 q)
      (hw : ∀ᵐ x : Position, w.val x = slaterOrbitalDensity f x) :
      (∫ x : Position, tfNuclearPotential z R x * slaterOrbitalDensity f x) =
        ∫ x : Position, tfNuclearPotential z R x * w.val x := by
    apply integral_congr_ae
    filter_upwards [hw] with x hx
    rw [hx]
  have hrep := tfDensity_add_represents_append u v d e hd he
  have hAe := TFFunctional.integral_tfNuclearPotential_mul_nonneg z R e
  have hcost : 0 ≤ (α : ℝ) ^ (-(1 : ℝ)) *
      ∫ x : Position, tfNuclearPotential z R x * e.val x :=
    mul_nonneg (Real.rpow_nonneg α.property _) hAe
  unfold orbitalUpperEnergy
  rw [Fin.sum_univ_add]
  simp only [Fin.addCases_left, Fin.addCases_right]
  rw [slaterDirectCoulomb_toReal_eq_tfDensity _ _ hrep,
    slaterDirectCoulomb_toReal_eq_tfDensity _ _ hd,
    TFFunctional.tfCoulombEnergy_add_self,
    hA _ _ hrep, hA _ _ hd, TFFunctional.integral_tfNuclearPotential_mul_add]
  linarith only [hcost]

end LiebThirring.TFUpper
end
