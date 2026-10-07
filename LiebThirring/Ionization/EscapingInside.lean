/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Ionization.EscapingMass
public import LiebThirring.Ionization.EscapingThreshold

/-! # The all-inside sector and exact finite-energy IMS assembly

The all-inside multiplier preserves full antisymmetry. Proper subsets use the blockwise variational comparison in the escaping-sector bound.
-/

public section

open MeasureTheory
open scoped ENNReal NNReal

namespace LiebThirring
open Sobolev

/-- Every radial IMS sector remains in the symmetry-free finite-energy domain. -/
theorem imsLocalizedState_kineticEnergy_lt_top {N q : ℕ} {R : ℝ} (hR : 0 < R)
    (S : Finset (Fin N)) (u : State N q) (hu : kineticEnergy u < ⊤) :
    kineticEnergy (imsLocalizedState hR S u) < ⊤ :=
  kineticEnergy_lipschitzBoundedSMul_lt_top u hu _ 1
    (norm_imsSectorWeight_le_one R S) _ (lipschitzWith_imsSectorWeight hR S)

/-- Full antisymmetry survives the all-inside localization. -/
theorem imsLocalizedState_univ_antisymmetric {N q : ℕ} {R : ℝ} (hR : 0 < R)
    (u : State N q) (hu : antisymmetric u) :
    antisymmetric (imsLocalizedState hR Finset.univ u) := by
  intro σ
  exact imsRampSector_permutation_identity hR u hu Finset.univ σ (by simp)

/-- The all-inside sector as a member of the original form domain. -/
@[expose] noncomputable def imsInsideForm {N q : ℕ} {R : ℝ} (hR : 0 < R)
    (u : FormDomain N q) : FormDomain N q :=
  ⟨imsLocalizedState hR Finset.univ (u : State N q),
    imsLocalizedState_univ_antisymmetric hR _ u.property.1,
    imsLocalizedState_kineticEnergy_lt_top hR _ _ u.property.2⟩

/-- The true N-electron variational bound applies to the all-inside term. -/
theorem atomic_inside_energy_ge {N q : ℕ} (hq : 1 ≤ q) (Z : ℝ≥0)
    {R : ℝ} (hR : 0 < R) (u : FormDomain N q) :
    (atomicGroundStateEnergy N q Z).toReal * imsInsideMass hR (u : State N q) ≤
      fullRealEnergy (fun _ : Fin 1 => Z) (fun _ => 0)
        (imsLocalizedState hR Finset.univ (u : State N q)) :=
  groundStateEnergy_toReal_mul_norm_sq_le_realEnergy q hq N 1
    (fun _ => Z) (fun _ => 0) (fun _ _ _ => Subsingleton.elim _ _) (imsInsideForm hR u)

/-- Exact IMS identity expressed with the symmetry-free real energy. -/
theorem fullRealEnergy_imsLocalizedState_partition {N q : ℕ} {R : ℝ}
    (hR : 0 < R) (Z : ℝ≥0) (u : State N q) (hu : kineticEnergy u < ⊤) :
    fullRealEnergy (fun _ : Fin 1 => Z) (fun _ => 0) u =
      (∑ S : Finset (Fin N),
        fullRealEnergy (fun _ : Fin 1 => Z) (fun _ => 0) (imsLocalizedState hR S u)) -
      ∫ x : Configuration N, imsRampErrorDensity R u x :=
  coulombEnergy_imsRamp_partition hR (fun _ : Fin 1 => Z) (fun _ => 0) u hu

/-- Mass of all proper sectors is the complementary mass. -/
theorem sum_erase_imsLocalizedState_norm_sq {N q : ℕ} {R : ℝ} (hR : 0 < R)
    (u : State N q) :
    (∑ S ∈ (Finset.univ : Finset (Finset (Fin N))).erase Finset.univ,
      ‖imsLocalizedState hR S u‖ ^ 2) = ‖u‖ ^ 2 - imsInsideMass hR u := by
  have hsum := sum_imsLocalizedState_norm_sq hR u
  have herase := Finset.sum_erase_add (Finset.univ : Finset (Finset (Fin N)))
    (fun S => ‖imsLocalizedState hR S u‖ ^ 2) (Finset.mem_univ Finset.univ)
  rw [hsum] at herase
  exact eq_sub_iff_add_eq.mpr herase

/-- Finite IMS assembly of estimate, conditional only on the separately required proper-sector
energy comparisons. This helper does not certify the proper-sector step. -/
theorem atomic_realEnergy_ge_inside_mass_of_sector_bounds {N q : ℕ} (hq : 1 ≤ q)
    (Z : ℝ≥0) {R : ℝ} (hR : 0 < R) (u : FormDomain N q)
    (hu : ‖(u : State N q)‖ = 1)
    (hsector : ∀ S : Finset (Fin N), S ≠ Finset.univ →
      ((atomicGroundStateEnergy (N - 1) q Z).toReal - (N : ℝ) * (Z : ℝ) / R) *
        ‖imsLocalizedState hR S (u : State N q)‖ ^ 2 ≤
      fullRealEnergy (fun _ : Fin 1 => Z) (fun _ => 0)
        (imsLocalizedState hR S (u : State N q))) :
    (atomicGroundStateEnergy N q Z).toReal * imsInsideMass hR (u : State N q) +
      (atomicGroundStateEnergy (N - 1) q Z).toReal * (1 - imsInsideMass hR (u : State N q)) -
      (N : ℝ) * (Z : ℝ) / R - (N : ℝ) * Real.pi ^ 2 / (4 * R ^ 2) ≤
      realEnergy (fun _ : Fin 1 => Z) (fun _ => 0)
        (fun _ _ _ => Subsingleton.elim _ _) u := by
  let a := (atomicGroundStateEnergy N q Z).toReal
  let b := (atomicGroundStateEnergy (N - 1) q Z).toReal
  let c := (N : ℝ) * (Z : ℝ) / R
  let m := imsInsideMass hR (u : State N q)
  have hinside := atomic_inside_energy_ge hq Z hR u
  have hproper : (b - c) * (1 - m) ≤
      ∑ S ∈ (Finset.univ : Finset (Finset (Fin N))).erase Finset.univ,
        fullRealEnergy (fun _ : Fin 1 => Z) (fun _ => 0)
          (imsLocalizedState hR S (u : State N q)) := by
    have h := Finset.sum_le_sum (s := (Finset.univ : Finset (Finset (Fin N))).erase Finset.univ)
      (fun S hS => hsector S (Finset.mem_erase.mp hS).1)
    rw [← Finset.mul_sum, sum_erase_imsLocalizedState_norm_sq, hu, one_pow] at h
    exact h
  have hsum := Finset.sum_erase_add (Finset.univ : Finset (Finset (Fin N)))
    (fun S => fullRealEnergy (fun _ : Fin 1 => Z) (fun _ => 0)
      (imsLocalizedState hR S (u : State N q))) (Finset.mem_univ Finset.univ)
  have hims := fullRealEnergy_imsLocalizedState_partition hR Z (u : State N q) u.property.2
  have herr := integral_imsRampErrorDensity_le hR (u : State N q)
  rw [hu, one_pow, mul_one] at herr
  have hnonneg := imsInsideMass_nonneg hR (u : State N q)
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hcm : 0 ≤ c * m := mul_nonneg hc hnonneg
  change a * m ≤ _ at hinside
  change a * m + b * (1 - m) - c - (N : ℝ) * Real.pi ^ 2 / (4 * R ^ 2) ≤ _
  rw [← fullRealEnergy_eq_realEnergy (fun _ : Fin 1 => Z) (fun _ => 0)
    (fun _ _ _ => Subsingleton.elim _ _) u]
  linarith only [hinside, hproper, hsum, hims, herr, hcm]

end LiebThirring
end
