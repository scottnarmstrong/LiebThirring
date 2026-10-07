/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Ionization.IMSRampError

/-! # Concrete kinetic and Coulomb IMS identities for the radial subset partition -/

public section

open MeasureTheory
open scoped NNReal ENNReal

namespace LiebThirring
open Sobolev Assembly

theorem norm_finset_prod_le_one {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (f : ι → ℝ) (hf : ∀ i ∈ s, ‖f i‖ ≤ 1) : ‖∏ i ∈ s, f i‖ ≤ 1 := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      rw [Finset.prod_insert hi, norm_mul]
      calc
        _ ≤ 1 * 1 := mul_le_mul (hf i (by simp))
          (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))) (norm_nonneg _) zero_le_one
        _ = 1 := one_mul 1

/-- Products of two real unit-bounded Lipschitz functions have the sum Lipschitz constant. -/
theorem LipschitzWith.mul_of_norm_le_one {E : Type*} [PseudoMetricSpace E]
    {f g : E → ℝ} {Cf Cg : ℝ≥0} (hf : LipschitzWith Cf f)
    (hg : LipschitzWith Cg g) (hfb : ∀ x, ‖f x‖ ≤ 1) (hgb : ∀ x, ‖g x‖ ≤ 1) :
    LipschitzWith (Cf + Cg) (fun x => f x * g x) := by
  rw [lipschitzWith_iff_dist_le_mul]
  intro x y
  rw [Real.dist_eq]
  calc
    |f x * g x - f y * g y| = |f x * (g x - g y) + g y * (f x - f y)| := by congr 1; ring
    _ ≤ |f x * (g x - g y)| + |g y * (f x - f y)| := abs_add_le _ _
    _ = |f x| * |g x - g y| + |g y| * |f x - f y| := by rw [abs_mul, abs_mul]
    _ ≤ 1 * ((Cg : ℝ) * dist x y) + 1 * ((Cf : ℝ) * dist x y) := by
      gcongr
      · simpa [Real.norm_eq_abs] using hfb x
      · simpa [Real.dist_eq] using (lipschitzWith_iff_dist_le_mul.mp hg x y)
      · simpa [Real.norm_eq_abs] using hgb y
      · simpa [Real.dist_eq] using (lipschitzWith_iff_dist_le_mul.mp hf x y)
    _ = ((Cf + Cg : ℝ≥0) : ℝ) * dist x y := by push_cast; ring

/-- A finite product of unit-bounded functions with a common Lipschitz constant has
Lipschitz constant `card * C`. -/
theorem lipschitzWith_finset_prod_of_norm_le_one {E ι : Type*} [PseudoMetricSpace E]
    [DecidableEq ι] (s : Finset ι) (f : ι → E → ℝ) (C : ℝ≥0)
    (hf : ∀ i ∈ s, LipschitzWith C (f i)) (hb : ∀ i ∈ s, ∀ x, ‖f i x‖ ≤ 1) :
    LipschitzWith (s.card * C) (fun x => ∏ i ∈ s, f i x) := by
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.card_empty, Nat.cast_zero, zero_mul, Finset.prod_empty]
      using (LipschitzWith.const (α := E) (1 : ℝ))
  | @insert i s hi ih =>
      have htail := ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))
        (fun j hj => hb j (Finset.mem_insert_of_mem hj))
      have htailb (x : E) : ‖∏ j ∈ s, f j x‖ ≤ 1 := by
        exact norm_finset_prod_le_one s (fun j => f j x)
          (fun j hj => hb j (Finset.mem_insert_of_mem hj) x)
      have hmul := LipschitzWith.mul_of_norm_le_one (hf i (by simp)) htail
        (hb i (by simp)) htailb
      simpa [Finset.prod_insert hi, Finset.card_insert_of_notMem hi, Nat.cast_add,
        Nat.cast_one, add_mul, add_comm] using hmul

/-- Every radial subset multiplier is bounded by one. -/
theorem norm_imsSectorWeight_le_one {N : ℕ} (R : ℝ) (S : Finset (Fin N))
    (x : Configuration N) : ‖imsSectorWeight (imsChi R) (imsEta R) S x‖ ≤ 1 := by
  rw [imsSectorWeight, norm_mul]
  calc
    _ ≤ 1 * 1 := mul_le_mul
      (norm_finset_prod_le_one S _ (fun i _ => norm_imsChi_le_one R _))
      (norm_finset_prod_le_one (Finset.univ \ S) _ (fun i _ => norm_imsEta_le_one R _))
      (norm_nonneg _) zero_le_one
    _ = 1 := one_mul 1

/-- A sufficient Lipschitz constant for every radial subset multiplier. -/
theorem lipschitzWith_imsSectorWeight {N : ℕ} {R : ℝ} (hR : 0 < R)
    (S : Finset (Fin N)) :
    LipschitzWith
      (N * NNReal.mk (Real.pi / (2 * R)) (by positivity))
      (imsSectorWeight (imsChi R) (imsEta R) S) := by
  let C : ℝ≥0 := NNReal.mk (Real.pi / (2 * R)) (by positivity)
  let f : Fin N → Configuration N → ℝ := fun i X => imsChi R (particlePosition X i)
  let g : Fin N → Configuration N → ℝ := fun i X => imsEta R (particlePosition X i)
  have hf (i : Fin N) : LipschitzWith C (f i) :=
    lipschitzWith_selected_multiplier i _ C (lipschitzWith_imsChi hR)
  have hg (i : Fin N) : LipschitzWith C (g i) :=
    lipschitzWith_selected_multiplier i _ C (lipschitzWith_imsEta hR)
  have hfp := lipschitzWith_finset_prod_of_norm_le_one S f C
    (fun i _ => hf i) (fun i _ x => norm_imsChi_le_one R _)
  have hgp := lipschitzWith_finset_prod_of_norm_le_one (Finset.univ \ S) g C
    (fun i _ => hg i) (fun i _ x => norm_imsEta_le_one R _)
  have hfpb : ∀ x, ‖∏ i ∈ S, f i x‖ ≤ 1 := fun x =>
    norm_finset_prod_le_one S _ (fun i _ => norm_imsChi_le_one R _)
  have hgpb : ∀ x, ‖∏ i ∈ Finset.univ \ S, g i x‖ ≤ 1 := fun x =>
    norm_finset_prod_le_one (Finset.univ \ S) _ (fun i _ => norm_imsEta_le_one R _)
  have hmul := LipschitzWith.mul_of_norm_le_one hfp hgp hfpb hgpb
  have hcard : S.card + (Finset.univ \ S).card = N := by
    have h := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ S)
    rw [Finset.card_univ, Fintype.card_fin] at h
    omega
  change LipschitzWith (N * C) (fun x =>
    (∏ i ∈ S, f i x) * ∏ i ∈ Finset.univ \ S, g i x)
  convert hmul using 1
  rw [← add_mul, ← Nat.cast_add, hcard]

/-- The literal radial sectors form a square partition when indexed by all finite subsets. -/
theorem sum_all_imsSectorWeight_sq {N : ℕ} (R : ℝ) (x : Configuration N) :
    (∑ S : Finset (Fin N), imsSectorWeight (imsChi R) (imsEta R) S x ^ 2) = 1 := by
  simpa using sum_imsSectorWeight_sq (imsChi R) (imsEta R)
    (imsChi_sq_add_imsEta_sq R) x

/-- Concrete Coulomb IMS identity for the literal radial subset partition. -/
theorem coulombEnergy_imsRamp_partition {N q M : ℕ} {R₀ : ℝ} (hR₀ : 0 < R₀)
    (z : Fin M → ℝ≥0) (R : Fin M → Position)
    (u : State N q) (hu : kineticEnergy u < ⊤) :
    let v := fun S : Finset (Fin N) => lipschitzBoundedSMul
      (imsSectorWeight (imsChi R₀) (imsEta R₀) S) 1
      (norm_imsSectorWeight_le_one R₀ S) (lipschitzWith_imsSectorWeight hR₀ S) u
    (kineticEnergy u).toReal +
      (∫⁻ x : Configuration N, electronRepulsion x * (‖u x‖₊ : ℝ≥0∞) ^ 2).toReal +
      (nuclearRepulsion z R).toReal * ‖u‖ ^ 2 -
      (∫⁻ x : Configuration N, attraction z R x * (‖u x‖₊ : ℝ≥0∞) ^ 2).toReal =
    (∑ S, ((kineticEnergy (v S)).toReal +
      (∫⁻ x : Configuration N, electronRepulsion x * (‖v S x‖₊ : ℝ≥0∞) ^ 2).toReal +
      (nuclearRepulsion z R).toReal * ‖v S‖ ^ 2 -
      (∫⁻ x : Configuration N, attraction z R x * (‖v S x‖₊ : ℝ≥0∞) ^ 2).toReal)) -
        ∫ x : Configuration N, imsRampErrorDensity R₀ u x := by
  let C : Finset (Fin N) → ℝ≥0 := fun _ =>
    N * NNReal.mk (Real.pi / (2 * R₀)) (by positivity)
  have h := coulombEnergy_lipschitz_partition z R u hu
    (fun S => imsSectorWeight (imsChi R₀) (imsEta R₀) S) (fun _ => 1)
    (fun S => norm_imsSectorWeight_le_one R₀ S) C
    (fun S => lipschitzWith_imsSectorWeight hR₀ S) (sum_all_imsSectorWeight_sq R₀)
  rw [lipschitz_partition_error_eq_integral u
    (fun S => imsSectorWeight (imsChi R₀) (imsEta R₀) S) C
    (fun S => lipschitzWith_imsSectorWeight hR₀ S)] at h
  have herr :
      (∫ x : Configuration N,
        (∑ a : Fin N × Fin 3, ∑ S : Finset (Fin N),
          lipschitzDirectionalDerivative
            (imsSectorWeight (imsChi R₀) (imsEta R₀) S) a x ^ 2) * ‖u x‖ ^ 2) =
      ∫ x : Configuration N, imsRampErrorDensity R₀ u x := by
    apply integral_congr_ae
    filter_upwards [] with x
    simp only [imsRampErrorDensity]
    congr 1
  rw [herr] at h
  exact h

/-- A bounded Lipschitz multiplier fixed by a particle permutation preserves the
corresponding fermionic identity. -/
theorem lipschitzBoundedSMul_permutation_identity {N q : ℕ}
    (u : State N q) (hu : antisymmetric u) (b : Configuration N → ℝ)
    (B : ℝ) (hB : ∀ x, ‖b x‖ ≤ B) (C : ℝ≥0) (hb : LipschitzWith C b)
    (σ : Equiv.Perm (Fin N)) (hinv : ∀ x, b (permutePositions σ x) = b x) :
    ∀ᵐ x ∂(volume : Measure (Configuration N)), ∀ s : SpinLabels N q,
      lipschitzBoundedSMul b B hB hb u (permutePositions σ x) (permuteSpins σ s) =
        (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : ℂ) * lipschitzBoundedSMul b B hB hb u x s := by
  have hrep := lipschitzBoundedSMul_coeFn b B hB hb u
  filter_upwards [hrep, (measurePreserving_permutePositions σ).quasiMeasurePreserving.ae hrep,
    hu σ] with x hx hpx hux
  intro s
  rw [hx, hpx]
  simp only [PiLp.smul_apply, smul_eq_mul, hinv, hux s]
  ring

/-- A radial IMS sector preserves antisymmetry under every permutation stabilizing its
inside subset (equivalently, permutations within the inside and outside blocks). -/
theorem imsRampSector_permutation_identity {N q : ℕ} {R : ℝ} (hR : 0 < R)
    (u : State N q) (hu : antisymmetric u) (S : Finset (Fin N))
    (σ : Equiv.Perm (Fin N)) (hσ : ∀ i, i ∈ S ↔ σ i ∈ S) :
    ∀ᵐ x ∂(volume : Measure (Configuration N)), ∀ s : SpinLabels N q,
      lipschitzBoundedSMul (imsSectorWeight (imsChi R) (imsEta R) S) 1
          (norm_imsSectorWeight_le_one R S) (lipschitzWith_imsSectorWeight hR S) u
          (permutePositions σ x) (permuteSpins σ s) =
        (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : ℂ) *
          lipschitzBoundedSMul (imsSectorWeight (imsChi R) (imsEta R) S) 1
            (norm_imsSectorWeight_le_one R S) (lipschitzWith_imsSectorWeight hR S) u x s :=
  lipschitzBoundedSMul_permutation_identity u hu _ 1
    (norm_imsSectorWeight_le_one R S) _ (lipschitzWith_imsSectorWeight hR S) σ
    (imsSectorWeight_permutePositions _ _ S σ hσ)

end LiebThirring

end
