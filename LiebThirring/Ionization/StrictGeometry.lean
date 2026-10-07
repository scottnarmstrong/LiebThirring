/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Sobolev.Collisions

/-!
# Strict triangle inequality almost everywhere

The equality case is contained in a one-dimensional subspace,
which has zero three-dimensional volume. Particle insertion transports this
statement to the configuration carrier.
-/

public section

open MeasureTheory MeasureTheory.Measure WithLp

namespace LiebThirring

/-- A line through the origin has zero spatial volume. -/
theorem volume_position_span_singleton (x : Position) :
    volume (Submodule.span ℝ {x} : Set Position) = 0 := by
  apply Measure.addHaar_submodule
  intro h
  by_cases hx : x = 0
  · subst x
    have hz : Submodule.span ℝ ({0} : Set Position) = ⊥ := by simp
    have hd := congrArg (fun s : Submodule ℝ Position => Module.finrank ℝ s) h
    rw [hz, finrank_bot, finrank_top, finrank_euclideanSpace, Fintype.card_fin] at hd
    norm_num at hd
  · have hd := congrArg (fun s : Submodule ℝ Position => Module.finrank ℝ s) h
    rw [finrank_span_singleton hx, finrank_top, finrank_euclideanSpace,
      Fintype.card_fin] at hd
    norm_num at hd

/-- Away from the line through a nonzero vector the triangle inequality is strict. -/
theorem norm_sub_lt_add_of_not_mem_span {x y : Position} (hx : x ≠ 0)
    (hy : y ∉ Submodule.span ℝ {x}) : ‖x - y‖ < ‖x‖ + ‖y‖ := by
  apply lt_of_le_of_ne (norm_sub_le x y)
  intro he
  have hs := (norm_add_eq_iff_real (x := x) (y := -y)).mp
    (by simpa only [sub_eq_add_neg, norm_neg] using he)
  simp only [norm_neg] at hs
  have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  apply hy
  rw [Submodule.mem_span_singleton]
  refine ⟨-(‖y‖ / ‖x‖), ?_⟩
  have hh : (‖y‖ / ‖x‖) • x = -y := by
    rw [div_eq_mul_inv, mul_comm, mul_smul, hs, smul_smul, inv_mul_cancel₀ hn, one_smul]
  simpa only [neg_smul, neg_neg] using congrArg Neg.neg hh

/-- For a nonzero fixed position, the norm triangle inequality is strict a.e. -/
theorem ae_position_norm_sub_lt_add {y : Position} (hy : y ≠ 0) :
    ∀ᵐ x : Position, ‖x - y‖ < ‖x‖ + ‖y‖ := by
  have ha : ∀ᵐ x : Position, x ∉ Submodule.span ℝ {y} := by
    rw [ae_iff]
    simp only [not_not]
    change volume (Submodule.span ℝ {y} : Set Position) = 0
    exact volume_position_span_singleton y
  filter_upwards [ha] with x hx
  simpa only [norm_sub_rev, add_comm] using norm_sub_lt_add_of_not_mem_span hy hx

/-- Two distinct particle labels satisfy the strict triangle inequality a.e. -/
theorem ae_particlePosition_norm_sub_lt_add {N : ℕ} (i j : Fin N) (hij : i ≠ j) :
    ∀ᵐ x : Configuration N,
      ‖particlePosition x i - particlePosition x j‖ <
        ‖particlePosition x i‖ + ‖particlePosition x j‖ := by
  have hm : MeasurableSet {x : Configuration N |
      ‖particlePosition x i - particlePosition x j‖ <
        ‖particlePosition x i‖ + ‖particlePosition x j‖} :=
    measurableSet_lt ((measurable_particlePosition i).sub (measurable_particlePosition j)).norm
      ((measurable_particlePosition i).norm.add (measurable_particlePosition j).norm)
  have ht : ∀ᵐ z : Position × OtherConfiguration i ∂volume.prod volume,
      ‖particlePosition (insertParticle i z.1 z.2) i -
        particlePosition (insertParticle i z.1 z.2) j‖ <
      ‖particlePosition (insertParticle i z.1 z.2) i‖ +
        ‖particlePosition (insertParticle i z.1 z.2) j‖ := by
    apply (ae_prod_iff_ae_ae ((measurePreserving_insertParticle i).measurable hm)).mpr
    have hj : ∀ᵐ y : OtherConfiguration i,
        toLp 2 (fun a => y (⟨j, Ne.symm hij⟩, a)) ≠ (0 : Position) := by
      have hc := (measurePreserving_insertParticle i).quasiMeasurePreserving.ae
        (Sobolev.ae_particlePosition_ne j 0)
      have hh := ae_ae_of_ae_prod hc
      obtain ⟨x, hx⟩ := hh.exists
      simpa only [Sobolev.particlePosition_insertParticle_other i j (Ne.symm hij)] using hx
    have hh : ∀ᵐ y : OtherConfiguration i, ∀ᵐ x : Position,
        ‖x - toLp 2 (fun a => y (⟨j, Ne.symm hij⟩, a))‖ <
          ‖x‖ + ‖toLp 2 (fun a => y (⟨j, Ne.symm hij⟩, a))‖ := by
      filter_upwards [hj] with y hy
      exact ae_position_norm_sub_lt_add hy
    apply (ae_ae_comm ?_).mpr
      (by simpa only [Set.mem_ofPred_eq, particlePosition_insertParticle,
        Sobolev.particlePosition_insertParticle_other i j (Ne.symm hij)] using hh)
    exact (measurePreserving_insertParticle i).measurable hm
  rw [← (measurePreserving_insertParticle i).map_eq]
  exact (ae_map_iff (measurePreserving_insertParticle i).measurable.aemeasurable hm).mpr ht

end LiebThirring

end
