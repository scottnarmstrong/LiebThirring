/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFQuantum.SlaterProduct
public import LiebThirring.Sobolev.Regrouping
import LiebThirring.Kinetic.Insertion

/-! # Partial integration of orbital products

Selected particle coordinates carry an arbitrary complex observable. Integrating
the remaining coordinates contracts exactly their orbital inner products.
-/

public section
open MeasureTheory WithLp
open scoped ComplexConjugate Classical
namespace LiebThirring

/-- Physical position of a particle in a block indexed by an arbitrary finite type. -/
@[expose] def orbitalBlockPosition {ι : Type*} [Fintype ι]
    (X : EuclideanSpace ℝ (ι × Fin 3)) (i : ι) : Position :=
  toLp 2 (fun a => X (i, a))

theorem orbitalBlockPosition_reindex {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : ι ≃ κ) (X : EuclideanSpace ℝ (ι × Fin 3)) (i : ι) :
    orbitalBlockPosition (Sobolev.configurationReindexMeasurableEquiv e X) (e i) =
      orbitalBlockPosition X i := by
  ext a
  simp only [orbitalBlockPosition, PiLp.toLp_apply]
  simp only [Sobolev.configurationReindexMeasurableEquiv,
    MeasurableEquiv.trans_apply, MeasurableEquiv.toLp_apply,
    MeasurableEquiv.toLp_symm_apply, MeasurableEquiv.piCongrLeft]
  exact Equiv.piCongrLeft_apply_apply _ _ _ (i, a)

/-- The product integration identity on any finite particle block. -/
theorem integral_prod_orbitalContraction_fintype {ι : Type*} [Fintype ι] {q : ℕ}
    (u v : ι → State 1 q) :
    (∫ X : EuclideanSpace ℝ (ι × Fin 3),
      ∏ i : ι, orbitalContraction (u i) (v i) (orbitalBlockPosition X i)) =
      ∏ i : ι, inner ℂ (u i) (v i) := by
  classical
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  let E := Sobolev.configurationReindexMeasurableEquiv e
  have hmp := Sobolev.measurePreserving_configurationReindex e
  calc
    _ = ∫ X : Configuration (Fintype.card ι),
        ∏ i : Fin (Fintype.card ι),
          orbitalContraction (u (e i)) (v (e i)) (particlePosition X i) := by
      rw [← hmp.integral_comp E.measurableEmbedding]
      apply integral_congr_ae
      filter_upwards [] with X
      rw [← e.prod_comp]
      apply Finset.prod_congr rfl
      intro i _
      rw [orbitalBlockPosition_reindex]
      rfl
    _ = _ := (integral_prod_orbitalContraction (u ∘ e) (v ∘ e)).trans (by
      simpa only [Function.comp_apply] using
        (e.prod_comp (fun i => inner ℂ (u i) (v i))))

theorem integrable_prod_orbitalContraction_fintype {ι : Type*} [Fintype ι] {q : ℕ}
    (u v : ι → State 1 q) :
    Integrable (fun X : EuclideanSpace ℝ (ι × Fin 3) =>
      ∏ i : ι, orbitalContraction (u i) (v i) (orbitalBlockPosition X i)) := by
  classical
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  let E := Sobolev.configurationReindexMeasurableEquiv e
  have hmp := Sobolev.measurePreserving_configurationReindex e
  apply (hmp.integrable_comp_emb E.measurableEmbedding).mp
  refine (integrable_prod_orbitalContraction (u ∘ e) (v ∘ e)).congr ?_
  filter_upwards [] with X
  simp only [Function.comp_def]
  rw [← e.prod_comp]
  apply Finset.prod_congr rfl
  intro i _
  rw [orbitalBlockPosition_reindex]
  rfl

theorem orbitalBlockPosition_insertParticle {N : ℕ} (i : Fin N) (x : Position)
    (Y : OtherConfiguration i) (j : {j : Fin N // j ≠ i}) :
    particlePosition (insertParticle i x Y) j = orbitalBlockPosition Y j := by
  ext a
  simp only [particlePosition, insertParticle, orbitalBlockPosition, PiLp.toLp_apply,
    j.property, ↓reduceDIte]

/-- Integrating a one-particle fiber contracts precisely the spectator orbitals. -/
theorem integral_orbitalContraction_insertParticle {N q : ℕ}
    (u v : Fin N → State 1 q) (i : Fin N) (x : Position) :
    (∫ Y : OtherConfiguration i,
      ∏ j : Fin N, orbitalContraction (u j) (v j)
        (particlePosition (insertParticle i x Y) j)) =
      orbitalContraction (u i) (v i) x *
        ∏ j : {j : Fin N // j ≠ i}, inner ℂ (u j) (v j) := by
  simp_rw [Fintype.prod_eq_mul_prod_subtype_ne (a := i),
    particlePosition_insertParticle, orbitalBlockPosition_insertParticle]
  rw [integral_const_mul, integral_prod_orbitalContraction_fintype
    (fun j : {j : Fin N // j ≠ i} => u j) (fun j => v j)]

theorem integrable_orbitalContraction_insertParticle {N q : ℕ}
    (u v : Fin N → State 1 q) (i : Fin N) (x : Position) :
    Integrable (fun Y : OtherConfiguration i =>
      ∏ j : Fin N, orbitalContraction (u j) (v j)
        (particlePosition (insertParticle i x Y) j)) := by
  simp_rw [Fintype.prod_eq_mul_prod_subtype_ne (a := i),
    particlePosition_insertParticle, orbitalBlockPosition_insertParticle]
  exact (integrable_prod_orbitalContraction_fintype
    (fun j : {j : Fin N // j ≠ i} => u j) (fun j => v j)).const_mul _

end LiebThirring
end
