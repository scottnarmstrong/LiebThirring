/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Kinetic.Encoding

/-!
# Regrouping arbitrary subsets of particles

Argument product and collision identities on the Euclidean configuration and counting-spin carriers.
A partition of particle indices has no Jacobian and introduces no spin factor.
-/

public section

open MeasureTheory WithLp
open scoped Classical

namespace LiebThirring.Sobolev

/-- Relabel any finite particle block using an ordering equivalence. -/
@[expose] noncomputable def configurationReindexMeasurableEquiv
    {ι κ : Type*} [Fintype ι] [Fintype κ] (e : ι ≃ κ) :
    EuclideanSpace ℝ (ι × Fin 3) ≃ᵐ EuclideanSpace ℝ (κ × Fin 3) :=
  (MeasurableEquiv.toLp 2 ((ι × Fin 3) → ℝ)).symm.trans
    ((MeasurableEquiv.piCongrLeft (fun _ : κ × Fin 3 => ℝ)
      (e.prodCongr (Equiv.refl (Fin 3)))).trans (MeasurableEquiv.toLp 2 _))

/-- Ordering a particle block does not change its Lebesgue measure. -/
theorem measurePreserving_configurationReindex
    {ι κ : Type*} [Fintype ι] [Fintype κ] (e : ι ≃ κ) :
    MeasurePreserving (configurationReindexMeasurableEquiv e) volume volume :=
  (PiLp.volume_preserving_ofLp (ι × Fin 3)).trans
    ((volume_measurePreserving_piCongrLeft _ (e.prodCongr (Equiv.refl (Fin 3)))).trans
      (PiLp.volume_preserving_toLp (κ × Fin 3)))

/-- Split the spatial coordinate index into a subset of particles and its complement. -/
@[expose] noncomputable def subsetCoordinateEquiv {N : ℕ} (S : Set (Fin N)) :
    (Fin N × Fin 3) ≃ ((S × Fin 3) ⊕ ((Sᶜ : Set (Fin N)) × Fin 3)) := by
  classical
  exact ((Equiv.Set.sumCompl S).symm.prodCongr (Equiv.refl (Fin 3))).trans
    (Equiv.sumProdDistrib S (Sᶜ : Set (Fin N)) (Fin 3))

/-- Insert the two spatial blocks into the original configuration. -/
@[expose] noncomputable def subsetInsertionMeasurableEquiv {N : ℕ} (S : Set (Fin N)) :
    (EuclideanSpace ℝ (S × Fin 3) × EuclideanSpace ℝ ((Sᶜ : Set (Fin N)) × Fin 3)) ≃ᵐ
      Configuration N :=
  ((MeasurableEquiv.toLp 2 ((S × Fin 3) → ℝ)).symm.prodCongr
    (MeasurableEquiv.toLp 2 (((Sᶜ : Set (Fin N)) × Fin 3) → ℝ)).symm).trans
  ((MeasurableEquiv.sumPiEquivProdPi (fun _ : (S × Fin 3) ⊕ ((Sᶜ : Set (Fin N)) × Fin 3) => ℝ)).symm.trans
    ((MeasurableEquiv.piCongrLeft (fun _ : (S × Fin 3) ⊕ ((Sᶜ : Set (Fin N)) × Fin 3) => ℝ)
      (subsetCoordinateEquiv S)).symm.trans (MeasurableEquiv.toLp 2 _)))

/-- Arbitrary particle-block insertion preserves the product of Lebesgue volumes. -/
theorem measurePreserving_subsetInsertion {N : ℕ} (S : Set (Fin N)) :
    MeasurePreserving (subsetInsertionMeasurableEquiv S) volume volume := by
  exact ((PiLp.volume_preserving_ofLp (S × Fin 3)).prod
    (PiLp.volume_preserving_ofLp ((Sᶜ : Set (Fin N)) × Fin 3))).trans
    ((volume_measurePreserving_sumPiEquivProdPi_symm _).trans
      ((volume_measurePreserving_piCongrLeft _ (subsetCoordinateEquiv S)).symm.trans
        (PiLp.volume_preserving_toLp (Fin N × Fin 3))))

/-- Read a coordinate in the selected block after insertion. -/
theorem subsetInsertion_apply_mem {N : ℕ} (S : Set (Fin N))
    (z : EuclideanSpace ℝ (S × Fin 3) × EuclideanSpace ℝ ((Sᶜ : Set (Fin N)) × Fin 3))
    (i : S) (a : Fin 3) : subsetInsertionMeasurableEquiv S z (i.val, a) = z.1 (i, a) := by
  classical
  simp only [subsetInsertionMeasurableEquiv, MeasurableEquiv.prodCongr,
    MeasurableEquiv.piCongrLeft, subsetCoordinateEquiv, Equiv.trans_apply,
    MeasurableEquiv.symm_mk, MeasurableEquiv.trans_apply, MeasurableEquiv.coe_mk,
    Equiv.prodCongr_apply, MeasurableEquiv.coe_toEquiv,
    MeasurableEquiv.coe_sumPiEquivProdPi_symm, Equiv.sumPiEquivProdPi, Equiv.symm_mk,
    Equiv.coe_fn_mk, Prod.map_fst, MeasurableEquiv.toLp_symm_apply, Prod.map_snd,
    MeasurableEquiv.toLp_apply, Equiv.piCongrLeft_symm_apply, Equiv.coe_refl,
    Prod.map_apply, Equiv.Set.sumCompl_symm_apply, id_eq, Equiv.sumProdDistrib_apply_left]

/-- Read a coordinate in the complementary block after insertion. -/
theorem subsetInsertion_apply_not_mem {N : ℕ} (S : Set (Fin N))
    (z : EuclideanSpace ℝ (S × Fin 3) × EuclideanSpace ℝ ((Sᶜ : Set (Fin N)) × Fin 3))
    (i : (Sᶜ : Set (Fin N))) (a : Fin 3) : subsetInsertionMeasurableEquiv S z (i.val, a) = z.2 (i, a) := by
  classical
  simp only [subsetInsertionMeasurableEquiv, MeasurableEquiv.prodCongr,
    MeasurableEquiv.piCongrLeft, subsetCoordinateEquiv, Equiv.trans_apply,
    MeasurableEquiv.symm_mk, MeasurableEquiv.trans_apply, MeasurableEquiv.coe_mk,
    Equiv.prodCongr_apply, MeasurableEquiv.coe_toEquiv,
    MeasurableEquiv.coe_sumPiEquivProdPi_symm, Equiv.sumPiEquivProdPi, Equiv.symm_mk,
    Equiv.coe_fn_mk, Prod.map_fst, MeasurableEquiv.toLp_symm_apply, Prod.map_snd,
    MeasurableEquiv.toLp_apply, Equiv.piCongrLeft_symm_apply, Equiv.coe_refl,
    Prod.map_apply, Equiv.Set.sumCompl_symm_apply_compl, id_eq, Equiv.sumProdDistrib_apply_right]

/-- Partition a spin assignment into its values on the subset and its complement. -/
@[expose] noncomputable def subsetSpinEquiv {N q : ℕ} (S : Set (Fin N)) :
    ((S → Fin q) × ((Sᶜ : Set (Fin N)) → Fin q)) ≃ SpinLabels N q := by
  classical
  exact (Equiv.sumPiEquivProdPi (fun _ : S ⊕ (Sᶜ : Set (Fin N)) => Fin q)).symm.trans
    (Equiv.piCongrLeft (fun _ : Fin N => Fin q) (Equiv.Set.sumCompl S))

end LiebThirring.Sobolev

end
