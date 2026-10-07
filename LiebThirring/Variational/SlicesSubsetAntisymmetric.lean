/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Variational.SlicesSubset
public import LiebThirring.Variational.SlicesAntisymmetric

/-! # Antisymmetry of arbitrary selected-block slices -/

public section

open MeasureTheory WithLp
open scoped ENNReal Classical
namespace LiebThirring.Variational

private lemma subsetOrderedInsertion_mem {N k : ℕ} (S : Set (Fin N)) (e : Fin k ≃ S)
    (y : SubsetSpectatorConfiguration S) (x : Configuration k) (j : Fin k) (a : Fin 3) :
    subsetOrderedInsertion S e (y, x) ((e j).val, a) = x (j, a) := by
  change Sobolev.subsetInsertionMeasurableEquiv S
    (Sobolev.configurationReindexMeasurableEquiv e x, y) ((e j).val, a) = _
  rw [Sobolev.subsetInsertion_apply_mem]
  simp only [Sobolev.configurationReindexMeasurableEquiv, MeasurableEquiv.trans_apply,
    MeasurableEquiv.toLp_symm_apply, MeasurableEquiv.toLp_apply]
  exact MeasurableEquiv.piCongrLeft_apply_apply
    (β := fun _ : S × Fin 3 => ℝ) (e.prodCongr (Equiv.refl (Fin 3))) x.ofLp (j, a)

private lemma subsetOrderedInsertion_compl {N k : ℕ} (S : Set (Fin N)) (e : Fin k ≃ S)
    (y : SubsetSpectatorConfiguration S) (x : Configuration k)
    (j : (Sᶜ : Set (Fin N))) (a : Fin 3) :
    subsetOrderedInsertion S e (y, x) (j.val, a) = y (j, a) := by
  change Sobolev.subsetInsertionMeasurableEquiv S
    (Sobolev.configurationReindexMeasurableEquiv e x, y) (j.val, a) = _
  exact Sobolev.subsetInsertion_apply_not_mem S _ j a

lemma subsetOrderedSpinEquiv_apply_mem {N k q : ℕ} (S : Set (Fin N))
    (e : Fin k ≃ S) (α : SubsetSpectatorSpins S q) (s : SpinLabels k q)
    (j : Fin k) : subsetOrderedSpinEquiv S e (α, s) (e j) = s j := by
  simp [subsetOrderedSpinEquiv, Sobolev.subsetSpinEquiv,
    Equiv.piCongrLeft, Equiv.piCongrLeft']

lemma subsetOrderedSpinEquiv_apply_compl {N k q : ℕ} (S : Set (Fin N))
    (e : Fin k ≃ S) (α : SubsetSpectatorSpins S q) (s : SpinLabels k q)
    (j : (Sᶜ : Set (Fin N))) : subsetOrderedSpinEquiv S e (α, s) j = α j := by
  simp [subsetOrderedSpinEquiv, Sobolev.subsetSpinEquiv,
    Equiv.piCongrLeft, Equiv.piCongrLeft']

lemma permutePositions_subsetOrderedInsertion {N k : ℕ} (S : Set (Fin N))
    (e : Fin k ≃ S) (σ : Equiv.Perm (Fin k))
    (y : SubsetSpectatorConfiguration S) (x : Configuration k) :
    permutePositions (σ.extendDomain e) (subsetOrderedInsertion S e (y, x)) =
      subsetOrderedInsertion S e (y, permutePositions σ x) := by
  ext ja
  change permutePositions (σ.extendDomain e) (subsetOrderedInsertion S e (y, x)) ja =
    subsetOrderedInsertion S e (y, permutePositions σ x) ja
  by_cases hj : ja.1 ∈ S
  · let j : Fin k := e.symm ⟨ja.1, hj⟩
    have he : e j = ⟨ja.1, hj⟩ := e.apply_symm_apply _
    have hv : (e j).val = ja.1 := congrArg Subtype.val he
    have hp : ((e j).val, ja.2) = ja := Prod.ext hv rfl
    rw [← hp]
    simp [permutePositions, Equiv.Perm.extendDomain_apply_image,
      subsetOrderedInsertion_mem]
  · let jc : (Sᶜ : Set (Fin N)) := ⟨ja.1, hj⟩
    have hfix : σ.extendDomain e ja.1 = ja.1 := by
      apply Equiv.Perm.extendDomain_apply_not_subtype
      simpa using hj
    simp only [permutePositions, PiLp.toLp_apply, hfix]
    exact subsetOrderedInsertion_compl S e y x jc ja.2 |>.trans
      (subsetOrderedInsertion_compl S e y (permutePositions σ x) jc ja.2).symm

lemma permuteSpins_subsetOrderedSpinEquiv {N k q : ℕ} (S : Set (Fin N))
    (e : Fin k ≃ S) (σ : Equiv.Perm (Fin k))
    (α : SubsetSpectatorSpins S q) (s : SpinLabels k q) :
    permuteSpins (σ.extendDomain e) (subsetOrderedSpinEquiv S e (α, s)) =
      subsetOrderedSpinEquiv S e (α, permuteSpins σ s) := by
  funext j
  by_cases hj : j ∈ S
  · let a : Fin k := e.symm ⟨j, hj⟩
    have he : e a = ⟨j, hj⟩ := e.apply_symm_apply _
    have hv : (e a).val = j := congrArg Subtype.val he
    rw [← hv]
    simp [permuteSpins, Equiv.Perm.extendDomain_apply_image,
      subsetOrderedSpinEquiv_apply_mem]
  · let jc : (Sᶜ : Set (Fin N)) := ⟨j, hj⟩
    have hfix : σ.extendDomain e j = j := by
      apply Equiv.Perm.extendDomain_apply_not_subtype
      simpa using hj
    rw [permuteSpins, hfix]
    change subsetOrderedSpinEquiv S e (α, s) jc =
      subsetOrderedSpinEquiv S e (α, permuteSpins σ s) jc
    rw [subsetOrderedSpinEquiv_apply_compl, subsetOrderedSpinEquiv_apply_compl]

end LiebThirring.Variational
end
