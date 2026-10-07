/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFCubes.LocalWeakDerivative
public import LiebThirring.Variational.SlicesSmooth

/-! # Weak derivatives under volume-preserving linear coordinates -/

@[expose] public section

open MeasureTheory Set
open scoped ContDiff

namespace LiebThirring.TFProduct

open LiebThirring TFCubes

variable {E H F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasureSpace E] [BorelSpace E]
  [NormedAddCommGroup H] [NormedSpace ℝ H]
  [MeasureSpace H] [BorelSpace H]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]

/-- Pullback by a continuous linear equivalence between two specified
restricted measures transforms the weak direction by the inverse equivalence. -/
theorem HasWeakDerivativeOn.continuousLinearEquiv_pullback_restrict
    (e : E ≃L[ℝ] H) {Ω : Set H} {Ω' : Set E}
    (hpre : e ⁻¹' Ω = Ω')
    (heR : MeasurePreserving e (volume.restrict Ω') (volume.restrict Ω))
    {v : H} {u g : RegionState H F Ω}
    (h : HasWeakDerivativeOn Ω v u g) :
    HasWeakDerivativeOn Ω' (e.symm v)
      (Lp.compMeasurePreserving e heR u)
      (Lp.compMeasurePreserving e heR g) := by
  intro η hc hs hsupp
  let A := e.symm.toContinuousLinearMap
  have hcs : HasCompactSupport (η ∘ e.symm) :=
    hc.comp_homeomorph e.symm.toHomeomorph
  have hss : ContDiff ℝ ∞ (η ∘ e.symm) := hs.comp A.contDiff
  have hsu : tsupport (η ∘ e.symm) ⊆ Ω := by
    intro y hy
    have hy' := hsupp ((tsupport_comp_subset_preimage η e.symm.continuous) hy)
    have hy'' : e.symm y ∈ e ⁻¹' Ω := by
      rw [hpre]
      exact hy'
    simpa only [Set.mem_preimage, ContinuousLinearEquiv.apply_symm_apply] using hy''
  have hd (y : H) : fderiv ℝ (η ∘ e.symm) y v =
      fderiv ℝ η (e.symm y) (e.symm v) := by
    have hf := (((hs.differentiable (by simp)).differentiableAt).hasFDerivAt.comp y
      A.hasFDerivAt).fderiv
    change fderiv ℝ (η ∘ A) y v = fderiv ℝ η (A y) (A v)
    rw [hf]
    rfl
  have hw := h (η ∘ e.symm) hcs hss hsu
  have hpair (ψ : E → F) (w : RegionState H F Ω) :
      (∫ x in Ω', inner ℂ (ψ x) (Lp.compMeasurePreserving e heR w x)) =
        ∫ y in Ω, inner ℂ (ψ (e.symm y)) (w y) := by
    calc
      _ = ∫ x in Ω', inner ℂ (ψ x) (w (e x)) := by
        apply integral_congr_ae
        filter_upwards [Lp.coeFn_compMeasurePreserving w heR] with x hx
        rw [hx]
        rfl
      _ = _ := by
        have hi := heR.integral_comp e.toHomeomorph.measurableEmbedding
          (fun y => inner ℂ (ψ (e.symm y)) (w y))
        simpa only [ContinuousLinearEquiv.symm_apply_apply] using hi
  rw [hpair η g, hpair (fun x => fderiv ℝ η x (e.symm v)) u]
  simpa only [Function.comp_apply, hd] using hw

/-- Particle insertion as a continuous linear equivalence from the ordinary
product carrier used by Fubini and contraction arguments. -/
noncomputable def insertionContinuousLinearEquiv {N : ℕ} (i : Fin N) :
    (Position × OtherConfiguration i) ≃L[ℝ] Configuration N :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ Position (OtherConfiguration i)).symm.trans
    (LiebThirring.Variational.configurationInsertionLinearIsometryEquiv i).toContinuousLinearEquiv

@[simp] theorem insertionContinuousLinearEquiv_apply {N : ℕ} (i : Fin N)
    (z : Position × OtherConfiguration i) :
    insertionContinuousLinearEquiv i z = insertParticle i z.1 z.2 := by
  change LiebThirring.Variational.configurationInsertionLinearIsometryEquiv i
    (WithLp.toLp 2 z) = _
  rw [LiebThirring.Variational.configurationInsertionLinearIsometryEquiv_apply]

/-- The ordinary-product continuous linear insertion coordinates preserve
Lebesgue volume. -/
theorem measurePreserving_insertionContinuousLinearEquiv {N : ℕ} (i : Fin N) :
    MeasurePreserving (insertionContinuousLinearEquiv i) volume volume := by
  have hf : (insertionContinuousLinearEquiv i :
      Position × OtherConfiguration i → Configuration N) = insertionMeasurableEquiv i := by
    funext z
    rw [insertionContinuousLinearEquiv_apply, insertionMeasurableEquiv_apply]
  rw [hf]
  exact measurePreserving_insertion i

end LiebThirring.TFProduct

end
