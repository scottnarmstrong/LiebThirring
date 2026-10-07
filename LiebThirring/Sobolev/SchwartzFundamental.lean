/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic

/-! # Identification of locally integrable functions by Schwartz inner pairings -/

public section

open MeasureTheory
open scoped SchwartzMap ContDiff

namespace LiebThirring.Sobolev

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- Locally integrable vector functions agreeing on all Schwartz inner pairings agree a.e. -/
theorem ae_eq_of_schwartz_inner_eq {f g : E → F}
    (hf : LocallyIntegrable f) (hg : LocallyIntegrable g)
    (h : ∀ η : 𝓢(E, F), (∫ x, inner ℂ (η x) (f x)) = ∫ x, inner ℂ (η x) (g x)) :
    f =ᵐ[volume] g := by
  apply ae_eq_of_integral_contDiff_smul_eq hf hg
  intro φ hφ hφK
  have hif := hf.integrable_smul_left_of_hasCompactSupport hφ.continuous hφK
  have hig := hg.integrable_smul_left_of_hasCompactSupport hφ.continuous hφK
  apply ext_inner_left ℂ
  intro c
  rw [← integral_inner hif, ← integral_inner hig]
  let η := (HasCompactSupport.smul_right (f' := fun _ => c) hφK).toSchwartzMap
    (hφ.smul contDiff_const)
  have hη : ∀ x, η x = φ x • c := by
    intro x
    exact HasCompactSupport.toSchwartzMap_toFun _ _ x
  have he (k : E → F) :
      (fun x => inner ℂ c (φ x • k x)) = (fun x => inner ℂ (η x) (k x)) := by
    funext x
    rw [hη, inner_smul_left_eq_smul, inner_smul_right_eq_smul]
  rw [he f, he g]
  exact h η

end LiebThirring.Sobolev

end
