/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic

/-! # Compact support for finite Schwartz operations -/

public section

open scoped SchwartzMap

namespace LiebThirring.Sobolev

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F]

/-- Constant scalar multiplication preserves compact support of Schwartz functions. -/
theorem hasCompactSupport_schwartz_smul (c : ℂ) (f : 𝓢(E, F)) (hf : HasCompactSupport f) :
    HasCompactSupport (c • f : 𝓢(E, F)) :=
  hf.comp_left (smul_zero c)

omit [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F] in
/-- A finite sum of compactly supported Schwartz functions has compact support. -/
theorem hasCompactSupport_schwartz_finsetSum {ι : Type*} (s : Finset ι) (f : ι → 𝓢(E, F))
    (hf : ∀ i ∈ s, HasCompactSupport (f i)) : HasCompactSupport (∑ i ∈ s, f i : 𝓢(E, F)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty]
    change HasCompactSupport (0 : E → F)
    exact HasCompactSupport.zero
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (hf a (Finset.mem_insert_self a s)).add
      (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)))

end LiebThirring.Sobolev

end
