/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Sobolev.FormGraph
public import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Normed.Module.WeakDual

/-! # Weak subsequence extraction in the form Hilbert graph

The weak extraction part of the compact extraction. Restricting to the closed span of the sequence
avoids any separability assumption on the ambient Hilbert space.
-/

public section

open Filter Topology

namespace LiebThirring

private theorem exists_weak_subsequence_separable {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [TopologicalSpace.SeparableSpace E] (u : ℕ → E) (K : ℝ)
    (hu : ∀ n, ‖u n‖ ≤ K) :
    ∃ v : E, ‖v‖ ≤ K ∧ ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ w : E, Tendsto (fun n => inner ℂ (u (φ n)) w) atTop (𝓝 (inner ℂ v w)) := by
  let f : ℕ → WeakDual ℂ E := fun n =>
    StrongDual.toWeakDual (InnerProductSpace.toDual ℂ E (u n))
  have hf (n : ℕ) : f n ∈ WeakDual.toStrongDual ⁻¹' Metric.closedBall
      (0 : StrongDual ℂ E) K := by
    change dist (InnerProductSpace.toDual ℂ E (u n)) 0 ≤ K
    rw [dist_zero_right, LinearIsometryEquiv.norm_map]
    exact hu n
  obtain ⟨a, ha, φ, hφ, hlim⟩ := (WeakDual.isSeqCompact_closedBall
    (𝕜 := ℂ) (E := E) 0 K) hf
  let v := (InnerProductSpace.toDual ℂ E).symm (WeakDual.toStrongDual a)
  refine ⟨v, ?_, φ, hφ, ?_⟩
  · simpa only [Set.mem_preimage, Metric.mem_closedBall, dist_zero_right,
      v, LinearIsometryEquiv.norm_map] using ha
  · intro w
    have h := (WeakDual.eval_continuous w).tendsto a |>.comp hlim
    change Tendsto (fun n => inner ℂ (u (φ n)) w) atTop (𝓝 (a w)) at h
    simpa only [v, InnerProductSpace.toDual_symm_apply, WeakDual.toStrongDual_apply] using h

/-- Every bounded sequence in a complex Hilbert space admits a weakly convergent subsequence.
The limit remains in the same closed ball, including when the ambient space is nonseparable. -/
theorem exists_weak_subsequence {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (u : ℕ → E) (K : ℝ) (hu : ∀ n, ‖u n‖ ≤ K) :
    ∃ v : E, ‖v‖ ≤ K ∧ ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ w : E, Tendsto (fun n => inner ℂ (u (φ n)) w) atTop (𝓝 (inner ℂ v w)) := by
  let S := (Submodule.span ℂ (Set.range u)).topologicalClosure
  have hclosed : IsClosed (S : Set E) := Submodule.isClosed_topologicalClosure _
  let : CompleteSpace S := hclosed.completeSpace_coe
  have hsep : TopologicalSpace.IsSeparable (S : Set E) := by
    change TopologicalSpace.IsSeparable
      ((Submodule.span ℂ (Set.range u)).topologicalClosure : Set E)
    rw [Submodule.topologicalClosure_coe]
    exact (Set.countable_range u).isSeparable.span.closure
  let : TopologicalSpace.SeparableSpace S := hsep.separableSpace
  let us : ℕ → S := fun n => ⟨u n,
    Submodule.le_topologicalClosure _ (Submodule.subset_span (Set.mem_range_self n))⟩
  obtain ⟨v, hv, φ, hφ, hlim⟩ := exists_weak_subsequence_separable us K hu
  refine ⟨v, hv, φ, hφ, ?_⟩
  intro w
  simpa only [Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left, us]
    using hlim (S.orthogonalProjectionOnto w)

/-- Compact extraction weak extraction on the state and weak-derivative carriers, with no condition
on particle number, spin number, normalization, or antisymmetry. -/
theorem exists_formGraph_weak_subsequence {N q : ℕ}
    (u : ℕ → Sobolev.formGraph N q) (K : ℝ) (hu : ∀ n, ‖u n‖ ≤ K) :
    ∃ v : Sobolev.formGraph N q, ‖v‖ ≤ K ∧ ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ w : Sobolev.formGraph N q,
        Tendsto (fun n => inner ℂ (u (φ n)) w) atTop (𝓝 (inner ℂ v w)) :=
  exists_weak_subsequence u K hu

/-- Bounded linear maps preserve weak convergence of Hilbert-space sequences. -/
theorem tendsto_inner_map_of_tendsto_inner {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    {u : ℕ → E} {v : E}
    (hu : ∀ w : E, Tendsto (fun n => inner ℂ (u n) w) atTop (𝓝 (inner ℂ v w)))
    (A : E →L[ℂ] F) (w : F) :
    Tendsto (fun n => inner ℂ (A (u n)) w) atTop (𝓝 (inner ℂ (A v) w)) := by
  simpa only [ContinuousLinearMap.adjoint_inner_right] using hu (A.adjoint w)

/-- Every state or derivative coordinate inherits weak convergence from the form graph. -/
theorem tendsto_inner_formGraph_coordinate {N q : ℕ}
    {u : ℕ → Sobolev.formGraph N q} {v : Sobolev.formGraph N q}
    (hu : ∀ w : Sobolev.formGraph N q,
      Tendsto (fun n => inner ℂ (u n) w) atTop (𝓝 (inner ℂ v w)))
    (a : Option (Fin N × Fin 3)) (w : State N q) :
    Tendsto (fun n => inner ℂ ((u n : Sobolev.FormGraphAmbient N q) a) w) atTop
      (𝓝 (inner ℂ ((v : Sobolev.FormGraphAmbient N q) a) w)) := by
  exact tendsto_inner_map_of_tendsto_inner hu
    ((PiLp.proj 2 (fun _ : Option (Fin N × Fin 3) => State N q) a).comp
      (Sobolev.formGraph N q).subtypeL) w

end LiebThirring

end
