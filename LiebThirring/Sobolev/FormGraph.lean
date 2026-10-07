/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Sobolev.WeakGraph

/-!
# The all-coordinate weak Sobolev graph

The zeroth coordinate stores a state and the remaining coordinates store all of its weak spatial
derivatives. The resulting closed linear subspace is a Hilbert space whose squared norm is exactly
the L² mass plus the sum of the squared L² derivative norms.
-/

public section

namespace LiebThirring.Sobolev

/-- The ambient Hilbert sum containing a state and one L² slot for each coordinate derivative. -/
abbrev FormGraphAmbient (N q : ℕ) :=
  PiLp 2 (fun _ : Option (Fin N × Fin 3) ↦ State N q)

/-- The all-coordinate weak derivative graph. -/
@[expose] noncomputable def formGraph (N q : ℕ) : Submodule ℂ (FormGraphAmbient N q) where
  carrier := {v | ∀ a, HasWeakDerivative a (v none) (v (some a))}
  zero_mem' := by
    intro a
    exact (weakDerivativeGraph (q := q) a).zero_mem
  add_mem' := by
    intro v w hv hw a
    have hv' : (v none, v (some a)) ∈ weakDerivativeGraph (q := q) a := hv a
    have hw' : (w none, w (some a)) ∈ weakDerivativeGraph (q := q) a := hw a
    have h := (weakDerivativeGraph (q := q) a).add_mem hv' hw'
    change HasWeakDerivative a (v none + w none) (v (some a) + w (some a)) at h
    exact h
  smul_mem' := by
    intro c v hv a
    have hv' : (v none, v (some a)) ∈ weakDerivativeGraph (q := q) a := hv a
    have h := (weakDerivativeGraph (q := q) a).smul_mem c hv'
    change HasWeakDerivative a (c • v none) (c • v (some a)) at h
    exact h

@[simp]
theorem mem_formGraph {N q : ℕ} {v : FormGraphAmbient N q} :
    v ∈ formGraph N q ↔ ∀ a, HasWeakDerivative a (v none) (v (some a)) := by
  rfl

/-- The all-coordinate weak derivative graph is closed in the ambient Hilbert sum. -/
theorem formGraph_isClosed (N q : ℕ) :
    IsClosed (formGraph N q : Set (FormGraphAmbient N q)) := by
  change IsClosed {v : FormGraphAmbient N q |
    ∀ a, (v none, v (some a)) ∈ weakDerivativeGraph (q := q) a}
  have hclosed := isClosed_iInter fun a ↦
    (weakDerivativeGraph_isClosed (q := q) a).preimage
      ((PiLp.continuous_apply 2 (fun _ : Option (Fin N × Fin 3) ↦ State N q) none).prodMk
        (PiLp.continuous_apply 2 (fun _ : Option (Fin N × Fin 3) ↦ State N q) (some a)))
  rw [show {v : FormGraphAmbient N q |
      ∀ a, (v none, v (some a)) ∈ weakDerivativeGraph (q := q) a} =
      ⋂ a, (fun v : FormGraphAmbient N q ↦ (v none, v (some a))) ⁻¹'
        (weakDerivativeGraph (q := q) a : Set (State N q × State N q)) by
    ext v
    simp only [Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_preimage]
    rfl]
  exact hclosed

/-- The all-coordinate graph is complete in its inherited Hilbert norm. -/
noncomputable instance formGraph.instCompleteSpace (N q : ℕ) : CompleteSpace (formGraph N q) :=
  (formGraph_isClosed N q).completeSpace_coe

/-- The inherited squared Hilbert norm is mass plus the sum of squared derivative norms. -/
theorem formGraph_norm_sq {N q : ℕ} (v : formGraph N q) :
    ‖v‖ ^ 2 = ‖(v : FormGraphAmbient N q) none‖ ^ 2 +
      ∑ a : Fin N × Fin 3, ‖(v : FormGraphAmbient N q) (some a)‖ ^ 2 := by
  rw [show ‖v‖ = ‖(v : FormGraphAmbient N q)‖ by rfl,
    PiLp.norm_sq_eq_of_L2, Fintype.sum_option]

end LiebThirring.Sobolev

end
