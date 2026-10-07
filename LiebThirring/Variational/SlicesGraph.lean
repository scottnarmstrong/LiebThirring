/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Sobolev.WeakEnergy
public import LiebThirring.Sobolev.FormDensityPermutation
public import LiebThirring.Variational.FormBounds

/-!
# The antisymmetric weak Sobolev graph

This module realizes the finite-energy form domain as the antisymmetric closed subspace of
the all-coordinate weak derivative graph. Its inherited norm is the kinetic form graph norm;
the subtype itself continues to carry its inherited L² norm.
-/

public section

open MeasureTheory WithLp

namespace LiebThirring

open Sobolev

/-- Antisymmetry is equivalently the signed fixed-point condition for every simultaneous
particle permutation. -/
theorem antisymmetric_iff_simultaneousPermutation_eq {N q : ℕ} (u : State N q) :
    antisymmetric u ↔ ∀ σ : Equiv.Perm (Fin N),
      simultaneousPermutation σ u = ((((Equiv.Perm.sign σ : ℤˣ) : ℤ) : ℂ)) • u := by
  constructor
  · exact fun hu σ ↦ simultaneousPermutation_eq_sign_smul σ u hu
  · intro h σ
    filter_upwards [simultaneousPermutation_apply_ae σ u,
      Lp.coeFn_smul ((((Equiv.Perm.sign σ : ℤˣ) : ℤ) : ℂ)) u] with x hx hs
    intro s
    rw [← hx s, h σ, hs]
    rfl

/-- The states in the all-coordinate weak graph whose zeroth component is antisymmetric. -/
@[expose] noncomputable def antisymmetricFormGraph (N q : ℕ) :
    Submodule ℂ (formGraph N q) where
  carrier := {v : formGraph N q | antisymmetric ((v : FormGraphAmbient N q) none)}
  zero_mem' := by
    change antisymmetric (0 : State N q)
    exact formDomain_zero_mem.1
  add_mem' := by
    intro v w hv hw
    change antisymmetric ((v : FormGraphAmbient N q) none) at hv
    change antisymmetric ((w : FormGraphAmbient N q) none) at hw
    change antisymmetric
      (((v : FormGraphAmbient N q) none) + ((w : FormGraphAmbient N q) none))
    exact antisymmetric_add hv hw
  smul_mem' := by
    intro c v hv
    change antisymmetric ((v : FormGraphAmbient N q) none) at hv
    change antisymmetric (c • ((v : FormGraphAmbient N q) none))
    exact antisymmetric_smul c hv

@[simp]
theorem mem_antisymmetricFormGraph {N q : ℕ} {v : formGraph N q} :
    v ∈ antisymmetricFormGraph N q ↔ antisymmetric ((v : FormGraphAmbient N q) none) := by
  rw [antisymmetricFormGraph]
  rfl

/-- Projection of the antisymmetric weak graph to the form domain. -/
noncomputable def antisymmetricFormGraphToFormDomain (N q : ℕ) :
    antisymmetricFormGraph N q →ₗ[ℂ] FormDomain N q where
  toFun v := ⟨((v : formGraph N q) : FormGraphAmbient N q) none,
    (mem_antisymmetricFormGraph.mp v.property),
    (kineticEnergy_lt_top_iff_exists_weakDerivatives _).2
      ⟨fun a ↦ ((v : formGraph N q) : FormGraphAmbient N q) (some a),
        mem_formGraph.mp (v : formGraph N q).property⟩⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem antisymmetricFormGraphToFormDomain_injective (N q : ℕ) :
    Function.Injective (antisymmetricFormGraphToFormDomain N q) := by
  intro v w hvw
  have hstate : ((v : formGraph N q) : FormGraphAmbient N q) none =
      ((w : formGraph N q) : FormGraphAmbient N q) none := congrArg Subtype.val hvw
  apply Subtype.ext
  apply Subtype.ext
  apply PiLp.ext
  intro a
  cases a with
  | none => exact hstate
  | some a =>
      exact HasWeakDerivative.unique
        ((mem_formGraph.mp (v : formGraph N q).property) a)
        (by rw [hstate]; exact (mem_formGraph.mp (w : formGraph N q).property) a)

theorem antisymmetricFormGraphToFormDomain_surjective (N q : ℕ) :
    ∀ u : FormDomain N q, ∃ v : antisymmetricFormGraph N q,
      antisymmetricFormGraphToFormDomain N q v = u := by
  intro u
  have hu : kineticEnergy (u : State N q) < ⊤ := u.property.2
  obtain ⟨g, hg⟩ := exists_weakDerivatives_of_kineticEnergy_lt_top (u : State N q) hu
  let v : FormGraphAmbient N q := toLp 2 (fun a ↦ match a with
    | none => u
    | some a => g a)
  have hv : v ∈ formGraph N q := by
    rw [mem_formGraph]
    intro a
    simpa [v] using hg a
  have hanti : antisymmetric (v none) := by
    simpa [v] using u.property.1
  refine ⟨⟨⟨v, hv⟩, hanti⟩, ?_⟩
  apply Subtype.ext
  change v none = (u : State N q)
  simp [v]

/-- Linear identification of the complete antisymmetric weak graph with the carrier. -/
@[expose] noncomputable def antisymmetricFormGraphEquiv (N q : ℕ) :
    antisymmetricFormGraph N q ≃ₗ[ℂ] FormDomain N q :=
  LinearEquiv.ofBijective (antisymmetricFormGraphToFormDomain N q)
    ⟨antisymmetricFormGraphToFormDomain_injective N q,
      antisymmetricFormGraphToFormDomain_surjective N q⟩

@[simp]
theorem antisymmetricFormGraphEquiv_coe {N q : ℕ} (v : antisymmetricFormGraph N q) :
    ((antisymmetricFormGraphEquiv N q v : FormDomain N q) : State N q) =
      ((v : formGraph N q) : FormGraphAmbient N q) none := by
  rfl

end LiebThirring

end
