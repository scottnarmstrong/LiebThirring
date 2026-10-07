/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Variational.CompactTight
public import LiebThirring.Variational.CompactAttraction

/-! # Compactness and the singular attraction limit on the form domain -/

public section

open MeasureTheory Filter WithLp
open scoped Topology ENNReal NNReal

namespace LiebThirring

/-- The form-domain state together with its unique complete weak-derivative family. -/
@[expose] noncomputable def formDomainGraph {N q : ℕ} (u : FormDomain N q) :
    Sobolev.formGraph N q := (antisymmetricFormGraphEquiv N q).symm u

@[simp] theorem formDomainGraph_state {N q : ℕ} (u : FormDomain N q) :
    ((formDomainGraph u : Sobolev.FormGraphAmbient N q) none) = (u : State N q) := by
  have h := antisymmetricFormGraphEquiv_coe ((antisymmetricFormGraphEquiv N q).symm u)
  simpa only [formDomainGraph, LinearEquiv.apply_symm_apply] using h.symm

/-- The graph Hilbert norm agrees exactly with the existing Fourier form norm. -/
@[simp] theorem norm_formDomainGraph {N q : ℕ} (u : FormDomain N q) :
    ‖formDomainGraph u‖ = formGraphNorm u := by
  rw [← Real.sqrt_sq (norm_nonneg (formDomainGraph u)),
    Sobolev.formGraph_norm_sq_eq_mass_add_kineticEnergy, formDomainGraph_state]
  rfl

/-- A bounded particle-tight sequence in the form domain has a limit in that same
form domain, weakly in the graph and strongly in global L², with the kinetic liminf bound. -/
theorem exists_formDomain_subsequence_of_particle_tight {N q : ℕ}
    (u : ℕ → FormDomain N q) (K : ℝ) (hK : ∀ n, formGraphNorm (u n) ≤ K)
    (htight : Tendsto (fun R : ℝ => limsup (fun n =>
      ∫ x in {x : Configuration N | ∃ i : Fin N, R < ‖particlePosition x i‖},
        ‖(u n : State N q) x‖ ^ 2) atTop) atTop (𝓝 0)) :
    ∃ v : FormDomain N q, formGraphNorm v ≤ K ∧ ∃ φ : ℕ → ℕ, StrictMono φ ∧
      (∀ w : Sobolev.formGraph N q,
        Tendsto (fun n => inner ℂ (formDomainGraph (u (φ n))) w) atTop
          (𝓝 (inner ℂ (formDomainGraph v) w))) ∧
      Tendsto (fun n => (u (φ n) : State N q)) atTop (𝓝 (v : State N q)) ∧
      (kineticEnergy (v : State N q)).toReal ≤
        liminf (fun n => (kineticEnergy (u (φ n) : State N q)).toReal) atTop := by
  have hbound (n : ℕ) : ‖formDomainGraph (u n)‖ ≤ K := by
    simpa only [norm_formDomainGraph] using hK n
  have ht : Tendsto (fun R : ℝ => limsup (fun n =>
      ∫ x in {x : Configuration N | ∃ i : Fin N, R < ‖particlePosition x i‖},
        ‖(formDomainGraph (u n) : Sobolev.FormGraphAmbient N q) none x‖ ^ 2) atTop) atTop (𝓝 0) := by
    simpa only [formDomainGraph_state] using htight
  obtain ⟨g, hg, φ, hφ, hweak, hstrong⟩ :=
    exists_formGraph_subsequence_of_particle_tight (fun n => formDomainGraph (u n)) K hbound ht
  have hanti : antisymmetric ((g : Sobolev.FormGraphAmbient N q) none) :=
    antisymmetric_of_tendsto_inner (tendsto_inner_formGraph_coordinate hweak none)
      (fun n => by simpa only [formDomainGraph_state] using (u (φ n)).property.1)
  let ga : antisymmetricFormGraph N q := ⟨g, hanti⟩
  let v : FormDomain N q := antisymmetricFormGraphEquiv N q ga
  have hvg : formDomainGraph v = g := by
    change (((antisymmetricFormGraphEquiv N q).symm
      (antisymmetricFormGraphEquiv N q ga) : antisymmetricFormGraph N q) : Sobolev.formGraph N q) = g
    rw [LinearEquiv.symm_apply_apply]
  refine ⟨v, ?_, φ, hφ, ?_, ?_, ?_⟩
  · rw [← norm_formDomainGraph, hvg]
    exact hg
  · simpa only [hvg] using hweak
  · simpa only [← hvg, formDomainGraph_state] using hstrong
  · have h := kineticEnergy_le_liminf_of_formGraph_weak hweak K (fun n => hbound (φ n))
    simpa only [← hvg, formDomainGraph_state] using h

/-- Strong L² convergence of a form-norm bounded sequence gives the full singular attraction
limit, with all finite-energy and second-moment assumptions discharged by the form domain. -/
theorem tendsto_attraction_expectation_of_form_bounded {N q M : ℕ}
    (z : Fin M → ℝ≥0) (R : Fin M → Position)
    {u : ℕ → FormDomain N q} {v : FormDomain N q}
    (hu : Tendsto (fun n => (u n : State N q)) atTop (𝓝 (v : State N q)))
    (K : ℝ) (hK : ∀ n, formGraphNorm (u n) ≤ K) :
    Tendsto (fun n => (∫⁻ x : Configuration N,
      attraction z R x * (‖(u n : State N q) x‖₊ : ℝ≥0∞) ^ 2).toReal) atTop
      (𝓝 (∫⁻ x : Configuration N,
        attraction z R x * (‖(v : State N q) x‖₊ : ℝ≥0∞) ^ 2).toReal) := by
  apply tendsto_attraction_expectation_of_tendsto_Lp z R hu
    (fun n => (u n).property.2) v.property.2 (K ^ 2)
  intro n
  calc
    _ ≤ formGraphNorm (u n) ^ 2 := by
      rw [formGraphNorm_sq]
      exact le_add_of_nonneg_left (sq_nonneg _)
    _ ≤ K ^ 2 := pow_le_pow_left₀ (formGraphNorm_nonneg _) (hK n) 2

end LiebThirring
end
