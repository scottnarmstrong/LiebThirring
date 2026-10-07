/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Variational.CompactWeak
public import LiebThirring.Variational.SlicesGraph

/-! # Weak lower semicontinuity and almost-everywhere subsequences

Auxiliary parts of the compact extraction. These statements do not assert local compactness.
-/

public section

open Filter Topology MeasureTheory

namespace LiebThirring

/-- The Hilbert norm is lower semicontinuous along a bounded weakly convergent sequence. -/
theorem norm_le_liminf_of_tendsto_inner {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {u : ℕ → E} {v : E}
    (hu : ∀ w : E, Tendsto (fun n => inner ℂ (u n) w) atTop (𝓝 (inner ℂ v w)))
    (K : ℝ) (hK : ∀ n, ‖u n‖ ≤ K) :
    ‖v‖ ≤ liminf (fun n => ‖u n‖) atTop := by
  have hlo : IsBoundedUnder (· ≥ ·) atTop (fun n => ‖u n‖) := by
    refine ⟨0, ?_⟩
    change ∀ᶠ n : ℕ in atTop, 0 ≤ ‖u n‖
    exact Eventually.of_forall fun n => norm_nonneg _
  have hhi : IsBoundedUnder (· ≤ ·) atTop (fun n => ‖u n‖) := by
    refine ⟨K, ?_⟩
    change ∀ᶠ n : ℕ in atTop, ‖u n‖ ≤ K
    exact Eventually.of_forall hK
  by_cases hv : ‖v‖ = 0
  · rw [hv]
    exact le_liminf_of_le hhi.isCoboundedUnder_ge (Eventually.of_forall fun n => norm_nonneg _)
  · have hvpos : 0 < ‖v‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hv)
    have hlim : Tendsto (fun n => (inner ℂ (u n) v).re / ‖v‖) atTop (𝓝 ‖v‖) := by
      have h := (Complex.continuous_re.tendsto _ |>.comp (hu v)).div_const ‖v‖
      have he : (inner ℂ v v).re = ‖v‖ ^ 2 := by
        simpa only [RCLike.re_to_complex] using (norm_sq_eq_re_inner (𝕜 := ℂ) v).symm
      rw [he] at h
      simpa only [Function.comp_apply, pow_two, mul_div_cancel_right₀ _ hv] using h
    have hle (n : ℕ) : (inner ℂ (u n) v).re / ‖v‖ ≤ ‖u n‖ := by
      apply (div_le_iff₀ hvpos).mpr
      exact (Complex.re_le_norm _).trans (norm_inner_le_norm _ _)
    rw [← hlim.liminf_eq]
    exact liminf_le_liminf (Eventually.of_forall hle)
      hlim.isBoundedUnder_ge hhi.isCoboundedUnder_ge

/-- The squared norm has the same weak lower semicontinuity, without exchanging a
conditionally defined real liminf with squaring outside its nonnegative range. -/
theorem norm_sq_le_liminf_of_tendsto_inner {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {u : ℕ → E} {v : E}
    (hu : ∀ w : E, Tendsto (fun n => inner ℂ (u n) w) atTop (𝓝 (inner ℂ v w)))
    (K : ℝ) (hK : ∀ n, ‖u n‖ ≤ K) :
    ‖v‖ ^ 2 ≤ liminf (fun n => ‖u n‖ ^ 2) atTop := by
  have h := norm_le_liminf_of_tendsto_inner hu K hK
  have hnonneg : 0 ≤ liminf (fun n => ‖u n‖) atTop := (norm_nonneg _).trans h
  have hlo : IsBoundedUnder (· ≥ ·) atTop (fun n => ‖u n‖) := by
    refine ⟨0, ?_⟩
    change ∀ᶠ n : ℕ in atTop, 0 ≤ ‖u n‖
    exact Eventually.of_forall fun n => norm_nonneg _
  have hhi : IsBoundedUnder (· ≤ ·) atTop (fun n => ‖u n‖) := by
    refine ⟨K, ?_⟩
    change ∀ᶠ n : ℕ in atTop, ‖u n‖ ≤ K
    exact Eventually.of_forall hK
  have hm : Monotone (fun r : ℝ => max r 0 ^ 2) := by
    intro a b hab
    exact pow_le_pow_left₀ (le_max_right _ _) (max_le_max hab le_rfl) 2
  have hc : Continuous (fun r : ℝ => max r 0 ^ 2) :=
    (continuous_id.max continuous_const).pow 2
  have he := hm.map_liminf_of_continuousAt (F := atTop) (fun n => ‖u n‖)
    hc.continuousAt hhi.isCoboundedUnder_ge hlo
  change max (liminf (fun n => ‖u n‖) atTop) 0 ^ 2 =
    liminf (fun n => max ‖u n‖ 0 ^ 2) atTop at he
  simp only [max_eq_left hnonneg, max_eq_left (norm_nonneg _)] at he
  rw [← he]
  exact pow_le_pow_left₀ (norm_nonneg _) h 2

/-- The complete weak derivative family as a bounded linear map from the form graph. -/
@[expose] noncomputable def formGraphGradientCLM (N q : ℕ) :
    Sobolev.formGraph N q →L[ℂ] PiLp 2 (fun _ : Fin N × Fin 3 => State N q) :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin N × Fin 3 => State N q)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun a =>
      (PiLp.proj 2 (fun _ : Option (Fin N × Fin 3) => State N q) (some a)).comp
        (Sobolev.formGraph N q).subtypeL)

/-- The gradient family's squared norm is the physical kinetic energy. -/
theorem norm_formGraphGradientCLM_sq {N q : ℕ} (v : Sobolev.formGraph N q) :
    ‖formGraphGradientCLM N q v‖ ^ 2 =
      (kineticEnergy ((v : Sobolev.FormGraphAmbient N q) none)).toReal := by
  rw [PiLp.norm_sq_eq_of_L2]
  simp only [formGraphGradientCLM]
  exact (Sobolev.kineticEnergy_toReal_eq_sum_weakDerivative_norm_sq _ _
    (Sobolev.mem_formGraph.mp v.property)).symm

/-- Compact extraction kinetic lower semicontinuity along bounded sequences weakly converging in the
actual form Hilbert graph. The limit energy remains the Fourier energy. -/
theorem kineticEnergy_le_liminf_of_formGraph_weak {N q : ℕ}
    {u : ℕ → Sobolev.formGraph N q} {v : Sobolev.formGraph N q}
    (hu : ∀ w : Sobolev.formGraph N q,
      Tendsto (fun n => inner ℂ (u n) w) atTop (𝓝 (inner ℂ v w)))
    (K : ℝ) (hK : ∀ n, ‖u n‖ ≤ K) :
    (kineticEnergy ((v : Sobolev.FormGraphAmbient N q) none)).toReal ≤
      liminf (fun n => (kineticEnergy ((u n : Sobolev.FormGraphAmbient N q) none)).toReal) atTop := by
  have hbound (n : ℕ) : ‖formGraphGradientCLM N q (u n)‖ ≤
      ‖formGraphGradientCLM N q‖ * K :=
    (formGraphGradientCLM N q).le_opNorm (u n) |>.trans
      (mul_le_mul_of_nonneg_left (hK n) (norm_nonneg (formGraphGradientCLM N q)))
  have h := norm_sq_le_liminf_of_tendsto_inner
    (tendsto_inner_map_of_tendsto_inner hu (formGraphGradientCLM N q)) _ hbound
  simpa only [norm_formGraphGradientCLM_sq] using h

/-- A bounded linear constraint passes to a weak limit. -/
theorem map_eq_zero_of_tendsto_inner {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    {u : ℕ → E} {v : E}
    (hu : ∀ w : E, Tendsto (fun n => inner ℂ (u n) w) atTop (𝓝 (inner ℂ v w)))
    (A : E →L[ℂ] F) (hA : ∀ n, A (u n) = 0) : A v = 0 := by
  apply ext_inner_right ℂ
  intro w
  have h := tendsto_inner_map_of_tendsto_inner hu A w
  simp only [hA, inner_zero_left] at h
  exact (tendsto_nhds_unique tendsto_const_nhds h).symm.trans (inner_zero_left _).symm

/-- The antisymmetry predicate is preserved by global weak L² convergence. -/
theorem antisymmetric_of_tendsto_inner {N q : ℕ} {u : ℕ → State N q} {v : State N q}
    (hu : ∀ w : State N q,
      Tendsto (fun n => inner ℂ (u n) w) atTop (𝓝 (inner ℂ v w)))
    (hanti : ∀ n, antisymmetric (u n)) : antisymmetric v := by
  rw [antisymmetric_iff_simultaneousPermutation_eq]
  intro σ
  let c : ℂ := (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : ℂ)
  let A := Sobolev.permutationStateCLM (q := q) σ -
    c • ContinuousLinearMap.id ℂ (State N q)
  have hA (n : ℕ) : A (u n) = 0 := by
    change simultaneousPermutation σ (u n) - c • u n = 0
    rw [(antisymmetric_iff_simultaneousPermutation_eq _).mp (hanti n) σ, sub_self]
  have h := map_eq_zero_of_tendsto_inner hu A hA
  change simultaneousPermutation σ v - c • v = 0 at h
  exact sub_eq_zero.mp h

/-- A globally strongly convergent state sequence has an a.e. convergent subsequence. -/
theorem exists_state_subsequence_tendsto_ae {N q : ℕ} {u : ℕ → State N q} {v : State N q}
    (hu : Tendsto u atTop (𝓝 v)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ᵐ x ∂(volume : Measure (Configuration N)),
      Tendsto (fun n => u (φ n) x) atTop (𝓝 (v x)) :=
  (tendstoInMeasure_of_tendsto_Lp hu).exists_seq_tendsto_ae

end LiebThirring

end
