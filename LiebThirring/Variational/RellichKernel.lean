/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Variational.CompactMass
public import LiebThirring.Variational.CompactWeak
public import LiebThirring.Sobolev.MultiplierContinuity
public import LiebThirring.Fourier.IntegralL2

/-! # Finite-frequency inverse integral compactness

Finite-measure frequency cutoffs turn weak L² convergence into strong local L² convergence.
The proof uses finite-dimensionality of the spin fiber and dominated convergence.
-/

public section

open MeasureTheory Filter WithLp
open scoped Topology FourierTransform ENNReal NNReal

namespace LiebThirring

/-- L² functions are integrable on every finite-measure set. -/
theorem state_integrableOn {N q : ℕ} (u : State N q)
    (s : Set (Configuration N)) (hμ : volume s ≠ ⊤) : IntegrableOn u s := by
  let : IsFiniteMeasure (volume.restrict s) := ⟨by simpa using hμ.lt_top⟩
  exact ((Lp.memLp u).mono_measure Measure.restrict_le_self).integrable (by norm_num)

/-- Cauchy--Schwarz bounds the L¹ norm on a finite-measure set. -/
theorem integral_state_norm_on_le {N q : ℕ} (u : State N q)
    (s : Set (Configuration N)) (hs : MeasurableSet s) (hμ : volume s ≠ ⊤) :
    (∫ x in s, ‖u x‖) ≤ Real.sqrt (volume s).toReal * ‖u‖ := by
  let a : Configuration N → ℝ := s.indicator (fun _ => 1)
  have ha : MemLp a 2 volume := memLp_indicator_const 2 hs 1 (Or.inr hμ)
  have hb : MemLp (fun x => ‖u x‖) 2 volume := (Lp.memLp u).norm
  have h := integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two
    (show MemLp a (ENNReal.ofReal 2) volume by simpa using ha)
    (show MemLp (fun x => ‖u x‖) (ENNReal.ofReal 2) volume by simpa using hb)
  have hpow : (fun x => ‖a x‖ ^ (2 : ℝ)) = a := by
    funext x
    by_cases hx : x ∈ s <;> simp [a, hx]
  have hmul : (fun x => ‖a x‖ * ‖‖u x‖‖) = s.indicator (fun x => ‖u x‖) := by
    funext x
    by_cases hx : x ∈ s <;> simp [a, hx]
  rw [hmul, integral_indicator hs, hpow] at h
  change (∫ x in s, ‖u x‖) ≤ (∫ x, s.indicator (fun _ => (1 : ℝ)) x) ^ (1 / 2 : ℝ) * _ at h
  rw [integral_indicator hs] at h
  simp only [integral_const, Measure.restrict_apply_univ, smul_eq_mul, mul_one, measureReal_def] at h
  simp only [norm_norm] at h
  simpa only [← Real.sqrt_eq_rpow, Real.rpow_two, integral_state_norm_sq,
    Real.sqrt_sq (norm_nonneg u)] using h

/-- Integration over a finite-measure spatial set, as a bounded linear map on L². -/
@[expose] noncomputable def stateSetIntegralCLM {N q : ℕ}
    (s : Set (Configuration N)) (hs : MeasurableSet s) (hμ : volume s ≠ ⊤) :
    State N q →L[ℂ] SpinAmplitudes N q :=
  LinearMap.mkContinuous
    { toFun := fun u => ∫ x in s, u x
      map_add' := fun u v => by
        calc
          (∫ x in s, (u + v) x) = ∫ x in s, u x + v x :=
            integral_congr_ae ((Lp.coeFn_add u v).filter_mono (ae_mono Measure.restrict_le_self))
          _ = _ := integral_add (state_integrableOn u s hμ) (state_integrableOn v s hμ)
      map_smul' := fun c u => by
        calc
          (∫ x in s, (c • u) x) = ∫ x in s, c • u x :=
            integral_congr_ae ((Lp.coeFn_smul c u).filter_mono (ae_mono Measure.restrict_le_self))
          _ = _ := integral_smul c _ }
    (Real.sqrt (volume s).toReal)
    (fun u => (norm_integral_le_integral_norm _).trans (integral_state_norm_on_le u s hs hμ))

/-- Weak convergence in the finite spin space implies norm convergence. -/
theorem tendsto_spin_of_tendsto_inner {N q : ℕ} {u : ℕ → SpinAmplitudes N q}
    {v : SpinAmplitudes N q}
    (h : ∀ w, Tendsto (fun n => inner ℂ (u n) w) atTop (𝓝 (inner ℂ v w))) :
    Tendsto u atTop (𝓝 v) := by
  have hc (i : SpinLabels N q) : Tendsto (fun n => u n i) atTop (𝓝 (v i)) := by
    have hi := (Complex.continuous_conj.tendsto _).comp (h (EuclideanSpace.single i 1))
    simp only [EuclideanSpace.inner_single_right, one_mul] at hi
    change Tendsto (fun n => star (star (u n i))) atTop (𝓝 (star (star (v i)))) at hi
    simpa only [star_star] using hi
  have hp := tendsto_pi_nhds.mpr hc
  exact ((PiLp.continuousLinearEquiv 2 ℂ (fun _ : SpinLabels N q => ℂ)).symm.continuous.tendsto _).comp hp

/-- The continuous representative of a finite-frequency inverse Fourier transform. -/
@[expose] noncomputable def inverseCutoffIntegral {N q : ℕ}
    (s : Set (Configuration N)) (u : State N q) : Configuration N → SpinAmplitudes N q :=
  𝓕⁻ (s.indicator ((𝓕 u : State N q) : Configuration N → SpinAmplitudes N q))

theorem continuous_inversePhase {N : ℕ} (x : Configuration N) :
    Continuous (fun ξ : Configuration N => (Real.fourierChar (inner ℝ ξ x) : ℂ)) :=
  continuous_subtype_val.comp (Real.continuous_fourierChar.comp
    (continuous_id.inner continuous_const))

/-- Inverse Fourier evaluation on a finite-measure frequency set is a bounded linear map. -/
@[expose] noncomputable def inverseCutoffEvalCLM {N q : ℕ}
    (s : Set (Configuration N)) (hs : MeasurableSet s) (hμ : volume s ≠ ⊤)
    (x : Configuration N) : State N q →L[ℂ] SpinAmplitudes N q :=
  (stateSetIntegralCLM s hs hμ).comp
    ((Sobolev.boundedSMulCLM
      (fun ξ => (Real.fourierChar (inner ℝ ξ x) : ℂ)) 1
      (fun ξ => by simp) (continuous_inversePhase x).aestronglyMeasurable).comp
      (Lp.fourierTransformₗᵢ (Configuration N) (SpinAmplitudes N q)).toContinuousLinearEquiv.toContinuousLinearMap)

@[simp] theorem inverseCutoffEvalCLM_apply {N q : ℕ}
    (s : Set (Configuration N)) (hs : MeasurableSet s) (hμ : volume s ≠ ⊤)
    (x : Configuration N) (u : State N q) :
    inverseCutoffEvalCLM s hs hμ x u = inverseCutoffIntegral s u x := by
  change (∫ ξ in s, Sobolev.boundedSMul _ (𝓕 u) _ _ _ ξ) = _
  rw [inverseCutoffIntegral, Real.fourierInv_eq]
  have he : (fun ξ => Real.fourierChar (inner ℝ ξ x) •
      s.indicator ((𝓕 u : State N q) : Configuration N → SpinAmplitudes N q) ξ) =
      s.indicator (fun ξ => Real.fourierChar (inner ℝ ξ x) • (𝓕 u) ξ) := by
    funext ξ
    by_cases hξ : ξ ∈ s <;> simp [hξ]
  rw [he, integral_indicator hs]
  apply integral_congr_ae
  exact (Sobolev.boundedSMul_coeFn _ (𝓕 u) 1 _ _).filter_mono
    (ae_mono Measure.restrict_le_self)

/-- Finite-frequency representatives are continuous. -/
theorem continuous_inverseCutoffIntegral {N q : ℕ}
    (s : Set (Configuration N)) (hs : MeasurableSet s) (hμ : volume s ≠ ⊤)
    (u : State N q) : Continuous (inverseCutoffIntegral s u) := by
  have hi : Integrable (s.indicator ((𝓕 u : State N q) : Configuration N → SpinAmplitudes N q)) :=
    (integrable_indicator_iff hs).mpr (state_integrableOn (𝓕 u) s hμ)
  exact VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
    ((innerSL ℝ).continuous₂.neg) hi

/-- The finite-frequency integral is uniformly bounded by the L² mass. -/
theorem norm_inverseCutoffIntegral_le {N q : ℕ}
    (s : Set (Configuration N)) (hs : MeasurableSet s) (hμ : volume s ≠ ⊤)
    (u : State N q) (x : Configuration N) :
    ‖inverseCutoffIntegral s u x‖ ≤ Real.sqrt (volume s).toReal * ‖u‖ := by
  have h := VectorFourier.norm_fourierIntegral_le_integral_norm Real.fourierChar volume
    (-innerₗ (Configuration N)) (s.indicator ((𝓕 u : State N q) : Configuration N → SpinAmplitudes N q)) x
  change ‖inverseCutoffIntegral s u x‖ ≤ _ at h
  have he : (fun ξ => ‖s.indicator ((𝓕 u : State N q) : Configuration N → SpinAmplitudes N q) ξ‖) =
      s.indicator (fun ξ => ‖(𝓕 u) ξ‖) := by
    funext ξ
    by_cases hξ : ξ ∈ s <;> simp [hξ]
  rw [he, integral_indicator hs] at h
  exact h.trans (by simpa only [Lp.norm_fourier_eq] using
    integral_state_norm_on_le (𝓕 u) s hs hμ)

/-- Weak L² convergence implies pointwise convergence of finite-frequency inverse integrals. -/
theorem tendsto_inverseCutoffIntegral {N q : ℕ}
    (s : Set (Configuration N)) (hs : MeasurableSet s) (hμ : volume s ≠ ⊤)
    {u : ℕ → State N q} {v : State N q}
    (hu : ∀ w, Tendsto (fun n => inner ℂ (u n) w) atTop (𝓝 (inner ℂ v w)))
    (x : Configuration N) :
    Tendsto (fun n => inverseCutoffIntegral s (u n) x) atTop
      (𝓝 (inverseCutoffIntegral s v x)) := by
  apply tendsto_spin_of_tendsto_inner
  intro w
  simpa only [inverseCutoffEvalCLM_apply] using
    tendsto_inner_map_of_tendsto_inner hu (inverseCutoffEvalCLM s hs hμ x) w

/-- Bounded weakly convergent states have strongly locally convergent finite-frequency integrals. -/
theorem tendsto_integral_inverseCutoffIntegral_sub_sq {N q : ℕ}
    (s b : Set (Configuration N)) (hs : MeasurableSet s)
    (hμs : volume s ≠ ⊤) (hμb : volume b ≠ ⊤)
    {u : ℕ → State N q} {v : State N q}
    (hu : ∀ w, Tendsto (fun n => inner ℂ (u n) w) atTop (𝓝 (inner ℂ v w)))
    (K : ℝ) (hK : ∀ n, ‖u n‖ ≤ K) :
    Tendsto (fun n => ∫ x in b,
      ‖inverseCutoffIntegral s (u n) x - inverseCutoffIntegral s v x‖ ^ 2)
      atTop (𝓝 0) := by
  let : IsFiniteMeasure (volume.restrict b) := ⟨by simpa using hμb.lt_top⟩
  let C := Real.sqrt (volume s).toReal * (K + ‖v‖)
  have hbound (n : ℕ) (x : Configuration N) :
      ‖inverseCutoffIntegral s (u n) x - inverseCutoffIntegral s v x‖ ≤ C := by
    calc
      _ ≤ ‖inverseCutoffIntegral s (u n) x‖ + ‖inverseCutoffIntegral s v x‖ := norm_sub_le _ _
      _ ≤ Real.sqrt (volume s).toReal * ‖u n‖ + Real.sqrt (volume s).toReal * ‖v‖ :=
        add_le_add (norm_inverseCutoffIntegral_le s hs hμs _ x)
          (norm_inverseCutoffIntegral_le s hs hμs _ x)
      _ ≤ C := by
        dsimp only [C]
        rw [mul_add]
        exact add_le_add (mul_le_mul_of_nonneg_left (hK n) (Real.sqrt_nonneg _)) le_rfl
  have h := tendsto_integral_of_dominated_convergence
    (μ := volume.restrict b) (F := fun n x =>
      ‖inverseCutoffIntegral s (u n) x - inverseCutoffIntegral s v x‖ ^ 2)
    (f := fun _ => (0 : ℝ)) (fun _ => C ^ 2)
    (fun n => (((continuous_inverseCutoffIntegral s hs hμs (u n)).sub
      (continuous_inverseCutoffIntegral s hs hμs v)).norm.pow 2).aestronglyMeasurable)
    (integrable_const _) (fun n => Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (norm_nonneg _) (hbound n x) 2)
    (Eventually.of_forall fun x => by
      have ht := ((tendsto_inverseCutoffIntegral s hs hμs hu x).sub
        (tendsto_const_nhds (x := inverseCutoffIntegral s v x))).norm.pow 2
      simpa only [sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0)] using ht)
  simpa only [integral_zero] using h

/-- Restriction to a measurable set, retained as a state on the global carrier. -/
@[expose] noncomputable def stateIndicatorCLM {N q : ℕ}
    (s : Set (Configuration N)) (hs : MeasurableSet s) : State N q →L[ℂ] State N q :=
  Sobolev.boundedSMulCLM (s.indicator (fun _ => (1 : ℂ))) 1
    (fun x => by by_cases hx : x ∈ s <;> simp [hx])
    (aestronglyMeasurable_const.indicator hs)

/-- The state restriction has its usual indicator representative. -/
theorem stateIndicatorCLM_coeFn {N q : ℕ}
    (s : Set (Configuration N)) (hs : MeasurableSet s) (u : State N q) :
    ⇑(stateIndicatorCLM s hs u) =ᵐ[volume] s.indicator (u : Configuration N → SpinAmplitudes N q) := by
  filter_upwards [Sobolev.boundedSMul_coeFn (s.indicator (fun _ => (1 : ℂ))) u 1
    (fun x => by by_cases hx : x ∈ s <;> simp [hx])
    (aestronglyMeasurable_const.indicator hs)] with x hx
  change Sobolev.boundedSMul (s.indicator (fun _ => (1 : ℂ))) u 1 _ _ x = _
  rw [hx]
  by_cases hxs : x ∈ s <;> simp [hxs]

/-- Restriction is a contraction in L². -/
theorem norm_stateIndicatorCLM_le {N q : ℕ}
    (s : Set (Configuration N)) (hs : MeasurableSet s) (u : State N q) :
    ‖stateIndicatorCLM s hs u‖ ≤ ‖u‖ := by
  change ‖Sobolev.boundedSMul (s.indicator (fun _ => (1 : ℂ))) u 1 _ _‖ ≤ ‖u‖
  simpa only [one_mul] using Sobolev.norm_boundedSMul_le
    (s.indicator (fun _ => (1 : ℂ))) u 1
    (fun x => by by_cases hx : x ∈ s <;> simp [hx])
    (aestronglyMeasurable_const.indicator hs)

/-- Squared norm of restriction is the local mass integral. -/
theorem norm_stateIndicatorCLM_sq {N q : ℕ}
    (s : Set (Configuration N)) (hs : MeasurableSet s) (u : State N q) :
    ‖stateIndicatorCLM s hs u‖ ^ 2 = ∫ x in s, ‖u x‖ ^ 2 := by
  rw [← integral_state_norm_sq]
  calc
    _ = ∫ x, s.indicator (fun x => ‖u x‖ ^ 2) x := by
      apply integral_congr_ae
      filter_upwards [stateIndicatorCLM_coeFn s hs u] with x hx
      rw [hx]
      by_cases hxs : x ∈ s <;> simp [hxs]
    _ = _ := integral_indicator hs

end LiebThirring
end
