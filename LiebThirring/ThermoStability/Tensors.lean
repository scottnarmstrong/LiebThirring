/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.ThermoStability.Fibres

/-! # Separated nuclear and electronic tensors

Elementary tensors are used only as a dense core for the joint Fourier identity in quantum stability.
No product-state assumption is made on the quantum state.
-/

public section

open MeasureTheory WithLp
open scoped ENNReal NNReal

namespace LiebThirring.ThermoStability

/-- Multiplying a fixed electronic state by a complex amplitude is a bounded target map. -/
@[expose] noncomputable def stateScalarMap {N q : ℕ} (v : State N q) :
    ℂ →L[ℂ] State N q := (ContinuousLinearMap.id ℂ ℂ).smulRight v

/-- A nuclear L² amplitude tensored with an electronic L² state. -/
@[expose] noncomputable def jointTensor {N M q : ℕ}
    (f : Lp ℂ 2 (volume : Measure (Configuration M))) (v : State N q) : QuantumState N M q :=
  (electronFibreEquiv N M q).symm ((stateScalarMap v).compLp f)

theorem electronFibreField_jointTensor {N M q : ℕ}
    (f : Lp ℂ 2 (volume : Measure (Configuration M))) (v : State N q) :
    electronFibreField (jointTensor f v) = (stateScalarMap v).compLp f :=
  (electronFibreEquiv N M q).apply_symm_apply _

theorem jointTensor_ae {N M q : ℕ}
    (f : Lp ℂ 2 (volume : Measure (Configuration M))) (v : State N q) :
    ∀ᵐ R : Configuration M, ∀ᵐ x : Configuration N,
      jointTensor f v (toLp 2 (x, R)) = f R • v x := by
  have h := (stateScalarMap v).coeFn_compLp f
  rw [← electronFibreField_jointTensor] at h
  filter_upwards [electronFibreField_ae (jointTensor f v), h] with R hR hT
  filter_upwards [hR, Lp.coeFn_smul (f R) v] with x hx hs
  rw [← hx, hT]
  exact hs

/-- Continuous maps on the joint space are determined by their separated tensors. -/
theorem continuousLinearMap_ext_jointTensor {N M q : ℕ} {K : Type*}
    [NormedAddCommGroup K] [NormedSpace ℂ K]
    (A B : QuantumState N M q →L[ℂ] K)
    (h : ∀ (f : Lp ℂ 2 (volume : Measure (Configuration M))) (v : State N q),
      A (jointTensor f v) = B (jointTensor f v)) : A = B := by
  classical
  let C := (electronFibreEquiv N M q).symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hfield : ∀ u : Lp (State N q) 2 (volume : Measure (Configuration M)),
      A (C u) = B (C u) := by
    intro u
    apply Lp.induction ENNReal.ofNat_ne_top (fun u => A (C u) = B (C u))
    · intro v s hs hμs
      let f : Lp ℂ 2 (volume : Measure (Configuration M)) :=
        indicatorConstLp 2 hs hμs.ne 1
      have ht : (stateScalarMap v).compLp f = indicatorConstLp 2 hs hμs.ne v := by
        apply Lp.ext
        filter_upwards [(stateScalarMap v).coeFn_compLp f,
          (show f =ᵐ[volume] s.indicator (fun _ => (1 : ℂ)) from indicatorConstLp_coeFn),
          (show (indicatorConstLp 2 hs hμs.ne v : Lp (State N q) 2 volume) =ᵐ[volume]
            s.indicator (fun _ => v) from indicatorConstLp_coeFn)] with R hR hf hv
        rw [hR, hf, hv]
        by_cases hRs : R ∈ s
        · simp only [Set.indicator_of_mem hRs, stateScalarMap,
            ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.id_apply, one_smul]
        · simp only [Set.indicator_of_notMem hRs, map_zero]
      rw [Lp.simpleFunc.coe_indicatorConst, ← ht]
      exact h f v
    · intro f g hf hg hfg hAf hAg
      simp only [map_add]
      exact congrArg₂ (· + ·) hAf hAg
    · exact isClosed_eq (A.continuous.comp C.continuous) (B.continuous.comp C.continuous)
  apply ContinuousLinearMap.ext
  intro ψ
  have hψ := hfield (electronFibreEquiv N M q ψ)
  change A ((electronFibreEquiv N M q).symm (electronFibreEquiv N M q ψ)) =
    B ((electronFibreEquiv N M q).symm (electronFibreEquiv N M q ψ)) at hψ
  simpa only [LinearIsometryEquiv.symm_apply_apply] using hψ

end LiebThirring.ThermoStability

end
