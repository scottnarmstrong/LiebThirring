/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Ionization.EscapeTensor
public import LiebThirring.Theorems.KineticEnergySchwartz
public import LiebThirring.Sobolev.FormDensityPermutation
import LiebThirring.Variational.TrialScaling

/-! # Coordinate derivatives of the escaping tensor -/

public section

open MeasureTheory WithLp
open scoped ENNReal NNReal ContDiff SchwartzMap

namespace LiebThirring

/-- The omitted-coordinate projection as a continuous linear map. -/
@[expose] noncomputable def escapeOmitPositionsCLM {N : ℕ} (i : Fin (N + 1)) :
    Configuration (N + 1) →L[ℝ] Configuration N :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin N × Fin 3 => ℝ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun ja =>
      PiLp.proj 2 (fun _ : Fin (N + 1) × Fin 3 => ℝ) (Equiv.swap 0 i ja.1.succ, ja.2))

/-- A particle-position projection as a continuous linear map. -/
@[expose] noncomputable def escapeParticlePositionCLM {N : ℕ} (i : Fin N) :
    Configuration N →L[ℝ] Position :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun a => PiLp.proj 2 (fun _ : Fin N × Fin 3 => ℝ) (i, a))

theorem escape_fderiv_spin_apply {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [Fintype ι] (f : E → EuclideanSpace ℂ ι) {x : E}
    (hf : DifferentiableAt ℝ f x) (v : E) (s : ι) :
    (fderiv ℝ f x v) s = fderiv ℝ (fun y => f y s) x v := by
  have hd := (PiLp.proj 2 (fun _ : ι => ℂ) s).hasFDerivAt.comp x hf.hasFDerivAt
  exact (congrArg (fun L : E →L[ℝ] ℂ => L v) hd.fderiv).symm

theorem escapeOmitPositions_single_zero {N : ℕ} (a : Fin 3) :
    escapeOmitPositions 0 (PiLp.single 2 (0, a) (1 : ℝ) : Configuration (N + 1)) = 0 := by
  ext ja
  simp only [escapeOmitPositions, PiLp.toLp_apply, Equiv.swap_self, Equiv.refl_apply,
    PiLp.single_apply, Prod.mk.injEq, Fin.succ_ne_zero,
    false_and, ite_false, PiLp.zero_apply]

theorem escapeOmitPositions_single_succ {N : ℕ} (j : Fin N) (a : Fin 3) :
    escapeOmitPositions 0 (PiLp.single 2 (j.succ, a) (1 : ℝ) : Configuration (N + 1)) =
      PiLp.single 2 (j, a) (1 : ℝ) := by
  ext ja
  rcases ja with ⟨k, b⟩
  simp only [escapeOmitPositions, PiLp.toLp_apply, Equiv.swap_self, Equiv.refl_apply,
    PiLp.single_apply, Prod.mk.injEq, Fin.succ_inj]

theorem escapeParticlePosition_single_zero {N : ℕ} (a : Fin 3) :
    particlePosition (PiLp.single 2 (0, a) (1 : ℝ) : Configuration (N + 1)) 0 =
      PiLp.single 2 a (1 : ℝ) := by
  ext b
  simp only [particlePosition, PiLp.toLp_apply, PiLp.single_apply,
    Prod.mk.injEq, true_and]

theorem escapeParticlePosition_single_succ {N : ℕ} (j : Fin N) (a : Fin 3) :
    particlePosition (PiLp.single 2 (j.succ, a) (1 : ℝ) : Configuration (N + 1)) 0 = 0 := by
  ext b
  simp only [particlePosition, PiLp.toLp_apply, PiLp.single_apply,
    Prod.mk.injEq, Ne.symm (Fin.succ_ne_zero j), false_and, ite_false, PiLp.zero_apply]

/-- Product rule for the zero-particle tensor, with both projections derived
as continuous linear maps. -/
theorem escapeWedgeTerm_zero_fderiv_apply {N q : ℕ}
    (f : Configuration N → SpinAmplitudes N q)
    (h : Position → EuclideanSpace ℂ (Fin q))
    (hf : ContDiff ℝ ∞ f) (hh : ContDiff ℝ ∞ h)
    (x v : Configuration (N + 1)) (s : SpinLabels (N + 1) q) :
    (fderiv ℝ (escapeWedgeTermAmplitudes f h 0) x v) s =
      (fderiv ℝ f (escapeOmitPositions 0 x) (escapeOmitPositions 0 v))
          (escapeOmitSpins 0 s) * h (particlePosition x 0) (s 0) +
        f (escapeOmitPositions 0 x) (escapeOmitSpins 0 s) *
          (fderiv ℝ h (particlePosition x 0) (particlePosition v 0)) (s 0) := by
  have hF := (PiLp.proj 2 (fun _ : SpinLabels N q => ℂ) (escapeOmitSpins 0 s)).hasFDerivAt.comp
    (escapeOmitPositions 0 x) (hf.differentiable (by simp)).differentiableAt.hasFDerivAt
  have hFc := hF.comp x (escapeOmitPositionsCLM (N := N) 0).hasFDerivAt
  have hH := (PiLp.proj 2 (fun _ : Fin q => ℂ) (s 0)).hasFDerivAt.comp
    (particlePosition x 0) (hh.differentiable (by simp)).differentiableAt.hasFDerivAt
  have hHc := hH.comp x (escapeParticlePositionCLM (N := N + 1) 0).hasFDerivAt
  have hd := hFc.fun_mul hHc
  have hp (y : Configuration (N + 1)) : escapeParticlePositionCLM 0 y =
      particlePosition y 0 := rfl
  have ho (y : Configuration (N + 1)) : escapeOmitPositionsCLM 0 y =
      escapeOmitPositions 0 y := rfl
  simp only [Function.comp_def, PiLp.proj_apply,
    hp] at hd
  rw [escape_fderiv_spin_apply _
    ((contDiff_escapeWedgeTermAmplitudes f h hf hh 0).differentiable (by simp)).differentiableAt]
  have he : (fun y => escapeWedgeTermAmplitudes f h 0 y s) =
      fun y => f (escapeOmitPositions 0 y) (escapeOmitSpins 0 s) *
        h (particlePosition y 0) (s 0) := by
    funext y
    simp only [escapeWedgeTermAmplitudes, PiLp.toLp_apply, escapeWedgeTerm,
      escapePermutationSign, Equiv.swap_self, Equiv.Perm.sign_refl, Units.val_one,
      Int.cast_one, one_mul]
  rw [he, hd.fderiv]
  simp only [add_apply, smul_apply, smul_eq_mul,
    ContinuousLinearMap.comp_apply, PiLp.proj_apply, ho,
    hp]
  ring

theorem escapeWedgeTerm_zero_fderiv_zero {N q : ℕ}
    (f : Configuration N → SpinAmplitudes N q)
    (h : Position → EuclideanSpace ℂ (Fin q))
    (hf : ContDiff ℝ ∞ f) (hh : ContDiff ℝ ∞ h)
    (x : Configuration (N + 1)) (a : Fin 3) :
    fderiv ℝ (escapeWedgeTermAmplitudes f h 0) x (PiLp.single 2 (0, a) (1 : ℝ)) =
      escapeWedgeTermAmplitudes f (fun p => fderiv ℝ h p (PiLp.single 2 a (1 : ℝ))) 0 x := by
  apply PiLp.ext
  intro s
  rw [escapeWedgeTerm_zero_fderiv_apply f h hf hh,
    escapeOmitPositions_single_zero, escapeParticlePosition_single_zero]
  simp only [map_zero, PiLp.zero_apply, zero_mul, zero_add,
    escapeWedgeTermAmplitudes, PiLp.toLp_apply, escapeWedgeTerm,
    escapePermutationSign, Equiv.swap_self, Equiv.Perm.sign_refl, Units.val_one,
    Int.cast_one, one_mul]

theorem escapeWedgeTerm_zero_fderiv_succ {N q : ℕ}
    (f : Configuration N → SpinAmplitudes N q)
    (h : Position → EuclideanSpace ℂ (Fin q))
    (hf : ContDiff ℝ ∞ f) (hh : ContDiff ℝ ∞ h)
    (x : Configuration (N + 1)) (j : Fin N) (a : Fin 3) :
    fderiv ℝ (escapeWedgeTermAmplitudes f h 0) x (PiLp.single 2 (j.succ, a) (1 : ℝ)) =
      escapeWedgeTermAmplitudes (fun y => fderiv ℝ f y (PiLp.single 2 (j, a) (1 : ℝ))) h 0 x := by
  apply PiLp.ext
  intro s
  rw [escapeWedgeTerm_zero_fderiv_apply f h hf hh,
    escapeOmitPositions_single_succ, escapeParticlePosition_single_succ]
  simp only [map_zero, PiLp.zero_apply, mul_zero, add_zero,
    escapeWedgeTermAmplitudes, PiLp.toLp_apply, escapeWedgeTerm,
    escapePermutationSign, Equiv.swap_self, Equiv.Perm.sign_refl, Units.val_one,
    Int.cast_one, one_mul]

/-- Exact Dirichlet splitting of the compact smooth tensor: old kinetic
energy times orbital mass, plus old mass times orbital Dirichlet energy. -/
theorem escapeWedgeTerm_zero_kineticEnergy {N q : ℕ}
    (f : 𝓢(Configuration N, SpinAmplitudes N q))
    (h : 𝓢(Position, EuclideanSpace ℂ (Fin q)))
    (hf : HasCompactSupport (fun x => f x)) (hh : HasCompactSupport (fun x => h x)) :
    kineticEnergy ((escapeWedgeTermSchwartz f h hf hh 0).toLp 2 volume) =
      kineticEnergy (f.toLp 2 volume) * (∫⁻ p : Position, (‖h p‖₊ : ℝ≥0∞) ^ 2) +
        (∫⁻ y : Configuration N, (‖f y‖₊ : ℝ≥0∞) ^ 2) *
          ∑ a : Fin 3, ∫⁻ p : Position,
            (‖fderiv ℝ (fun z => h z) p (PiLp.single 2 a (1 : ℝ))‖₊ : ℝ≥0∞) ^ 2 := by
  classical
  have hd0 (a : Fin 3) :
      (∫⁻ x : Configuration (N + 1),
        (‖fderiv ℝ (escapeWedgeTermAmplitudes (fun y => f y) (fun y => h y) 0) x
          (PiLp.single 2 (0, a) (1 : ℝ))‖₊ : ℝ≥0∞) ^ 2) =
      (∫⁻ p : Position, (‖fderiv ℝ (fun z => h z) p (PiLp.single 2 a (1 : ℝ))‖₊ : ℝ≥0∞) ^ 2) *
        ∫⁻ y : Configuration N, (‖f y‖₊ : ℝ≥0∞) ^ 2 := by
    simp_rw [escapeWedgeTerm_zero_fderiv_zero (fun y => f y) (fun y => h y)
      (f.smooth ⊤) (h.smooth ⊤)]
    exact escapeWedgeTerm_lintegral_mass (fun y => f y) f.continuous.measurable
      (fun p => fderiv ℝ (fun z => h z) p (PiLp.single 2 a (1 : ℝ)))
      (((h.smooth ⊤).continuous_fderiv (by simp)).clm_apply continuous_const).measurable 0
  have hds (j : Fin N) (a : Fin 3) :
      (∫⁻ x : Configuration (N + 1),
        (‖fderiv ℝ (escapeWedgeTermAmplitudes (fun y => f y) (fun y => h y) 0) x
          (PiLp.single 2 (j.succ, a) (1 : ℝ))‖₊ : ℝ≥0∞) ^ 2) =
      (∫⁻ p : Position, (‖h p‖₊ : ℝ≥0∞) ^ 2) *
        ∫⁻ y : Configuration N,
          (‖fderiv ℝ (fun z => f z) y (PiLp.single 2 (j, a) (1 : ℝ))‖₊ : ℝ≥0∞) ^ 2 := by
    simp_rw [escapeWedgeTerm_zero_fderiv_succ (fun y => f y) (fun y => h y)
      (f.smooth ⊤) (h.smooth ⊤)]
    exact escapeWedgeTerm_lintegral_mass
      (fun y => fderiv ℝ (fun z => f z) y (PiLp.single 2 (j, a) (1 : ℝ)))
      (((f.smooth ⊤).continuous_fderiv (by simp)).clm_apply continuous_const).measurable
      (fun p => h p) h.continuous.measurable 0
  rw [kineticEnergy_schwartz]
  change (∑ i : Fin (N + 1), ∑ a : Fin 3, ∫⁻ x : Configuration (N + 1),
    (‖fderiv ℝ (escapeWedgeTermAmplitudes (fun y => f y) (fun y => h y) 0) x
      (PiLp.single 2 (i, a) (1 : ℝ))‖₊ : ℝ≥0∞) ^ 2) = _
  rw [Fin.sum_univ_succ]
  simp_rw [hd0, hds]
  simp only [← Finset.sum_mul, ← Finset.mul_sum]
  rw [← kineticEnergy_schwartz N q f]
  ring

/-- Relabeling the selected particle and its spin converts every summand
to the zero summand, up to its unit fermionic sign. -/
theorem escapeWedgeTermSchwartz_permute_swap {N q : ℕ}
    (f : 𝓢(Configuration N, SpinAmplitudes N q))
    (h : 𝓢(Position, EuclideanSpace ℂ (Fin q)))
    (hf : HasCompactSupport (fun x => f x)) (hh : HasCompactSupport (fun x => h x))
    (i : Fin (N + 1)) :
    Sobolev.permuteSchwartz (Equiv.swap 0 i) (escapeWedgeTermSchwartz f h hf hh i) =
      escapePermutationSign (Equiv.swap 0 i) • escapeWedgeTermSchwartz f h hf hh 0 := by
  apply SchwartzMap.ext
  intro x
  rw [Sobolev.permuteSchwartz_apply]
  apply PiLp.ext
  intro s
  change escapeWedgeTermAmplitudes (fun y => f y) (fun y => h y) i
      (permutePositions (Equiv.swap 0 i) x) (permuteSpins (Equiv.swap 0 i) s) =
    escapePermutationSign (Equiv.swap 0 i) *
      escapeWedgeTermAmplitudes (fun y => f y) (fun y => h y) 0 x s
  rw [escapeWedgeTermAmplitudes_permute_swap]
  have hp : permutePositions (Equiv.swap 0 i) (permutePositions (Equiv.swap 0 i) x) = x := by
    ext ja
    simp only [permutePositions, PiLp.toLp_apply, Equiv.swap_apply_self]
  rw [hp]

theorem escapeWedgeTerm_kineticEnergy_eq_zero {N q : ℕ}
    (f : 𝓢(Configuration N, SpinAmplitudes N q))
    (h : 𝓢(Position, EuclideanSpace ℂ (Fin q)))
    (hf : HasCompactSupport (fun x => f x)) (hh : HasCompactSupport (fun x => h x))
    (i : Fin (N + 1)) :
    kineticEnergy ((escapeWedgeTermSchwartz f h hf hh i).toLp 2 volume) =
      kineticEnergy ((escapeWedgeTermSchwartz f h hf hh 0).toLp 2 volume) := by
  have he := congrArg (fun g : 𝓢(Configuration (N + 1), SpinAmplitudes (N + 1) q) =>
    g.toLp 2 (volume : Measure (Configuration (N + 1))))
    (escapeWedgeTermSchwartz_permute_swap f h hf hh i)
  have hs := map_smul (SchwartzMap.toLpCLM ℂ (SpinAmplitudes (N + 1) q) 2
    (volume : Measure (Configuration (N + 1))))
    (escapePermutationSign (Equiv.swap 0 i)) (escapeWedgeTermSchwartz f h hf hh 0)
  simp only [SchwartzMap.toLpCLM_apply] at hs
  rw [Sobolev.permuteSchwartz_toLp, hs] at he
  have hn : ‖escapePermutationSign (Equiv.swap 0 i)‖₊ = 1 :=
    NNReal.coe_injective (norm_escapePermutationSign (Equiv.swap 0 i))
  calc
    _ = kineticEnergy (simultaneousPermutation (Equiv.swap 0 i)
        ((escapeWedgeTermSchwartz f h hf hh i).toLp 2 volume)) :=
      (Sobolev.kineticEnergy_simultaneousPermutation _ _).symm
    _ = _ := by
      rw [he, trial_kineticEnergy_smul, hn, ENNReal.coe_one, one_pow, one_mul]

end LiebThirring

end
