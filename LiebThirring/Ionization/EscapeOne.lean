/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module
public import LiebThirring.Variational.TrialVariational
public import LiebThirring.Variational.TrialVacuum
public import LiebThirring.Kinetic.CurryingProductBasic
/-! # The one-electron escape threshold

For one electron there is no repulsive pair energy. Normalized states whose Fourier
support shrinks to zero have kinetic energy tending to zero, and the attractive
term can only lower their energy. This proves the vacuum comparison without a
compact-core density input. The trials used here are Schwartz functions obtained
by inverse Fourier transform of compact smooth momentum-space bumps.
-/

public section
open MeasureTheory WithLp Set Function FourierTransform
open scoped ENNReal NNReal ContDiff SchwartzMap
namespace LiebThirring

/-- Every one-electron state is antisymmetric. -/
theorem antisymmetric_one (q : ℕ) (u : State 1 q) : antisymmetric u := by
  intro σ
  have hσ : σ = Equiv.refl (Fin 1) := Subsingleton.elim _ _
  subst σ
  filter_upwards [] with x
  intro s
  have hs : permuteSpins (Equiv.refl (Fin 1)) s = s := by
    funext i
    rfl
  rw [hs]
  simp [permutePositions]

/-- Normalized smooth momentum-space bumps exist inside every positive-radius ball. -/
theorem exists_normalized_small_support (q : ℕ) (hq : 1 ≤ q) (r : ℝ) (hr : 0 < r) :
    ∃ f : 𝓢(Configuration 1, SpinAmplitudes 1 q),
      ‖f.toLp 2 (volume : Measure (Configuration 1))‖ = 1 ∧
      ∀ x, r ≤ ‖x‖ → f x = 0 := by
  obtain ⟨b, hb, hc, hs, _, hv⟩ := exists_contDiff_tsupport_subset
    (n := (⊤ : ℕ∞)) (Metric.ball_mem_nhds (0 : Configuration 1) hr)
  let t : Fin q := ⟨0, lt_of_lt_of_le Nat.zero_lt_one hq⟩
  let v := trialSpinVector 1 q t
  let f : 𝓢(Configuration 1, SpinAmplitudes 1 q) :=
    (hc.smul_right (f' := fun _ => v)).toSchwartzMap (hs.smul contDiff_const)
  have hf : f ≠ 0 := by
    intro hf
    have he := congrArg (fun g : 𝓢(Configuration 1, SpinAmplitudes 1 q) =>
      g 0 (fun _ => t)) hf
    change (b 0 : ℂ) * v (fun _ => t) = 0 at he
    simp [hv, v, trialSpinVector] at he
  refine ⟨‖f.toLp 2 (volume : Measure (Configuration 1))‖⁻¹ • f,
    norm_schwartz_toLp_normalize f hf, ?_⟩
  intro x hx
  have hbx : b x = 0 := by
    apply image_eq_zero_of_notMem_tsupport
    intro hm
    have hball := hb hm
    rw [Metric.mem_ball, dist_zero_right] at hball
    exact (not_lt.mpr hx) hball
  change (‖f.toLp 2 (volume : Measure (Configuration 1))‖⁻¹ : ℝ) • (b x • v) = 0
  rw [hbx, zero_smul, smul_zero]

/-- An inverse-Fourier trial supported in a momentum ball has the expected kinetic bound. -/
theorem kineticEnergy_inverse_small_support (q : ℕ) (r : ℝ) (hr : 0 ≤ r)
    (f : 𝓢(Configuration 1, SpinAmplitudes 1 q))
    (hf : ∀ x, r ≤ ‖x‖ → f x = 0) :
    kineticEnergy ((Lp.fourierTransformₗᵢ (Configuration 1) (SpinAmplitudes 1 q)).symm
      (f.toLp 2 (volume : Measure (Configuration 1)))) ≤
      ENNReal.ofReal ((2 * Real.pi) ^ 2 * r ^ 2) *
        ‖f.toLp 2 (volume : Measure (Configuration 1))‖ₑ ^ 2 := by
  rw [kineticEnergy]
  simp only [LinearIsometryEquiv.apply_symm_apply]
  calc
    _ ≤ ∫⁻ x : Configuration 1,
        ENNReal.ofReal ((2 * Real.pi) ^ 2 * r ^ 2) *
          (‖(f.toLp 2 (volume : Measure (Configuration 1))) x‖₊ : ℝ≥0∞) ^ 2 := by
      apply lintegral_mono_ae
      filter_upwards [f.coeFn_toLp 2 (volume : Measure (Configuration 1))] with x hx
      rw [hx]
      by_cases hxr : r ≤ ‖x‖
      · rw [hf x hxr]
        simp only [nnnorm_zero, ENNReal.coe_zero, zero_pow (by decide : 2 ≠ 0), mul_zero]
        exact le_rfl
      · have hn : (‖x‖₊ : ℝ≥0∞) ≤ ENNReal.ofReal r := by
          rw [← ENNReal.ofReal_coe_nnreal]
          exact ENNReal.ofReal_le_ofReal (le_of_not_ge hxr)
        have hp := mul_le_mul' (le_refl (ENNReal.ofReal ((2 * Real.pi) ^ 2))) (pow_le_pow_left' hn 2)
        have hprod : ENNReal.ofReal ((2 * Real.pi) ^ 2) * ENNReal.ofReal r ^ 2 =
            ENNReal.ofReal ((2 * Real.pi) ^ 2 * r ^ 2) := by
          rw [← ENNReal.ofReal_pow hr, ENNReal.ofReal_mul (sq_nonneg _)]
        rw [hprod] at hp
        exact mul_le_mul' hp (le_refl _)
    _ = _ := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      rw [← lintegral_l2_enorm_sq]
      rfl

/-- Normalized one-electron form-domain states have arbitrarily small kinetic energy. -/
theorem exists_normalized_one_kinetic_lt (q : ℕ) (hq : 1 ≤ q)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ u : FormDomain 1 q, ‖(u : State 1 q)‖ = 1 ∧
      (kineticEnergy (u : State 1 q)).toReal < ε := by
  obtain ⟨c, hc, hsmall⟩ := exists_pos_mul_lt hε ((2 * Real.pi) ^ 2)
  let r := Real.sqrt c
  have hr : 0 < r := Real.sqrt_pos.mpr hc
  obtain ⟨f, hn, hs⟩ := exists_normalized_small_support q hq r hr
  let u : State 1 q :=
    (Lp.fourierTransformₗᵢ (Configuration 1) (SpinAmplitudes 1 q)).symm
      (f.toLp 2 (volume : Measure (Configuration 1)))
  have hk : kineticEnergy u ≤ ENNReal.ofReal ((2 * Real.pi) ^ 2 * c) := by
    have h := kineticEnergy_inverse_small_support q r hr.le f hs
    rw [← ofReal_norm, hn, ENNReal.ofReal_one, one_pow, mul_one,
      Real.sq_sqrt hc.le] at h
    exact h
  have hfinite : kineticEnergy u < ⊤ := lt_of_le_of_lt hk ENNReal.ofReal_lt_top
  refine ⟨⟨u, antisymmetric_one q u, hfinite⟩, ?_, ?_⟩
  · exact ((Lp.fourierTransformₗᵢ (Configuration 1) (SpinAmplitudes 1 q)).symm.norm_map _).trans hn
  · have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hk
    rw [ENNReal.toReal_ofReal (mul_nonneg (sq_nonneg _) hc.le)] at hreal
    exact hreal.trans_lt hsmall

/-- The one-electron atomic quadratic form is bounded above by kinetic energy. -/
theorem realEnergy_one_le_kinetic (q : ℕ) (Z : ℝ≥0) (u : FormDomain 1 q) :
    realEnergy (fun _ : Fin 1 => Z) (fun _ => 0)
      (fun _ _ _ => Subsingleton.elim _ _) u ≤
      (kineticEnergy (u : State 1 q)).toReal := by
  have he (x : Configuration 1) : electronRepulsion x = 0 := by
    simp [electronRepulsion]
  unfold realEnergy
  rw [nuclearRepulsion_single]
  simp only [he, zero_mul, lintegral_zero, ENNReal.toReal_zero, add_zero]
  exact sub_le_self _ ENNReal.toReal_nonneg

/-- Every one-electron atomic energy is bounded above by zero. -/
theorem atomicGroundStateEnergy_one_le_zero (q : ℕ) (hq : 1 ≤ q) (Z : ℝ≥0) :
    atomicGroundStateEnergy 1 q Z ≤ 0 := by
  have hreal : (atomicGroundStateEnergy 1 q Z).toReal ≤ 0 := by
    apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨u, hn, hk⟩ := exists_normalized_one_kinetic_lt q hq ε hε
    have hvar := groundStateEnergy_toReal_le_realEnergy q hq 1 1 (fun _ => Z)
      (fun _ => 0) (fun _ _ _ => Subsingleton.elim _ _) u hn
    have hbound := (hvar.trans (realEnergy_one_le_kinetic q Z u)).trans hk.le
    change (groundStateEnergy 1 q 1 (fun _ => Z) (fun _ => 0)
      (fun _ _ _ => Subsingleton.elim _ _)).toReal ≤ 0 + ε
    simpa only [zero_add] using hbound
  have hf := trial_groundStateEnergy_finite q hq 1 1 (fun _ => Z) (fun _ => 0)
    (fun _ _ _ => Subsingleton.elim _ _)
  change atomicGroundStateEnergy 1 q Z ≠ ⊤ ∧ atomicGroundStateEnergy 1 q Z ≠ ⊥ at hf
  rw [← EReal.coe_toReal hf.1 hf.2]
  exact_mod_cast hreal

/-- The one-electron escape comparison, with the vacuum sector on the right. -/
theorem atomicGroundStateEnergy_one_le_vacuum (q : ℕ) (hq : 1 ≤ q) (Z : ℝ≥0) :
    atomicGroundStateEnergy 1 q Z ≤ atomicGroundStateEnergy 0 q Z := by
  rw [atomicGroundStateEnergy_vacuum q hq Z]
  exact atomicGroundStateEnergy_one_le_zero q hq Z

end LiebThirring
end
