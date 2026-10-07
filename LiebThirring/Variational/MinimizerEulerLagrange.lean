/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Variational.TrialVariational
public import LiebThirring.Variational.FormPolarization
public import LiebThirring.Variational.WeakGroundState

/-! # Euler--Lagrange equation for a variational minimizer

A normalized state attaining the variational infimum satisfies the full complex weak
eigenfunction equation. The proof first treats real variations and then repeats the argument
with an imaginary test direction.
-/

public section

open MeasureTheory WithLp
open scoped ENNReal NNReal ComplexConjugate

namespace LiebThirring

/-- Expansion of the energy along a real affine line in the complex form domain. -/
theorem realEnergy_add_real_smul {N q M : ℕ} (z : Fin M → ℝ≥0)
    (R : Fin M → Position) (hR : Function.Injective R)
    (u v : FormDomain N q) (t : ℝ) :
    realEnergy z R hR (u + (t : ℂ) • v) =
      realEnergy z R hR u + 2 * t * (energyForm z R hR v u).re +
        t ^ 2 * realEnergy z R hR v := by
  apply Complex.ofReal_injective
  rw [← energyForm_self z R hR (u + (t : ℂ) • v)]
  simp only [energyForm_add_left, energyForm_add_right,
    energyForm_smul_left, energyForm_smul_right]
  rw [energyForm_self z R hR u, energyForm_self z R hR v,
    ← energyForm_conj_symm z R hR v u]
  push_cast
  apply Complex.ext
  · norm_num [pow_two, Complex.mul_re, Complex.mul_im]
    ring
  · norm_num [pow_two, Complex.mul_re, Complex.mul_im]

/-- Expansion of squared mass along a real affine line in the complex form domain. -/
theorem norm_sq_add_real_smul {N q : ℕ} (u v : FormDomain N q) (t : ℝ) :
    ‖((u + (t : ℂ) • v : FormDomain N q) : State N q)‖ ^ 2 =
      ‖(u : State N q)‖ ^ 2 + 2 * t * (inner ℂ (v : State N q) (u : State N q)).re +
        t ^ 2 * ‖(v : State N q)‖ ^ 2 := by
  rw [formDomain_coe_add, formDomain_coe_smul,
    InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ)]
  simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right]
  rw [inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (u : State N q),
    inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (v : State N q),
    ← inner_conj_symm (𝕜 := ℂ) (v : State N q) (u : State N q)]
  norm_num [pow_two, Complex.mul_re, Complex.mul_im]
  have hreal : (inner ℂ (u : State N q) (v : State N q)).re =
      (inner ℂ (v : State N q) (u : State N q)).re := by
    rw [← inner_conj_symm (𝕜 := ℂ) (v : State N q) (u : State N q),
      Complex.conj_re]
  rw [hreal]
  ring

/-- A quadratic polynomial with zero constant term that is nonnegative everywhere has
zero linear coefficient. -/
theorem linear_eq_zero_of_quadratic_nonneg (a b : ℝ)
    (h : ∀ t : ℝ, 0 ≤ 2 * t * a + t ^ 2 * b) : a = 0 := by
  by_contra ha
  let c : ℝ := |b| + 1
  have hc : 0 < c := by
    dsimp only [c]
    positivity
  have hb : b < 2 * c := by
    dsimp only [c]
    calc
      b ≤ |b| := le_abs_self b
      _ < 2 * (|b| + 1) := by linarith only [abs_nonneg b]
  have ht := h (-a / c)
  have hneg : 2 * (-a / c) * a + (-a / c) ^ 2 * b < 0 := by
    rw [div_pow]
    have hc0 : c ≠ 0 := ne_of_gt hc
    have hs : 0 < a ^ 2 := sq_pos_of_ne_zero ha
    have heq : 2 * (-a / c) * a + (-a / c) ^ 2 * b =
        (a ^ 2 * (b - 2 * c)) / c ^ 2 := by
      field_simp
      ring
    rw [← div_pow, heq]
    exact div_neg_iff.mpr (Or.inr
      ⟨mul_neg_of_pos_of_neg hs (sub_neg.mpr hb), sq_pos_of_ne_zero hc0⟩)
  exact (not_lt_of_ge ht) hneg

/-- The energy of an attained normalized minimizer gives the homogeneous lower bound on
every form-domain state. The proof normalizes each nonzero comparison state directly. -/
theorem minimizer_energy_mul_norm_sq_le {N q M : ℕ} (z : Fin M → ℝ≥0)
    (R : Fin M → Position) (hR : Function.Injective R)
    (u : FormDomain N q)
    (hmin : groundStateEnergy N q M z R hR = (realEnergy z R hR u : EReal))
    (v : FormDomain N q) :
    realEnergy z R hR u * ‖(v : State N q)‖ ^ 2 ≤ realEnergy z R hR v := by
  by_cases hv : (v : State N q) = 0
  · rw [hv, norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero,
      realEnergy_eq_zero_of_state_eq_zero z R hR v hv]
  · let c : ℂ := (‖(v : State N q)‖⁻¹ : ℝ)
    have hn : ‖(v : State N q)‖ ≠ 0 := norm_ne_zero_iff.mpr hv
    have hc : ‖c‖ = ‖(v : State N q)‖⁻¹ := by
      exact Complex.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _))
    have hvnorm : ‖((c • v : FormDomain N q) : State N q)‖ = 1 := by
      rw [formDomain_coe_smul, norm_smul, hc]
      exact inv_mul_cancel₀ hn
    have hbE : groundStateEnergy N q M z R hR ≤
        (realEnergy z R hR (c • v) : EReal) := by
      let w : {ψ : FormDomain N q // ‖(ψ : State N q)‖ = 1} := ⟨c • v, hvnorm⟩
      exact iInf_le (fun w : {ψ : FormDomain N q // ‖(ψ : State N q)‖ = 1} =>
        (realEnergy z R hR w.val : EReal)) w
    rw [hmin] at hbE
    have hb : realEnergy z R hR u ≤ realEnergy z R hR (c • v) :=
      EReal.coe_le_coe_iff.mp hbE
    rw [realEnergy_smul, hc] at hb
    have hscaled := mul_le_mul_of_nonneg_right hb (sq_nonneg ‖(v : State N q)‖)
    have heq : (‖(v : State N q)‖⁻¹ ^ 2 * realEnergy z R hR v) *
        ‖(v : State N q)‖ ^ 2 = realEnergy z R hR v := by
      rw [mul_right_comm, ← mul_pow, inv_mul_cancel₀ hn, one_pow, one_mul]
    exact heq ▸ hscaled

/-- A normalized state attaining the variational infimum is a weak eigenfunction at its
real energy. -/
theorem normalized_minimizer_is_weak_eigenfunction {N q M : ℕ}
    (z : Fin M → ℝ≥0) (R : Fin M → Position) (hR : Function.Injective R)
    (u : FormDomain N q) (hu : ‖(u : State N q)‖ = 1)
    (hmin : groundStateEnergy N q M z R hR = (realEnergy z R hR u : EReal)) :
    is_weak_eigenfunction z R hR (realEnergy z R hR u) u := by
  constructor
  · intro hzero
    rw [hzero, norm_zero] at hu
    norm_num at hu
  intro v
  let A : ℂ := energyForm z R hR v u -
    (realEnergy z R hR u : ℂ) * inner ℂ (v : State N q) (u : State N q)
  have hre : A.re = 0 := by
    apply linear_eq_zero_of_quadratic_nonneg A.re
      (realEnergy z R hR v - realEnergy z R hR u * ‖(v : State N q)‖ ^ 2)
    intro t
    have hb := minimizer_energy_mul_norm_sq_le z R hR u hmin (u + (t : ℂ) • v)
    rw [realEnergy_add_real_smul, norm_sq_add_real_smul, hu, one_pow] at hb
    dsimp only [A]
    simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
    linarith only [hb]
  have him : A.im = 0 := by
    let w : FormDomain N q := Complex.I • v
    have hreal : (energyForm z R hR w u -
        (realEnergy z R hR u : ℂ) * inner ℂ (w : State N q) (u : State N q)).re = 0 := by
      apply linear_eq_zero_of_quadratic_nonneg
        (energyForm z R hR w u -
          (realEnergy z R hR u : ℂ) * inner ℂ (w : State N q) (u : State N q)).re
        (realEnergy z R hR w - realEnergy z R hR u * ‖(w : State N q)‖ ^ 2)
      intro t
      have hb := minimizer_energy_mul_norm_sq_le z R hR u hmin (u + (t : ℂ) • w)
      rw [realEnergy_add_real_smul, norm_sq_add_real_smul, hu, one_pow] at hb
      simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
      linarith only [hb]
    dsimp only [w] at hreal
    rw [energyForm_smul_left, formDomain_coe_smul, inner_smul_left] at hreal
    dsimp only [A]
    simp only [Complex.conj_I, Complex.sub_re, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im] at hreal ⊢
    norm_num [Complex.I] at hreal ⊢
    linarith only [hreal]
  exact sub_eq_zero.mp (Complex.ext hre him)

/-- A normalized minimizer satisfies the weak-ground-state predicate. -/
theorem normalized_minimizer_is_weak_ground_state {N q M : ℕ}
    (z : Fin M → ℝ≥0) (R : Fin M → Position) (hR : Function.Injective R)
    (u : FormDomain N q) (hu : ‖(u : State N q)‖ = 1)
    (hmin : groundStateEnergy N q M z R hR = (realEnergy z R hR u : EReal)) :
    is_weak_ground_state z R hR u := by
  exact ⟨hu, realEnergy z R hR u, hmin,
    normalized_minimizer_is_weak_eigenfunction z R hR u hu hmin⟩

/-- Conversely, a weak ground state attains the variational infimum. -/
theorem weak_ground_state_attains_infimum {N q M : ℕ} (z : Fin M → ℝ≥0)
    (R : Fin M → Position) (hR : Function.Injective R) (u : FormDomain N q)
    (hu : is_weak_ground_state z R hR u) :
    groundStateEnergy N q M z R hR = (realEnergy z R hR u : EReal) := by
  obtain ⟨hnorm, E, hground, _, heigen⟩ := hu
  have henergy : realEnergy z R hR u = E := by
    have hself := heigen u
    rw [energyForm_self, inner_self_eq_norm_sq_to_K, hnorm] at hself
    norm_num at hself
    exact hself
  rw [henergy]
  exact hground

end LiebThirring

end
