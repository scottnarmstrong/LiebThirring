/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Sobolev.FormDensity
public import LiebThirring.Sobolev.WeakEnergy

/-!
# Compact smooth density in weak-derivative graph coordinates

Finite-energy states admit compact smooth approximants whose states and every coordinate weak
derivative converge in L².
-/

public section

open MeasureTheory Filter LineDeriv
open scoped ENNReal NNReal SchwartzMap FourierTransform ContDiff Topology

namespace LiebThirring.Sobolev

/-- The classical coordinate derivative of a Schwartz state, bundled in L². -/
noncomputable def schwartzCoordinateDerivativeL2 {N q : ℕ}
    (f : 𝓢(Configuration N, SpinAmplitudes N q)) (a : Fin N × Fin 3) : State N q :=
  (lineDerivOp (coordinateVector a) f).toLp 2 volume

/-- A Schwartz coordinate derivative is its weak coordinate derivative. -/
theorem hasWeakDerivative_schwartzCoordinateDerivativeL2 {N q : ℕ}
    (f : 𝓢(Configuration N, SpinAmplitudes N q)) (a : Fin N × Fin 3) :
    HasWeakDerivative a (f.toLp 2 volume) (schwartzCoordinateDerivativeL2 f a) := by
  rw [hasWeakDerivative_iff_fourier_eq_symbol]
  have hderiv : 𝓕 (schwartzCoordinateDerivativeL2 f a) =
      (𝓕 (lineDerivOp (coordinateVector a) f)).toLp 2 volume := by
    exact SchwartzMap.toLp_fourier_eq _
  have hstate : 𝓕 (f.toLp 2 volume) = (𝓕 f).toLp 2 volume :=
    SchwartzMap.toLp_fourier_eq f
  filter_upwards [(𝓕 (lineDerivOp (coordinateVector a) f)).coeFn_toLp 2 volume,
    (𝓕 f).coeFn_toLp 2 volume] with ξ hd hu
  rw [hderiv, hstate, hd, hu, fourier_lineDeriv_coordinate]

theorem HasWeakDerivative.sub_schwartz {N q : ℕ} {u g : State N q}
    {a : Fin N × Fin 3} (h : HasWeakDerivative a u g)
    (f : 𝓢(Configuration N, SpinAmplitudes N q)) :
    HasWeakDerivative a (u - f.toLp 2 volume)
      (g - schwartzCoordinateDerivativeL2 f a) := by
  have hu' : (u, g) ∈ weakDerivativeGraph (q := q) a := h
  have hf' : (f.toLp 2 volume, schwartzCoordinateDerivativeL2 f a) ∈
      weakDerivativeGraph (q := q) a := hasWeakDerivative_schwartzCoordinateDerivativeL2 f a
  have hd := (weakDerivativeGraph (q := q) a).sub_mem hu' hf'
  change HasWeakDerivative a (u - f.toLp 2 volume)
    (g - schwartzCoordinateDerivativeL2 f a) at hd
  exact hd

theorem norm_weakDerivative_sub_schwartz_le {N q : ℕ} {u : State N q}
    {g : (Fin N × Fin 3) → State N q} (hg : ∀ a, HasWeakDerivative a u (g a))
    (f : 𝓢(Configuration N, SpinAmplitudes N q)) {ε : ℝ} (hε : 0 ≤ ε)
    (henergy : kineticEnergy (u - f.toLp 2 volume) ≤
      ENNReal.ofReal ((2 * Real.pi * ε) ^ 2)) (a : Fin N × Fin 3) :
    ‖g a - schwartzCoordinateDerivativeL2 f a‖ ≤ 2 * Real.pi * ε := by
  have hsq : ‖g a - schwartzCoordinateDerivativeL2 f a‖ ^ 2 ≤
      (2 * Real.pi * ε) ^ 2 := by
    calc
      _ ≤ ∑ b : Fin N × Fin 3, ‖g b - schwartzCoordinateDerivativeL2 f b‖ ^ 2 :=
        Finset.single_le_sum (fun _ _ ↦ sq_nonneg _) (Finset.mem_univ a)
      _ = (kineticEnergy (u - f.toLp 2 volume)).toReal := by
        symm
        apply kineticEnergy_toReal_eq_sum_weakDerivative_norm_sq
        intro b
        exact (hg b).sub_schwartz f
      _ ≤ (2 * Real.pi * ε) ^ 2 :=
        ENNReal.toReal_le_of_le_ofReal (sq_nonneg _) henergy
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg
    (le_of_lt (mul_pos (by norm_num) Real.pi_pos)) hε)).mp hsq

theorem tendsto_schwartzCoordinateDerivativeL2_of_form_bounds {N q : ℕ}
    {u : State N q} {g : (Fin N × Fin 3) → State N q}
    (hg : ∀ a, HasWeakDerivative a u (g a))
    (f : ℕ → 𝓢(Configuration N, SpinAmplitudes N q)) (ε : ℕ → ℝ)
    (hεnonneg : ∀ n, 0 ≤ ε n) (hε : Tendsto ε atTop (𝓝 0))
    (henergy : ∀ n, kineticEnergy (u - (f n).toLp 2 volume) ≤
      ENNReal.ofReal ((2 * Real.pi * ε n) ^ 2)) (a : Fin N × Fin 3) :
    Tendsto (fun n ↦ schwartzCoordinateDerivativeL2 (f n) a) atTop (𝓝 (g a)) := by
  have hnorm (n : ℕ) : ‖g a - schwartzCoordinateDerivativeL2 (f n) a‖ ≤
      2 * Real.pi * ε n :=
    norm_weakDerivative_sub_schwartz_le hg (f n) (hεnonneg n) (henergy n) a
  have hzero : Tendsto (fun n ↦ ‖g a - schwartzCoordinateDerivativeL2 (f n) a‖)
      atTop (𝓝 0) := by
    apply squeeze_zero (fun _ ↦ norm_nonneg _) hnorm
    simpa only [mul_zero] using hε.const_mul (2 * Real.pi)
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simpa only [norm_sub_rev] using hzero

/-- Compact smooth approximation with simultaneous convergence of all weak derivatives. -/
theorem exists_compact_smooth_weakDerivative_sequence {N q : ℕ} (u : State N q)
    (g : (Fin N × Fin 3) → State N q) (hg : ∀ a, HasWeakDerivative a u (g a)) :
    ∃ f : ℕ → 𝓢(Configuration N, SpinAmplitudes N q),
      (∀ n, HasCompactSupport (f n)) ∧
      Tendsto (fun n ↦ (f n).toLp 2 volume) atTop (𝓝 u) ∧
      ∀ a, Tendsto (fun n ↦ schwartzCoordinateDerivativeL2 (f n) a) atTop (𝓝 (g a)) := by
  have hu : kineticEnergy u < ⊤ :=
    (kineticEnergy_lt_top_iff_exists_weakDerivatives u).mpr ⟨g, hg⟩
  let ε : ℕ → ℝ := fun n ↦ ((n : ℝ) + 1)⁻¹
  have hεpos (n : ℕ) : 0 < ε n := by
    dsimp [ε]
    positivity
  choose f hfK hmass henergy using fun n ↦
    exists_compact_smooth_form_approximation u hu (hεpos n)
  have hε : Tendsto ε atTop (𝓝 0) := by
    exact tendsto_inv_atTop_zero.comp
      (tendsto_atTop_add_const_right atTop 1
        (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ ↦ (n : ℝ)) atTop atTop))
  have hstate : Tendsto (fun n ↦ (f n).toLp 2 volume) atTop (𝓝 u) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    simpa only [norm_sub_rev] using
      squeeze_zero (fun _ ↦ norm_nonneg _) hmass hε
  refine ⟨f, hfK, hstate, ?_⟩
  intro a
  exact tendsto_schwartzCoordinateDerivativeL2_of_form_bounds hg f ε
    (fun n ↦ (hεpos n).le) hε henergy a

end LiebThirring.Sobolev

end
