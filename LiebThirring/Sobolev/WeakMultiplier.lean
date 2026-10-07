/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Sobolev.WeakDerivative
import Mathlib.Analysis.Calculus.Rademacher

/-!
# Bounded spatial multipliers on states

This file supplies the `L²` part of the weak-derivative multiplier construction.  The
multiplier is allowed to be complex-valued; later product-rule results can therefore use
the same construction for a multiplier and for each of its weak derivatives.
-/

public section

open MeasureTheory
open scoped NNReal

namespace LiebThirring.Sobolev

/-- Pointwise multiplication of a state by a bounded measurable scalar function. -/
noncomputable def boundedSMul {N q : ℕ} (b : Configuration N → ℂ) (u : State N q)
    (C : ℝ) (hb : ∀ x, ‖b x‖ ≤ C) (hbm : AEStronglyMeasurable b) : State N q :=
  (MemLp.of_le_mul (Lp.memLp u) (hbm.smul (Lp.aestronglyMeasurable u))
    (Filter.Eventually.of_forall fun x => by
      change ‖b x • u x‖ ≤ C * ‖u x‖
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_right (hb x) (norm_nonneg _))).toLp
      (fun x => b x • u x)

/-- The bounded spatial multiplier agrees almost everywhere with pointwise multiplication. -/
theorem boundedSMul_coeFn {N q : ℕ} (b : Configuration N → ℂ) (u : State N q)
    (C : ℝ) (hb : ∀ x, ‖b x‖ ≤ C) (hbm : AEStronglyMeasurable b) :
    ⇑(boundedSMul b u C hb hbm) =ᵐ[volume] fun x => b x • u x :=
  MemLp.coeFn_toLp _

/-- Multiplication by a scalar function bounded by `C` has operator norm at most `C`. -/
theorem norm_boundedSMul_le {N q : ℕ} (b : Configuration N → ℂ) (u : State N q)
    (C : ℝ) (hb : ∀ x, ‖b x‖ ≤ C) (hbm : AEStronglyMeasurable b) :
    ‖boundedSMul b u C hb hbm‖ ≤ C * ‖u‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [boundedSMul_coeFn b u C hb hbm] with x hx
  rw [hx, norm_smul]
  exact mul_le_mul_of_nonneg_right (hb x) (norm_nonneg _)

/-- The classical directional derivative chosen by `fderiv`; it is zero at points where the
multiplier is not differentiable.  Rademacher's theorem says that the latter set is null for a
Lipschitz multiplier. -/
@[expose] noncomputable def lipschitzDirectionalDerivative {N : ℕ}
    (b : Configuration N → ℝ) (a : Fin N × Fin 3) (x : Configuration N) : ℝ :=
  fderiv ℝ b x (coordinateVector a)

/-- The chosen directional derivative is measurable. -/
theorem lipschitzDirectionalDerivative_measurable {N : ℕ}
    (b : Configuration N → ℝ) (a : Fin N × Fin 3) :
    Measurable (lipschitzDirectionalDerivative b a) :=
  measurable_fderiv_apply_const ℝ b (coordinateVector a)

/-- Every coordinate derivative of a `C`-Lipschitz function is bounded by `C`. -/
theorem norm_lipschitzDirectionalDerivative_le {N : ℕ}
    (b : Configuration N → ℝ) (C : ℝ≥0) (hb : LipschitzWith C b)
    (a : Fin N × Fin 3) (x : Configuration N) :
    ‖lipschitzDirectionalDerivative b a x‖ ≤ C := by
  calc
    _ ≤ ‖fderiv ℝ b x‖ * ‖coordinateVector a‖ := ContinuousLinearMap.le_opNorm _ _
    _ = ‖fderiv ℝ b x‖ := by simp [coordinateVector]
    _ ≤ C := norm_fderiv_le_of_lipschitz ℝ (f := b) hb

/-- A Lipschitz multiplier is differentiable almost everywhere on configuration space. -/
theorem LipschitzWith.ae_differentiableAt_configuration {N : ℕ}
    {b : Configuration N → ℝ} {C : ℝ≥0} (hb : LipschitzWith C b) :
    ∀ᵐ x ∂(volume : Measure (Configuration N)), DifferentiableAt ℝ b x :=
  hb.ae_differentiableAt

/-- Multiplication by a bounded real Lipschitz function, viewed as a complex scalar multiplier. -/
noncomputable def lipschitzBoundedSMul {N q : ℕ} (b : Configuration N → ℝ)
    (B : ℝ) (hB : ∀ x, ‖b x‖ ≤ B) {C : ℝ≥0} (hb : LipschitzWith C b)
    (u : State N q) : State N q :=
  boundedSMul (fun x => (b x : ℂ)) u B (fun x => by simpa using hB x)
    (Complex.measurable_ofReal.comp hb.continuous.measurable).aestronglyMeasurable

/-- The bounded real Lipschitz multiplier has its pointwise representative. -/
theorem lipschitzBoundedSMul_coeFn {N q : ℕ} (b : Configuration N → ℝ)
    (B : ℝ) (hB : ∀ x, ‖b x‖ ≤ B) {C : ℝ≥0} (hb : LipschitzWith C b)
    (u : State N q) :
    ⇑(lipschitzBoundedSMul b B hB hb u) =ᵐ[volume] fun x => (b x : ℂ) • u x :=
  boundedSMul_coeFn _ _ _ _ _

/-- The `L²` state represented by a coordinate derivative of a Lipschitz multiplier times a
state.  This is the lower-order term in the weak product rule. -/
noncomputable def lipschitzDerivativeSMul {N q : ℕ} (b : Configuration N → ℝ)
    (C : ℝ≥0) (hb : LipschitzWith C b) (a : Fin N × Fin 3) (u : State N q) : State N q :=
  boundedSMul (fun x => (lipschitzDirectionalDerivative b a x : ℂ)) u C
    (fun x => by simpa using norm_lipschitzDirectionalDerivative_le b C hb a x)
    (Complex.measurable_ofReal.comp
      (lipschitzDirectionalDerivative_measurable b a)).aestronglyMeasurable

/-- The derivative multiplier has the expected pointwise representative. -/
theorem lipschitzDerivativeSMul_coeFn {N q : ℕ} (b : Configuration N → ℝ)
    (C : ℝ≥0) (hb : LipschitzWith C b) (a : Fin N × Fin 3) (u : State N q) :
    ⇑(lipschitzDerivativeSMul b C hb a u) =ᵐ[volume]
      fun x => (lipschitzDirectionalDerivative b a x : ℂ) • u x :=
  boundedSMul_coeFn _ _ _ _ _

/-- The `L²` representative predicted by the weak product rule
`∂ₐ(bu) = b ∂ₐu + (∂ₐb)u`. -/
@[expose] noncomputable def lipschitzProductDerivative {N q : ℕ} (b : Configuration N → ℝ)
    (B : ℝ) (hB : ∀ x, ‖b x‖ ≤ B) (C : ℝ≥0) (hb : LipschitzWith C b)
    (a : Fin N × Fin 3) (u g : State N q) : State N q :=
  lipschitzBoundedSMul b B hB hb g + lipschitzDerivativeSMul b C hb a u

/-- The candidate product derivative agrees a.e. with the pointwise product-rule formula. -/
theorem lipschitzProductDerivative_coeFn {N q : ℕ} (b : Configuration N → ℝ)
    (B : ℝ) (hB : ∀ x, ‖b x‖ ≤ B) (C : ℝ≥0) (hb : LipschitzWith C b)
    (a : Fin N × Fin 3) (u g : State N q) :
    ⇑(lipschitzProductDerivative b B hB C hb a u g) =ᵐ[volume]
      fun x => (b x : ℂ) • g x + (lipschitzDirectionalDerivative b a x : ℂ) • u x := by
  filter_upwards [Lp.coeFn_add (lipschitzBoundedSMul b B hB hb g)
      (lipschitzDerivativeSMul b C hb a u),
    lipschitzBoundedSMul_coeFn b B hB hb g,
    lipschitzDerivativeSMul_coeFn b C hb a u] with x hadd hb' hd'
  change (lipschitzBoundedSMul b B hB hb g +
    lipschitzDerivativeSMul b C hb a u : State N q) x = _
  rw [hadd]
  simp only [Pi.add_apply, hb', hd']

end LiebThirring.Sobolev

end
