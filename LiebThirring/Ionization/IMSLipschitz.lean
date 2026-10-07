/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Ionization.IMSAlgebra
public import LiebThirring.Variational.CompactMass
public import LiebThirring.Variational.FormFinite
public import LiebThirring.Sobolev.LipschitzProductRule

/-! # IMS localization for bounded Lipschitz partitions

The correction uses the actual a.e. derivatives of the multipliers.  Thus a sharp
pointwise bound on the summed squared gradient passes to the energy identity without
a dimension or partition-cardinality loss.
-/

public section

open MeasureTheory WithLp
open scoped ENNReal NNReal

namespace LiebThirring
open Sobolev Assembly

/-- The differentiated square-partition identity holds almost everywhere for a finite
Lipschitz partition. -/
theorem ae_sum_partition_mul_lipschitzDirectionalDerivative_eq_zero
    {ι : Type*} [Fintype ι] {N : ℕ}
    (b : ι → Configuration N → ℝ) (C : ι → ℝ≥0)
    (hb : ∀ s, LipschitzWith (C s) (b s))
    (hpart : ∀ x, ∑ s, b s x ^ 2 = 1) :
    ∀ᵐ x ∂(volume : Measure (Configuration N)), ∀ a : Fin N × Fin 3,
      ∑ s, b s x * lipschitzDirectionalDerivative (b s) a x = 0 := by
  have hd : ∀ᵐ x ∂(volume : Measure (Configuration N)), ∀ s,
      DifferentiableAt ℝ (b s) x :=
    ae_all_iff.mpr fun s => (hb s).ae_differentiableAt_configuration
  filter_upwards [hd] with x hx
  intro a
  have hs : HasFDerivAt (fun y => ∑ s, b s y ^ 2)
      (∑ s, (2 * b s x) • fderiv ℝ (b s) x) x := by
    apply HasFDerivAt.fun_sum
    intro s _
    simpa only [Nat.reduceSub, pow_one, two_smul, two_mul] using (hx s).hasFDerivAt.pow 2
  have hconst : (fun y => ∑ s, b s y ^ 2) = fun _ => (1 : ℝ) := funext hpart
  rw [hconst] at hs
  have he := congrArg (fun f : Configuration N →L[ℝ] ℝ => f (coordinateVector a)) hs.fderiv
  rw [fderiv_const_apply 1] at he
  simp only [zero_apply] at he
  rw [show (∑ s, (2 * b s x) • fderiv ℝ (b s) x) =
      Finset.univ.sum (fun s => (2 * b s x) • fderiv ℝ (b s) x) from rfl,
    sum_apply] at he
  simp only [smul_apply, smul_eq_mul] at he
  have htwo : (∑ s, (2 * b s x) * fderiv ℝ (b s) x (coordinateVector a)) =
      2 * ∑ s, b s x * fderiv ℝ (b s) x (coordinateVector a) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s _
    ring
  rw [htwo] at he
  exact (mul_eq_zero.mp he.symm).resolve_left (by norm_num)

/-- The integrated square identity for one weak coordinate and a finite Lipschitz partition. -/
theorem sum_norm_lipschitzProductDerivative_sq {ι : Type*} [Fintype ι]
    {N q : ℕ} (b : ι → Configuration N → ℝ) (B : ι → ℝ)
    (hB : ∀ s x, ‖b s x‖ ≤ B s) (C : ι → ℝ≥0)
    (hb : ∀ s, LipschitzWith (C s) (b s))
    (hpart : ∀ x, ∑ s, b s x ^ 2 = 1) (a : Fin N × Fin 3) (u g : State N q) :
    (∑ s, ‖lipschitzProductDerivative (b s) (B s) (hB s) (C s) (hb s) a u g‖ ^ 2) =
      ‖g‖ ^ 2 + ∑ s, ‖lipschitzDerivativeSMul (b s) (C s) (hb s) a u‖ ^ 2 := by
  have hrep : ∀ᵐ x ∂(volume : Measure (Configuration N)), ∀ s,
      lipschitzProductDerivative (b s) (B s) (hB s) (C s) (hb s) a u g x =
        (b s x : ℂ) • g x + (lipschitzDirectionalDerivative (b s) a x : ℂ) • u x :=
    ae_all_iff.mpr fun s => lipschitzProductDerivative_coeFn _ _ _ _ _ _ _ _
  have hdrep : ∀ᵐ x ∂(volume : Measure (Configuration N)), ∀ s,
      lipschitzDerivativeSMul (b s) (C s) (hb s) a u x =
        (lipschitzDirectionalDerivative (b s) a x : ℂ) • u x :=
    ae_all_iff.mpr fun s => lipschitzDerivativeSMul_coeFn _ _ _ _ _
  have hcross := ae_sum_partition_mul_lipschitzDirectionalDerivative_eq_zero b C hb hpart
  simp_rw [← integral_state_norm_sq]
  rw [← integral_finsetSum, ← integral_finsetSum, ← integral_add]
  · apply integral_congr_ae
    filter_upwards [hrep, hdrep, hcross] with x hx hdx hcx
    simp only [hx, hdx, norm_smul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs,
      ← Finset.sum_mul]
    exact sum_norm_partition_product_sq (fun s => b s x)
      (fun s => lipschitzDirectionalDerivative (b s) a x) (hpart x) (hcx a) (u x) (g x)
  · exact integrable_state_norm_sq g
  · exact integrable_finsetSum _ (fun s _ => integrable_state_norm_sq _)
  · intro s _; exact integrable_state_norm_sq _
  · intro s _; exact integrable_state_norm_sq _

/-- Exact kinetic IMS for a finite bounded Lipschitz square partition. -/
theorem kineticEnergy_lipschitz_partition {ι : Type*} [Fintype ι]
    {N q : ℕ} (u : State N q) (hu : kineticEnergy u < ⊤)
    (b : ι → Configuration N → ℝ) (B : ι → ℝ)
    (hB : ∀ s x, ‖b s x‖ ≤ B s) (C : ι → ℝ≥0)
    (hb : ∀ s, LipschitzWith (C s) (b s))
    (hpart : ∀ x, ∑ s, b s x ^ 2 = 1) :
    (∑ s, (kineticEnergy (lipschitzBoundedSMul (b s) (B s) (hB s) (hb s) u)).toReal) =
      (kineticEnergy u).toReal + ∑ a : Fin N × Fin 3, ∑ s,
        ‖lipschitzDerivativeSMul (b s) (C s) (hb s) a u‖ ^ 2 := by
  obtain ⟨g, hg⟩ := exists_weakDerivatives_of_kineticEnergy_lt_top u hu
  have hprod (s : ι) := hasWeakDerivative_lipschitz_product u g hg
    (b s) (B s) (hB s) (C s) (hb s)
  simp_rw [kineticEnergy_toReal_eq_sum_weakDerivative_norm_sq _ _ (hprod _)]
  rw [Finset.sum_comm]
  simp_rw [sum_norm_lipschitzProductDerivative_sq b B hB C hb hpart]
  rw [Finset.sum_add_distrib, ← kineticEnergy_toReal_eq_sum_weakDerivative_norm_sq u g hg]

/-- The Lipschitz IMS correction is its literal full-gradient integral. -/
theorem lipschitz_partition_error_eq_integral {ι : Type*} [Fintype ι]
    {N q : ℕ} (u : State N q) (b : ι → Configuration N → ℝ)
    (C : ι → ℝ≥0) (hb : ∀ s, LipschitzWith (C s) (b s)) :
    (∑ a : Fin N × Fin 3, ∑ s,
      ‖lipschitzDerivativeSMul (b s) (C s) (hb s) a u‖ ^ 2) =
    ∫ x : Configuration N,
      (∑ a : Fin N × Fin 3, ∑ s,
        lipschitzDirectionalDerivative (b s) a x ^ 2) * ‖u x‖ ^ 2 := by
  have hi : Integrable (fun x => ∑ a : Fin N × Fin 3, ∑ s,
      ‖lipschitzDerivativeSMul (b s) (C s) (hb s) a u x‖ ^ 2) :=
    integrable_finsetSum _ (fun a _ => integrable_finsetSum _
      (fun s _ => integrable_state_norm_sq _))
  calc
    _ = ∫ x : Configuration N, ∑ a : Fin N × Fin 3, ∑ s,
        ‖lipschitzDerivativeSMul (b s) (C s) (hb s) a u x‖ ^ 2 := by
      rw [integral_finsetSum _ (fun a _ => integrable_finsetSum _
        (fun s _ => integrable_state_norm_sq _))]
      apply Finset.sum_congr rfl
      intro a _
      rw [integral_finsetSum _ (fun s _ => integrable_state_norm_sq _)]
      simp only [integral_state_norm_sq]
    _ = _ := by
      apply integral_congr_ae
      have hrep : ∀ᵐ x ∂(volume : Measure (Configuration N)), ∀ a s,
          lipschitzDerivativeSMul (b s) (C s) (hb s) a u x =
            (lipschitzDirectionalDerivative (b s) a x : ℂ) • u x :=
        ae_all_iff.mpr fun a => ae_all_iff.mpr fun s =>
          lipschitzDerivativeSMul_coeFn _ _ _ _ _
      filter_upwards [hrep] with x hx
      simp only [hx, norm_smul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs,
        Finset.sum_mul]

/-- A Lipschitz square partition preserves every nonnegative weighted expectation. -/
theorem lintegral_weight_lipschitz_partition {ι : Type*} [Fintype ι]
    {N q : ℕ} (u : State N q) (p : Configuration N → ℝ≥0∞) (hp : Measurable p)
    (b : ι → Configuration N → ℝ) (B : ι → ℝ)
    (hB : ∀ s x, ‖b s x‖ ≤ B s) (C : ι → ℝ≥0)
    (hb : ∀ s, LipschitzWith (C s) (b s)) (hpart : ∀ x, ∑ s, b s x ^ 2 = 1) :
    (∑ s, ∫⁻ x : Configuration N, p x *
      (‖lipschitzBoundedSMul (b s) (B s) (hB s) (hb s) u x‖₊ : ℝ≥0∞) ^ 2) =
      ∫⁻ x : Configuration N, p x * (‖u x‖₊ : ℝ≥0∞) ^ 2 := by
  have hrep : ∀ᵐ x ∂(volume : Measure (Configuration N)), ∀ s,
      lipschitzBoundedSMul (b s) (B s) (hB s) (hb s) u x = (b s x : ℂ) • u x :=
    ae_all_iff.mpr fun s => lipschitzBoundedSMul_coeFn _ _ _ _ _
  rw [← lintegral_finsetSum]
  · apply lintegral_congr_ae
    filter_upwards [hrep] with x hx
    have hn (s : ι) :
        (‖lipschitzBoundedSMul (b s) (B s) (hB s) (hb s) u x‖₊ : ℝ≥0∞) ^ 2 =
          ENNReal.ofReal (b s x ^ 2) * (‖u x‖₊ : ℝ≥0∞) ^ 2 := by
      rw [hx s]
      change ‖(b s x : ℂ) • u x‖ₑ ^ 2 = ENNReal.ofReal (b s x ^ 2) * ‖u x‖ₑ ^ 2
      rw [← ofReal_norm, norm_smul, Complex.norm_real, Real.norm_eq_abs,
        ENNReal.ofReal_mul (abs_nonneg _), mul_pow,
        ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs, ofReal_norm]
    simp_rw [hn]
    rw [← Finset.mul_sum, ← Finset.sum_mul,
      ← ENNReal.ofReal_sum_of_nonneg (fun s _ => sq_nonneg (b s x)), hpart x,
      ENNReal.ofReal_one, one_mul]
  · intro s _
    exact hp.mul (measurable_state_norm_sq _)

/-- Every bounded Lipschitz multiplier preserves finite kinetic energy. -/
theorem kineticEnergy_lipschitzMultiplier_lt_top {N q : ℕ} (u : State N q)
    (hu : kineticEnergy u < ⊤) (b : Configuration N → ℝ) (B : ℝ)
    (hB : ∀ x, ‖b x‖ ≤ B) (C : ℝ≥0) (hb : LipschitzWith C b) :
    kineticEnergy (lipschitzBoundedSMul b B hB hb u) < ⊤ :=
  kineticEnergy_lipschitzBoundedSMul_lt_top u hu b B hB C hb

/-- A bounded Lipschitz square partition preserves total mass. -/
theorem sum_norm_lipschitz_partition_sq {ι : Type*} [Fintype ι]
    {N q : ℕ} (u : State N q) (b : ι → Configuration N → ℝ) (B : ι → ℝ)
    (hB : ∀ s x, ‖b s x‖ ≤ B s) (C : ι → ℝ≥0)
    (hb : ∀ s, LipschitzWith (C s) (b s)) (hpart : ∀ x, ∑ s, b s x ^ 2 = 1) :
    (∑ s, ‖lipschitzBoundedSMul (b s) (B s) (hB s) (hb s) u‖ ^ 2) = ‖u‖ ^ 2 := by
  have h := lintegral_weight_lipschitz_partition u (fun _ => 1) measurable_const
    b B hB C hb hpart
  simp only [one_mul, lintegral_state_norm_sq] at h
  have hr := congrArg ENNReal.toReal h
  simpa only [ENNReal.toReal_sum (fun _ _ => ENNReal.pow_ne_top ENNReal.coe_ne_top),
    ENNReal.toReal_pow, ENNReal.coe_toReal, coe_nnnorm] using hr

/-- The full Coulomb quadratic expression satisfies IMS for bounded Lipschitz partitions. -/
theorem coulombEnergy_lipschitz_partition {ι : Type*} [Fintype ι]
    {N q M : ℕ} (z : Fin M → ℝ≥0) (R : Fin M → Position)
    (u : State N q) (hu : kineticEnergy u < ⊤)
    (b : ι → Configuration N → ℝ) (B : ι → ℝ)
    (hB : ∀ s x, ‖b s x‖ ≤ B s) (C : ι → ℝ≥0)
    (hb : ∀ s, LipschitzWith (C s) (b s)) (hpart : ∀ x, ∑ s, b s x ^ 2 = 1) :
    let v := fun s => lipschitzBoundedSMul (b s) (B s) (hB s) (hb s) u
    (kineticEnergy u).toReal +
      (∫⁻ x : Configuration N, electronRepulsion x * (‖u x‖₊ : ℝ≥0∞) ^ 2).toReal +
      (nuclearRepulsion z R).toReal * ‖u‖ ^ 2 -
      (∫⁻ x : Configuration N, attraction z R x * (‖u x‖₊ : ℝ≥0∞) ^ 2).toReal =
    (∑ s, ((kineticEnergy (v s)).toReal +
      (∫⁻ x : Configuration N, electronRepulsion x * (‖v s x‖₊ : ℝ≥0∞) ^ 2).toReal +
      (nuclearRepulsion z R).toReal * ‖v s‖ ^ 2 -
      (∫⁻ x : Configuration N, attraction z R x * (‖v s x‖₊ : ℝ≥0∞) ^ 2).toReal)) -
        ∑ a : Fin N × Fin 3, ∑ s,
          ‖lipschitzDerivativeSMul (b s) (C s) (hb s) a u‖ ^ 2 := by
  dsimp only
  have hv (s : ι) := kineticEnergy_lipschitzMultiplier_lt_top u hu
    (b s) (B s) (hB s) (C s) (hb s)
  have hrep := congrArg ENNReal.toReal (lintegral_weight_lipschitz_partition u
    electronRepulsion measurable_electronRepulsion b B hB C hb hpart)
  rw [ENNReal.toReal_sum (fun s _ => (lintegral_electronRepulsion_lt_top _ (hv s)).ne)] at hrep
  have hatt := congrArg ENNReal.toReal (lintegral_weight_lipschitz_partition u
    (attraction z R) (measurable_attraction z R) b B hB C hb hpart)
  rw [ENNReal.toReal_sum (fun s _ => (lintegral_attraction_lt_top z R _ (hv s)).ne)] at hatt
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [kineticEnergy_lipschitz_partition u hu b B hB C hb hpart, hrep, hatt,
    sum_norm_lipschitz_partition_sq u b B hB C hb hpart]
  abel

end LiebThirring

end
