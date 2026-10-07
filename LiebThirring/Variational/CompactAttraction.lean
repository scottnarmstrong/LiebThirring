/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Variational.FormIntegralBounds
public import LiebThirring.Variational.FormFinite
public import LiebThirring.Variational.CompactMass

/-! # Singular expectations under strong mass convergence

Second weighted moments control first weighted expectation differences by
the unweighted L² distance. This is the estimate needed for the attractive Coulomb limit.
-/

public section

open MeasureTheory
open scoped ENNReal NNReal

namespace LiebThirring
open Assembly

/-- The first-weight product is integrable, and its integral is controlled by mass in the
first factor and the second weighted moment in the second factor. -/
theorem integral_weight_norm_mul_le {N q : ℕ}
    (p : Configuration N → ℝ≥0∞) (hp : AEMeasurable p)
    (u v : State N q)
    (hv : (∫⁻ x : Configuration N, p x ^ 2 * (‖v x‖₊ : ℝ≥0∞) ^ 2) < ⊤) :
    Integrable (fun x => (p x).toReal * ‖u x‖ * ‖v x‖) ∧
      (∫ x, (p x).toReal * ‖u x‖ * ‖v x‖) ≤
        ‖u‖ * Real.sqrt (∫⁻ x : Configuration N,
          p x ^ 2 * (‖v x‖₊ : ℝ≥0∞) ^ 2).toReal := by
  let a : Configuration N → ℝ := fun x => ‖u x‖
  let b : Configuration N → ℝ := fun x => (p x).toReal * ‖v x‖
  have ha : MemLp a 2 volume := (Lp.memLp u).norm
  have hb : MemLp b 2 volume := by
    have h := memLp_sqrt_weight_norm (hp.pow_const 2) (Lp.aestronglyMeasurable v) hv
    simpa only [ENNReal.toReal_pow, Real.sqrt_sq ENNReal.toReal_nonneg] using h
  have hcs := integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two
    (show MemLp a (ENNReal.ofReal 2) volume by simpa only [ENNReal.ofReal_ofNat] using ha)
    (show MemLp b (ENNReal.ofReal 2) volume by simpa only [ENNReal.ofReal_ofNat] using hb)
  have ha0 (x) : 0 ≤ a x := norm_nonneg _
  have hb0 (x) : 0 ≤ b x := mul_nonneg ENNReal.toReal_nonneg (norm_nonneg _)
  simp only [Real.norm_eq_abs, abs_of_nonneg (ha0 _), abs_of_nonneg (hb0 _),
    ← Real.sqrt_eq_rpow, Real.rpow_two] at hcs
  have hbi : (∫ x, b x ^ 2) =
      (∫⁻ x : Configuration N, p x ^ 2 * (‖v x‖₊ : ℝ≥0∞) ^ 2).toReal := by
    simpa only [b, mul_pow, ENNReal.toReal_pow] using
      integral_weight_norm_sq (hp.pow_const 2) (Lp.aestronglyMeasurable v) hv
  rw [show (∫ x, a x ^ 2) = ‖u‖ ^ 2 from integral_state_norm_sq u,
    Real.sqrt_sq (norm_nonneg _), hbi] at hcs
  have he (x : Configuration N) : a x * b x = (p x).toReal * ‖u x‖ * ‖v x‖ := by
    dsimp only [a, b]
    ring
  refine ⟨(ha.integrable_mul hb).congr (Filter.Eventually.of_forall he), ?_⟩
  simpa only [he] using hcs

/-- Strong L² distance controls singular first-moment differences using the two second
moments. No convergence of derivatives and no normalization or antisymmetry is needed. -/
theorem abs_weight_expectation_sub_le {N q : ℕ}
    (p : Configuration N → ℝ≥0∞) (hp : AEMeasurable p)
    (u v : State N q)
    (hu : (∫⁻ x : Configuration N, p x ^ 2 * (‖u x‖₊ : ℝ≥0∞) ^ 2) < ⊤)
    (hv : (∫⁻ x : Configuration N, p x ^ 2 * (‖v x‖₊ : ℝ≥0∞) ^ 2) < ⊤) :
    |(∫⁻ x : Configuration N, p x * (‖u x‖₊ : ℝ≥0∞) ^ 2).toReal -
      (∫⁻ x : Configuration N, p x * (‖v x‖₊ : ℝ≥0∞) ^ 2).toReal| ≤
    ‖u - v‖ * (Real.sqrt (∫⁻ x : Configuration N,
      p x ^ 2 * (‖u x‖₊ : ℝ≥0∞) ^ 2).toReal +
        Real.sqrt (∫⁻ x : Configuration N, p x ^ 2 * (‖v x‖₊ : ℝ≥0∞) ^ 2).toReal) := by
  have hm (w : State N q) : (∫⁻ x : Configuration N, (‖w x‖₊ : ℝ≥0∞) ^ 2) < ⊤ := by
    rw [lintegral_state_norm_sq]
    exact ENNReal.pow_lt_top ENNReal.coe_lt_top
  have hfu := (lintegral_weight_first_le hp (Lp.aestronglyMeasurable u) (hm u) hu).1
  have hfv := (lintegral_weight_first_le hp (Lp.aestronglyMeasurable v) (hm v) hv).1
  have hiu := integrable_weight_norm_sq hp (Lp.aestronglyMeasurable u) hfu
  have hiv := integrable_weight_norm_sq hp (Lp.aestronglyMeasurable v) hfv
  have hcu := integral_weight_norm_mul_le p hp (u - v) u hu
  have hcv := integral_weight_norm_mul_le p hp (u - v) v hv
  rw [← integral_weight_norm_sq hp (Lp.aestronglyMeasurable u) hfu,
    ← integral_weight_norm_sq hp (Lp.aestronglyMeasurable v) hfv,
    ← integral_sub hiu hiv, ← Real.norm_eq_abs]
  calc
    _ ≤ ∫ x : Configuration N,
        ‖(p x).toReal * ‖u x‖ ^ 2 - (p x).toReal * ‖v x‖ ^ 2‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ x : Configuration N,
        ((p x).toReal * ‖(u - v) x‖ * ‖u x‖ +
          (p x).toReal * ‖(u - v) x‖ * ‖v x‖) := by
      apply integral_mono_ae (hiu.sub hiv).norm (hcu.1.add hcv.1)
      filter_upwards [Lp.coeFn_sub u v] with x hx
      simp only [Pi.sub_apply] at hx
      simp only [Pi.sub_apply, Pi.add_apply]
      rw [hx, ← mul_sub, Real.norm_eq_abs, abs_mul,
        abs_of_nonneg ENNReal.toReal_nonneg]
      have hs : |‖u x‖ ^ 2 - ‖v x‖ ^ 2| ≤ ‖u x - v x‖ * (‖u x‖ + ‖v x‖) := by
        rw [sq_sub_sq, abs_mul, abs_of_nonneg
          (add_nonneg (norm_nonneg (u x)) (norm_nonneg (v x)))]
        rw [mul_comm (‖u x‖ + ‖v x‖)]
        exact mul_le_mul_of_nonneg_right (abs_norm_sub_norm_le (u x) (v x))
          (add_nonneg (norm_nonneg (u x)) (norm_nonneg (v x)))
      calc
        _ ≤ (p x).toReal * (‖u x - v x‖ * (‖u x‖ + ‖v x‖)) :=
          mul_le_mul_of_nonneg_left hs ENNReal.toReal_nonneg
        _ = _ := by ring
    _ = (∫ x, (p x).toReal * ‖(u - v) x‖ * ‖u x‖) +
        (∫ x, (p x).toReal * ‖(u - v) x‖ * ‖v x‖) := integral_add hcu.1 hcv.1
    _ ≤ _ := by
      rw [mul_add]
      exact add_le_add hcu.2 hcv.2

/-- Inverse-square Hardy bounds the second Coulomb moment by the full kinetic energy. -/
theorem sqrt_nucleus_second_moment_le {N q : ℕ} (i : Fin N) (c : Position)
    (u : State N q) (hu : kineticEnergy u < ⊤) :
    Real.sqrt (∫⁻ x : Configuration N, coulombKernel (particlePosition x i) c ^ 2 *
      (‖u x‖₊ : ℝ≥0∞) ^ 2).toReal ≤ 2 * Real.sqrt (kineticEnergy u).toReal := by
  have hkin : (4 : ℝ≥0∞) * particleFourierEnergy u i ≤ 4 * kineticEnergy u := by
    gcongr
    exact realForm_particleFourierEnergy_le i u
  have hle := (lintegral_nucleus_coulomb_sq_le i c u).trans hkin
  have hfin : (4 : ℝ≥0∞) * kineticEnergy u ≠ ⊤ :=
    (ENNReal.mul_lt_top (by norm_num) hu).ne
  have hr := ENNReal.toReal_mono hfin hle
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofNat] at hr
  apply (Real.sqrt_le_sqrt hr).trans_eq
  rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
  have h4 : Real.sqrt (4 : ℝ) = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
  rw [h4]

/-- Singular Coulomb expectation differences are controlled by strong L² distance and
the two kinetic energies, with the Hardy constant and physical Fourier normalization. -/
theorem abs_nucleus_expectation_sub_le {N q : ℕ} (i : Fin N) (c : Position)
    (u v : State N q) (hu : kineticEnergy u < ⊤) (hv : kineticEnergy v < ⊤) :
    |(∫⁻ x : Configuration N, coulombKernel (particlePosition x i) c *
        (‖u x‖₊ : ℝ≥0∞) ^ 2).toReal -
      (∫⁻ x : Configuration N, coulombKernel (particlePosition x i) c *
        (‖v x‖₊ : ℝ≥0∞) ^ 2).toReal| ≤
      2 * ‖u - v‖ * (Real.sqrt (kineticEnergy u).toReal +
        Real.sqrt (kineticEnergy v).toReal) := by
  have hs (w : State N q) (hw : kineticEnergy w < ⊤) :
      (∫⁻ x : Configuration N, coulombKernel (particlePosition x i) c ^ 2 *
        (‖w x‖₊ : ℝ≥0∞) ^ 2) < ⊤ :=
    (lintegral_nucleus_coulomb_sq_le i c w).trans_lt
      (ENNReal.mul_lt_top (a := 4) (by norm_num : (4 : ℝ≥0∞) < ⊤)
        ((Assembly.realForm_particleFourierEnergy_le i w).trans_lt hw))
  have hp : Measurable (fun x : Configuration N => coulombKernel (particlePosition x i) c) :=
    ((measurable_particlePosition i).sub (measurable_const (a := c))).norm.ennreal_ofReal.inv
  calc
    _ ≤ ‖u - v‖ *
        (Real.sqrt (∫⁻ x : Configuration N, coulombKernel (particlePosition x i) c ^ 2 *
          (‖u x‖₊ : ℝ≥0∞) ^ 2).toReal +
        Real.sqrt (∫⁻ x : Configuration N, coulombKernel (particlePosition x i) c ^ 2 *
          (‖v x‖₊ : ℝ≥0∞) ^ 2).toReal) :=
      abs_weight_expectation_sub_le (N := N) (q := q)
        (fun x => coulombKernel (particlePosition x i) c) hp.aemeasurable u v (hs u hu) (hs v hv)
    _ ≤ ‖u - v‖ * (2 * Real.sqrt (kineticEnergy u).toReal +
        2 * Real.sqrt (kineticEnergy v).toReal) :=
      mul_le_mul_of_nonneg_left (add_le_add
        (sqrt_nucleus_second_moment_le i c u hu)
        (sqrt_nucleus_second_moment_le i c v hv)) (norm_nonneg _)
    _ = _ := by ring

/-- Each nuclear singular expectation is continuous along globally strongly L²-convergent
sequences with uniformly bounded kinetic energy. No strong derivative convergence is used. -/
theorem tendsto_nucleus_expectation_of_tendsto_Lp {N q : ℕ}
    (i : Fin N) (c : Position) {u : ℕ → State N q} {v : State N q}
    (hu : Filter.Tendsto u Filter.atTop (nhds v))
    (hTu : ∀ n, kineticEnergy (u n) < ⊤) (hTv : kineticEnergy v < ⊤)
    (K : ℝ) (hK : ∀ n, (kineticEnergy (u n)).toReal ≤ K) :
    Filter.Tendsto (fun n => (∫⁻ x : Configuration N,
      coulombKernel (particlePosition x i) c * (‖u n x‖₊ : ℝ≥0∞) ^ 2).toReal)
      Filter.atTop (nhds (∫⁻ x : Configuration N,
        coulombKernel (particlePosition x i) c * (‖v x‖₊ : ℝ≥0∞) ^ 2).toReal) := by
  have hd : Filter.Tendsto (fun n => ‖u n - v‖) Filter.atTop (nhds 0) := by
    simpa only [sub_self, norm_zero] using (hu.sub
      (tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ => v) Filter.atTop (nhds v))).norm
  have hb (n : ℕ) := (abs_nucleus_expectation_sub_le i c (u n) v (hTu n) hTv).trans
    (mul_le_mul_of_nonneg_left
      (add_le_add (Real.sqrt_le_sqrt (hK n)) le_rfl) (by positivity))
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simp only [Real.norm_eq_abs]
  apply squeeze_zero (fun n => abs_nonneg _) hb
  simpa only [mul_zero, zero_mul] using
    (tendsto_const_nhds.mul hd).mul_const
      (Real.sqrt K + Real.sqrt (kineticEnergy v).toReal)

/-- The finite real attraction expectation is the literal finite sum of nuclear terms. -/
theorem attraction_expectation_eq_sum_real {N q M : ℕ} (z : Fin M → ℝ≥0)
    (R : Fin M → Position) (u : State N q) (hu : kineticEnergy u < ⊤) :
    (∫⁻ x : Configuration N, attraction z R x * (‖u x‖₊ : ℝ≥0∞) ^ 2).toReal =
      ∑ i : Fin N, ∑ k : Fin M, (z k : ℝ) *
        (∫⁻ x : Configuration N, coulombKernel (particlePosition x i) (R k) *
          (‖u x‖₊ : ℝ≥0∞) ^ 2).toReal := by
  have hf (i : Fin N) (k : Fin M) := (lintegral_nucleus_coulomb_le_sqrt i (R k) u hu).1
  rw [lintegral_attraction_eq_sum, ENNReal.toReal_sum (fun i _ =>
    (ENNReal.sum_lt_top.mpr (fun k _ => ENNReal.mul_lt_top ENNReal.coe_lt_top (hf i k))).ne)]
  simp only [ENNReal.toReal_sum (fun k _ =>
    (ENNReal.mul_lt_top ENNReal.coe_lt_top (hf _ k)).ne), ENNReal.toReal_mul,
    ENNReal.coe_toReal]

/-- The entire singular attraction converges under strong L² convergence and a uniform
kinetic-energy bound. This is the compactness attractive-term limit used in the existence proof. -/
theorem tendsto_attraction_expectation_of_tendsto_Lp {N q M : ℕ}
    (z : Fin M → ℝ≥0) (R : Fin M → Position) {u : ℕ → State N q} {v : State N q}
    (hu : Filter.Tendsto u Filter.atTop (nhds v))
    (hTu : ∀ n, kineticEnergy (u n) < ⊤) (hTv : kineticEnergy v < ⊤)
    (K : ℝ) (hK : ∀ n, (kineticEnergy (u n)).toReal ≤ K) :
    Filter.Tendsto (fun n => (∫⁻ x : Configuration N,
      attraction z R x * (‖u n x‖₊ : ℝ≥0∞) ^ 2).toReal)
      Filter.atTop (nhds (∫⁻ x : Configuration N,
        attraction z R x * (‖v x‖₊ : ℝ≥0∞) ^ 2).toReal) := by
  have he : (fun n => (∫⁻ x : Configuration N,
      attraction z R x * (‖u n x‖₊ : ℝ≥0∞) ^ 2).toReal) =
      (fun n => ∑ i : Fin N, ∑ k : Fin M, (z k : ℝ) *
        (∫⁻ x : Configuration N, coulombKernel (particlePosition x i) (R k) *
          (‖u n x‖₊ : ℝ≥0∞) ^ 2).toReal) :=
    funext fun n => attraction_expectation_eq_sum_real z R (u n) (hTu n)
  rw [he, attraction_expectation_eq_sum_real z R v hTv]
  apply tendsto_finsetSum
  intro i _
  apply tendsto_finsetSum
  intro k _
  exact (tendsto_nucleus_expectation_of_tendsto_Lp i (R k) hu hTu hTv K hK).const_mul _

end LiebThirring

end
