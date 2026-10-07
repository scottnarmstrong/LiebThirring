/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Variational.FormBounds

/-! # Continuity in the literal Fourier form graph norm

form continuity: a quantitative difference estimate and its epsilon–delta consequence.
No L² subtype topology is substituted for the stronger graph topology.
-/

public section
open MeasureTheory
open scoped ENNReal NNReal
namespace LiebThirring

/-- Subtraction in the second slot. -/
theorem energyForm_sub_right {N q M : ℕ} (z : Fin M → ℝ≥0)
    (R : Fin M → Position) (hR : Function.Injective R) (φ ψ χ : FormDomain N q) :
    energyForm z R hR φ (ψ - χ) = energyForm z R hR φ ψ - energyForm z R hR φ χ := by
  rw [sub_eq_add_neg, energyForm_add_right, energyForm_neg_right, sub_eq_add_neg]

/-- Subtraction in the first slot. -/
theorem energyForm_sub_left {N q M : ℕ} (z : Fin M → ℝ≥0)
    (R : Fin M → Position) (hR : Function.Injective R) (φ ψ χ : FormDomain N q) :
    energyForm z R hR (φ - ψ) χ = energyForm z R hR φ χ - energyForm z R hR ψ χ := by
  rw [sub_eq_add_neg, energyForm_add_left, energyForm_neg_left, sub_eq_add_neg]

/-- A coarse graph triangle bound sufficient for continuity, without Hilbert packaging. -/
theorem formGraphNorm_add_le {N q : ℕ} (φ ψ : FormDomain N q) :
    formGraphNorm (φ + ψ) ≤ 2 * (formGraphNorm φ + formGraphNorm ψ) := by
  have hT := ENNReal.toReal_mono
    (ENNReal.mul_lt_top (by norm_num : (2 : ℝ≥0∞) < ⊤)
      (ENNReal.add_lt_top.mpr ⟨φ.property.2, ψ.property.2⟩)).ne
    (kineticEnergy_add_le (φ : State N q) (ψ : State N q))
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofNat,
    ENNReal.toReal_add φ.property.2.ne ψ.property.2.ne] at hT
  have hm : ‖(φ : State N q) + (ψ : State N q)‖ ^ 2 ≤
      2 * (‖(φ : State N q)‖ ^ 2 + ‖(ψ : State N q)‖ ^ 2) := by
    have h := norm_add_le (φ : State N q) (ψ : State N q)
    have hs := (sq_le_sq₀ (norm_nonneg _) (add_nonneg (norm_nonneg _) (norm_nonneg _))).mpr h
    nlinarith only [hs, sq_nonneg (‖(φ : State N q)‖ - ‖(ψ : State N q)‖)]
  apply (sq_le_sq₀ (formGraphNorm_nonneg _)
    (mul_nonneg (by norm_num) (add_nonneg (formGraphNorm_nonneg φ) (formGraphNorm_nonneg ψ)))).mp
  have hφ := formGraphNorm_sq φ
  have hψ := formGraphNorm_sq ψ
  rw [formGraphNorm_sq, formDomain_coe_add]
  have hprod := mul_nonneg (formGraphNorm_nonneg φ) (formGraphNorm_nonneg ψ)
  nlinarith only [hT, hm, hφ, hψ, hprod, sq_nonneg (formGraphNorm φ), sq_nonneg (formGraphNorm ψ)]

/-- The real diagonal has the standard sesquilinear difference bound. -/
theorem abs_realEnergy_sub_le {N q M : ℕ} (z : Fin M → ℝ≥0)
    (R : Fin M → Position) (hR : Function.Injective R) (φ ψ : FormDomain N q) :
    |realEnergy z R hR φ - realEnergy z R hR ψ| ≤
      (3 + (N.choose 2 : ℝ) ^ 2 + (N : ℝ) * (∑ k : Fin M, (z k : ℝ)) ^ 2 +
        (nuclearRepulsion z R).toReal) * formGraphNorm (φ - ψ) *
          (formGraphNorm φ + formGraphNorm ψ) := by
  have he : ((realEnergy z R hR φ - realEnergy z R hR ψ : ℝ) : ℂ) =
      energyForm z R hR (φ - ψ) φ + energyForm z R hR ψ (φ - ψ) := by
    rw [Complex.ofReal_sub, ← energyForm_self, ← energyForm_self,
      energyForm_sub_left, energyForm_sub_right]
    abel
  rw [← Real.norm_eq_abs, ← Complex.norm_real, he]
  apply (norm_add_le _ _).trans
  apply (add_le_add (norm_energyForm_le z R hR (φ - ψ) φ)
    (norm_energyForm_le z R hR ψ (φ - ψ))).trans_eq
  ring

/-- Epsilon–delta continuity of the real energy in the graph norm. -/
theorem realEnergy_continuous_formGraphNorm {N q M : ℕ} (z : Fin M → ℝ≥0)
    (R : Fin M → Position) (hR : Function.Injective R) (φ : FormDomain N q)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ψ : FormDomain N q, formGraphNorm (ψ - φ) < δ →
      |realEnergy z R hR ψ - realEnergy z R hR φ| < ε := by
  let C : ℝ := 3 + (N.choose 2 : ℝ) ^ 2 +
    (N : ℝ) * (∑ k : Fin M, (z k : ℝ)) ^ 2 + (nuclearRepulsion z R).toReal
  let A : ℝ := C * (2 + 3 * formGraphNorm φ) + 1
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hA : 0 < A := by
    dsimp only [A]
    exact add_pos_of_nonneg_of_pos (mul_nonneg hC
      (add_nonneg (by norm_num) (mul_nonneg (by norm_num) (formGraphNorm_nonneg φ)))) (by norm_num)
  refine ⟨min 1 (ε / A), lt_min (by norm_num) (div_pos hε hA), ?_⟩
  intro ψ hψ
  have hd1 : formGraphNorm (ψ - φ) < 1 := hψ.trans_le (min_le_left _ _)
  have hdε : formGraphNorm (ψ - φ) < ε / A := hψ.trans_le (min_le_right _ _)
  have htri : formGraphNorm ψ ≤ 2 * (formGraphNorm (ψ - φ) + formGraphNorm φ) := by
    simpa only [sub_add_cancel] using formGraphNorm_add_le (ψ - φ) φ
  have hsum : formGraphNorm ψ + formGraphNorm φ ≤ 2 + 3 * formGraphNorm φ := by
    linarith only [htri, hd1]
  calc
    _ ≤ C * formGraphNorm (ψ - φ) * (formGraphNorm ψ + formGraphNorm φ) :=
      abs_realEnergy_sub_le z R hR ψ φ
    _ ≤ C * formGraphNorm (ψ - φ) * (2 + 3 * formGraphNorm φ) :=
      mul_le_mul_of_nonneg_left hsum (mul_nonneg hC (formGraphNorm_nonneg _))
    _ ≤ A * formGraphNorm (ψ - φ) := by
      dsimp only [A]
      nlinarith only [formGraphNorm_nonneg (ψ - φ)]
    _ < ε := by
      rw [mul_comm]
      exact (lt_div_iff₀ hA).mp hdε

end LiebThirring
end
