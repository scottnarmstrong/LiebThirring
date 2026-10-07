/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Variational.FormCoulombSlices
public import LiebThirring.Variational.FormDomain

/-! # Finite unnormalized Coulomb expectations

Hardy estimates. All estimates apply without symmetry or
normalization.
-/

public section
open MeasureTheory
open scoped ENNReal NNReal
namespace LiebThirring
open Assembly

/-- The attraction kernel is measurable, including its collision values. -/
theorem measurable_attraction {N M : ℕ} (z : Fin M → ℝ≥0) (R : Fin M → Position) :
    Measurable (attraction (N := N) z R) := by
  unfold attraction
  have hk (i : Fin N) (k : Fin M) : Measurable (fun X : Configuration N =>
      (z k : ℝ≥0∞) * coulombKernel (particlePosition X i) (R k)) :=
    measurable_const.mul
      (((measurable_particlePosition i).sub measurable_const).norm.ennreal_ofReal.inv)
  exact Finset.measurable_sum _ (fun i _ => Finset.measurable_sum _ (fun k _ => hk i k))

/-- Attraction is the finite sum of its individual Coulomb expectations. -/
theorem lintegral_attraction_eq_sum {N q M : ℕ} (z : Fin M → ℝ≥0)
    (R : Fin M → Position) (ψ : State N q) :
    (∫⁻ X : Configuration N, attraction z R X * (‖ψ X‖₊ : ℝ≥0∞) ^ 2) =
      ∑ i : Fin N, ∑ k : Fin M, (z k : ℝ≥0∞) *
        ∫⁻ X : Configuration N,
          coulombKernel (particlePosition X i) (R k) * (‖ψ X‖₊ : ℝ≥0∞) ^ 2 := by
  unfold attraction
  simp_rw [Finset.sum_mul, mul_assoc]
  rw [lintegral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i _
    rw [lintegral_finsetSum]
    · exact Finset.sum_congr rfl (fun k _ => lintegral_const_mul' _ _ ENNReal.coe_ne_top)
    · intro k _
      exact measurable_const.mul ((measurable_coulombKernel.comp
        ((measurable_particlePosition i).prodMk measurable_const)).mul
          (measurable_state_norm_sq ψ))
  · intro i _
    exact Finset.measurable_sum _ (fun k _ => measurable_const.mul
      ((measurable_coulombKernel.comp
        ((measurable_particlePosition i).prodMk measurable_const)).mul
          (measurable_state_norm_sq ψ)))

/-- Attraction is finite for every finite-kinetic state. -/
theorem lintegral_attraction_lt_top {N q M : ℕ} (z : Fin M → ℝ≥0)
    (R : Fin M → Position) (ψ : State N q) (hT : kineticEnergy ψ < ⊤) :
    (∫⁻ X : Configuration N, attraction z R X * (‖ψ X‖₊ : ℝ≥0∞) ^ 2) < ⊤ := by
  rw [lintegral_attraction_eq_sum]
  apply ENNReal.sum_lt_top.mpr
  intro i _
  apply ENNReal.sum_lt_top.mpr
  intro k _
  exact ENNReal.mul_lt_top ENNReal.coe_lt_top
    (lintegral_nucleus_coulomb_le_sqrt i (R k) ψ hT).1

/-- Electron repulsion is finite for every finite-kinetic state. -/
theorem lintegral_electronRepulsion_lt_top {N q : ℕ} (ψ : State N q)
    (hT : kineticEnergy ψ < ⊤) :
    (∫⁻ X : Configuration N, electronRepulsion X * (‖ψ X‖₊ : ℝ≥0∞) ^ 2) < ⊤ :=
  lintegral_electronRepulsion_lt_top_of_one_body_bound
    (fun (c : Position) (u : Lp (SpinAmplitudes N q) 2 (volume : Measure Position)) =>
      lintegral_coulomb_le_of_fourier c u) ψ hT

/-- Coulomb finiteness on the unnormalized form domain. -/
theorem formDomain_coulomb_lt_top {N q M : ℕ} (z : Fin M → ℝ≥0)
    (R : Fin M → Position) (hR : Function.Injective R) (ψ : FormDomain N q) :
    (∫⁻ X : Configuration N, attraction z R X * (‖(ψ : State N q) X‖₊ : ℝ≥0∞) ^ 2) < ⊤ ∧
    (∫⁻ X : Configuration N, electronRepulsion X * (‖(ψ : State N q) X‖₊ : ℝ≥0∞) ^ 2) < ⊤ ∧
    nuclearRepulsion z R < ⊤ :=
  ⟨lintegral_attraction_lt_top z R (ψ : State N q) ψ.property.2,
    lintegral_electronRepulsion_lt_top (ψ : State N q) ψ.property.2, nuclearRepulsion_lt_top z R hR⟩

/-- Particle kinetic energies sum in the real finite form. -/
theorem sum_particleFourierEnergy_toReal {N q : ℕ} (ψ : State N q)
    (hT : kineticEnergy ψ < ⊤) :
    (∑ i : Fin N, (particleFourierEnergy ψ i).toReal) = (kineticEnergy ψ).toReal := by
  rw [kineticEnergy_eq_sum_particleFourierEnergy]
  exact (ENNReal.toReal_sum (fun i _ =>
    ((realForm_particleFourierEnergy_le i ψ).trans_lt hT).ne)).symm

/-- Sharp unnormalized attraction estimate. -/
theorem lintegral_attraction_toReal_le_sqrt {N q M : ℕ} (z : Fin M → ℝ≥0)
    (R : Fin M → Position) (ψ : State N q) (hT : kineticEnergy ψ < ⊤) :
    (∫⁻ X : Configuration N, attraction z R X * (‖ψ X‖₊ : ℝ≥0∞) ^ 2).toReal ≤
      2 * (∑ k : Fin M, (z k : ℝ)) *
        Real.sqrt ((N : ℝ) * ‖ψ‖ ^ 2 * (kineticEnergy ψ).toReal) := by
  have hf (i : Fin N) (k : Fin M) :=
    (lintegral_nucleus_coulomb_le_sqrt i (R k) ψ hT).1
  rw [lintegral_attraction_eq_sum, ENNReal.toReal_sum (fun i _ =>
    (ENNReal.sum_lt_top.mpr (fun k _ => ENNReal.mul_lt_top ENNReal.coe_lt_top (hf i k))).ne)]
  simp_rw [ENNReal.toReal_sum (fun k _ =>
    (ENNReal.mul_lt_top ENNReal.coe_lt_top (hf _ k)).ne), ENNReal.toReal_mul,
    ENNReal.coe_toReal]
  have hsum : (∑ i : Fin N, Real.sqrt (‖ψ‖ ^ 2 * (particleFourierEnergy ψ i).toReal)) ≤
      Real.sqrt ((N : ℝ) * ‖ψ‖ ^ 2 * (kineticEnergy ψ).toReal) := by
    have h := Real.sum_sqrt_mul_sqrt_le (Finset.univ : Finset (Fin N))
      (f := fun _ => ‖ψ‖ ^ 2) (g := fun i => (particleFourierEnergy ψ i).toReal)
      (fun _ => sq_nonneg _) (fun _ => ENNReal.toReal_nonneg)
    simp_rw [← Real.sqrt_mul (sq_nonneg ‖ψ‖)] at h
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      sum_particleFourierEnergy_toReal ψ hT, ← Real.sqrt_mul (mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)),
      mul_assoc] using h
  calc
    _ ≤ ∑ i : Fin N, ∑ k : Fin M,
        (z k : ℝ) * (2 * Real.sqrt (‖ψ‖ ^ 2 * (particleFourierEnergy ψ i).toReal)) :=
      Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun k _ =>
        mul_le_mul_of_nonneg_left (lintegral_nucleus_coulomb_le_sqrt i (R k) ψ hT).2 (z k).coe_nonneg))
    _ = 2 * (∑ k : Fin M, (z k : ℝ)) *
        ∑ i : Fin N, Real.sqrt (‖ψ‖ ^ 2 * (particleFourierEnergy ψ i).toReal) := by
      simp only [← Finset.sum_mul, ← Finset.mul_sum]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hsum (by positivity)

/-- Scalar Young inequality in the form used for infinitesimal form bounds. -/
theorem two_mul_sqrt_mul_le {m t a δ : ℝ} (hm : 0 ≤ m) (ht : 0 ≤ t)
    (hδ : 0 < δ) :
    2 * a * Real.sqrt (m * t) ≤ δ * t + a ^ 2 / δ * m := by
  rw [Real.sqrt_mul hm]
  have h := two_mul_le_add_sq (δ * Real.sqrt t) (a * Real.sqrt m)
  rw [mul_pow, mul_pow, Real.sq_sqrt ht, Real.sq_sqrt hm] at h
  apply (mul_le_mul_iff_right₀ hδ).mp
  have he : δ * (δ * t + a ^ 2 / δ * m) = δ ^ 2 * t + a ^ 2 * m := by
    field_simp
  rw [he]
  nlinarith only [h]

/-- Attraction has an arbitrarily small relative kinetic coefficient. -/
theorem lintegral_attraction_toReal_le {N q M : ℕ} (z : Fin M → ℝ≥0)
    (R : Fin M → Position) (ψ : State N q) (hT : kineticEnergy ψ < ⊤)
    {δ : ℝ} (hδ : 0 < δ) :
    (∫⁻ X : Configuration N, attraction z R X * (‖ψ X‖₊ : ℝ≥0∞) ^ 2).toReal ≤
      δ * (kineticEnergy ψ).toReal +
        ((N : ℝ) * (∑ k : Fin M, (z k : ℝ)) ^ 2 / δ) * ‖ψ‖ ^ 2 := by
  have h := two_mul_sqrt_mul_le (m := (N : ℝ) * ‖ψ‖ ^ 2)
    (t := (kineticEnergy ψ).toReal) (a := ∑ k : Fin M, (z k : ℝ))
    (mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)) ENNReal.toReal_nonneg
    hδ
  apply (lintegral_attraction_toReal_le_sqrt z R ψ hT).trans
  convert h using 1
  ring

end LiebThirring
end
