/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Ionization.WeightedSum
public import LiebThirring.Variational.WeakEigenfunction

/-! # The weak equation tested with the admissible sum weight

The finite-sum identity is on the full finite-energy domain. It never applies
the weak equation to an individual selected-coordinate weighted state.
-/

public section
open MeasureTheory
open scoped ENNReal NNReal FourierTransform
namespace LiebThirring

/-- A weighted L² pairing distributes over a finite sum in its first slot. -/
theorem integral_mul_inner_sum_left {α F ι : Type*} [MeasurableSpace α]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] {μ : Measure α}
    (s : Finset ι) (a : α → ℂ) (f : ι → Lp F 2 μ) (g : Lp F 2 μ)
    (hi : ∀ i ∈ s, Integrable (fun x => a x * inner ℂ (f i x) (g x)) μ) :
    (∫ x, a x * inner ℂ ((∑ i ∈ s, f i) x) (g x) ∂μ) =
      ∑ i ∈ s, ∫ x, a x * inner ℂ (f i x) (g x) ∂μ := by
  rw [← integral_finsetSum s hi]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_finsetSum s f] with x hx
  rw [hx]
  simp only [Finset.sum_apply, sum_inner, Finset.mul_sum]

/-- The full finite-energy form is additive over a finite sum in the first slot. -/
theorem fullEnergyForm_sum_left {N q M ι : ℕ} (z : Fin M → ℝ≥0)
    (R : Fin M → Position) (s : Finset (Fin ι)) (f : Fin ι → State N q)
    (g : State N q) (hf : ∀ i ∈ s, kineticEnergy (f i) < ⊤)
    (hg : kineticEnergy g < ⊤) :
    fullEnergyForm z R (∑ i ∈ s, f i) g = ∑ i ∈ s, fullEnergyForm z R (f i) g := by
  have hF : (𝓕 (∑ i ∈ s, f i) : State N q) = ∑ i ∈ s, (𝓕 (f i) : State N q) :=
    map_sum (Lp.fourierTransformₗᵢ (Configuration N) (SpinAmplitudes N q)) f s
  unfold fullEnergyForm
  rw [hF, integral_mul_inner_sum_left s _ _ _ (fun i hi =>
    integrable_fullEnergyForm_kinetic (f i) g (hf i hi) hg),
    integral_mul_inner_sum_left s _ _ _ (fun i hi =>
      integrable_fullEnergyForm_potential z R (f i) g (hf i hi) hg), sum_inner]
  simp only [Finset.mul_sum, Finset.sum_add_distrib]

/-- Testing the genuine weak equation with `Wε u` gives the sum of the
literal full-domain selected-coordinate defects. -/
theorem ionization_sum_weak_defect_eq_zero {N q M : ℕ} (z : Fin M → ℝ≥0)
    (R : Fin M → Position) (hR : Function.Injective R) (E : ℝ)
    (u : FormDomain N q)
    (heq : ∀ v : FormDomain N q, energyForm z R hR v u =
      (E : ℂ) * inner ℂ (v : State N q) (u : State N q))
    (ε : ℝ) (hε : 0 < ε) :
    ∑ i : Fin N, (fullEnergyForm z R
      (ionizationParticleState ε hε i (u : State N q)) (u : State N q) -
      (E : ℂ) * inner ℂ (ionizationParticleState ε hε i (u : State N q))
        (u : State N q)).re = 0 := by
  have htest := heq (ionizationSumFormTest ε hε u)
  change fullEnergyForm z R (ionizationSumState ε hε (u : State N q))
      (u : State N q) = (E : ℂ) * inner ℂ
      (ionizationSumState ε hε (u : State N q)) (u : State N q) at htest
  rw [ionizationSumState_eq_sum,
    fullEnergyForm_sum_left z R Finset.univ _ _
      (fun i _ => kineticEnergy_ionizationParticleState_lt_top ε hε i _ u.property.2)
      u.property.2, sum_inner, Finset.mul_sum] at htest
  rw [← Complex.re_sum, Finset.sum_sub_distrib, htest, sub_self, Complex.zero_re]

end LiebThirring
end
