/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.ThermoClusters.TensorExpectations
public import LiebThirring.Screening.Integrability

/-! # Real cross Coulomb energy in the electron–nucleus charge representation

The four-term expression is the mutual energy of the signed charges
`z μ_nuc − μ_el`. When the positive pair integrals are finite, their
extended-value formulation agrees with ordinary double Coulomb integrals.
Lieb–Lebowitz (1972) II.E (2.25).
-/

public section
open MeasureTheory
open scoped ENNReal
namespace LiebThirring

/-- Real mutual energy in the four-positive-measure charge representation. -/
@[expose] noncomputable def clusterChargeInteraction (z : ℕ)
    (μe μn νe νn : Measure Position) : ℝ :=
  (clusterCoulombInteraction μe νe).toReal +
    (z : ℝ)^2 * (clusterCoulombInteraction μn νn).toReal -
    (z : ℝ) * (clusterCoulombInteraction μe νn).toReal -
    (z : ℝ) * (clusterCoulombInteraction μn νe).toReal

/-- Finite positive mutual energy agrees with the ordinary double inverse-distance integral. -/
theorem clusterCoulombInteraction_toReal (μ ν : Measure Position) [SFinite μ] [SFinite ν]
    (hfin : clusterCoulombInteraction μ ν < ⊤) :
    (clusterCoulombInteraction μ ν).toReal = ∫ x, ∫ y, ‖x-y‖⁻¹ ∂ν ∂μ := by
  have hm : AEMeasurable (fun Z : Position × Position => coulombKernel Z.1 Z.2) (μ.prod ν) :=
    measurable_coulombKernel.aemeasurable
  have hi := integrable_toReal_of_lintegral_ne_top hm hfin.ne
  have ht := integral_toReal hm (ae_lt_top measurable_coulombKernel hfin.ne)
  rw [clusterCoulombInteraction]
  rw [← ht, integral_prod _ hi]
  simp only [← inverse_norm_eq_coulombKernel_toReal]

/-- The signed-charge cross formula is exactly its four ordinary Coulomb integrals. -/
theorem clusterChargeInteraction_eq_four_integrals (z : ℕ) (μe μn νe νn : Measure Position)
    [IsFiniteMeasure μe] [IsFiniteMeasure μn] [IsFiniteMeasure νe] [IsFiniteMeasure νn]
    (hee : clusterCoulombInteraction μe νe < ⊤)
    (hnn : clusterCoulombInteraction μn νn < ⊤)
    (hen : clusterCoulombInteraction μe νn < ⊤)
    (hne : clusterCoulombInteraction μn νe < ⊤) :
    clusterChargeInteraction z μe μn νe νn =
      (∫ x, ∫ y, ‖x-y‖⁻¹ ∂νe ∂μe) +
      (z : ℝ)^2 * (∫ x, ∫ y, ‖x-y‖⁻¹ ∂νn ∂μn) -
      (z : ℝ) * (∫ x, ∫ y, ‖x-y‖⁻¹ ∂νn ∂μe) -
      (z : ℝ) * (∫ x, ∫ y, ‖x-y‖⁻¹ ∂νe ∂μn) := by
  rw [clusterChargeInteraction, clusterCoulombInteraction_toReal μe νe hee,
    clusterCoulombInteraction_toReal μn νn hnn, clusterCoulombInteraction_toReal μe νn hen,
    clusterCoulombInteraction_toReal μn νe hne]

/-- Cross charge energy is additive over a finite second-cluster family when every pair is finite. -/
theorem clusterChargeInteraction_sum_right {ι : Type*} [Fintype ι] (z : ℕ)
    (μe μn : Measure Position) (νe νn : ι → Measure Position)
    [∀ i, IsFiniteMeasure (νe i)] [∀ i, IsFiniteMeasure (νn i)]
    (hee : ∀ i, clusterCoulombInteraction μe (νe i) < ⊤)
    (hnn : ∀ i, clusterCoulombInteraction μn (νn i) < ⊤)
    (hen : ∀ i, clusterCoulombInteraction μe (νn i) < ⊤)
    (hne : ∀ i, clusterCoulombInteraction μn (νe i) < ⊤) :
    clusterChargeInteraction z μe μn (∑ i, νe i) (∑ i, νn i) =
      ∑ i, clusterChargeInteraction z μe μn (νe i) (νn i) := by
  classical
  simp only [clusterChargeInteraction, clusterCoulombInteraction_sum_right]
  rw [ENNReal.toReal_sum (fun i _ => (hee i).ne),
    ENNReal.toReal_sum (fun i _ => (hnn i).ne),
    ENNReal.toReal_sum (fun i _ => (hen i).ne),
    ENNReal.toReal_sum (fun i _ => (hne i).ne)]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]

end LiebThirring
end
