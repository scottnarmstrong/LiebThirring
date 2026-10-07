/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Ionization.WeightedSum
public import LiebThirring.Ionization.PairInequalityAlgebra
public import LiebThirring.Variational.SpectatorCoulombReal
import LiebThirring.Sobolev.Collisions

/-! # Finite cutoff pair densities and their regrouping

Bounded radial weights multiply finite Coulomb densities.
Every exchange of an ordinary integral with a finite sum has explicit
integrability.
-/

public section
open MeasureTheory
open scoped ENNReal NNReal
namespace LiebThirring
open Variational

/-- The totalized real Coulomb kernel is the inverse Euclidean separation. -/
theorem coulombKernel_toReal (x y : Position) :
    (coulombKernel x y).toReal = ‖x - y‖⁻¹ := by
  rw [coulombKernel, ENNReal.toReal_inv, ENNReal.toReal_ofReal (norm_nonneg _)]

/-- Each finite-energy state has an integrable real pair Coulomb density. -/
theorem integrable_pair_coulomb_density {N q : ℕ} (i j : Fin N) (hij : i ≠ j)
    (u : FormDomain N q) : Integrable (fun X : Configuration N =>
      (coulombKernel (particlePosition X i) (particlePosition X j)).toReal *
        ‖(u : State N q) X‖ ^ 2) := by
  have hfin := (lintegral_pair_coulomb_le_sqrt i j hij (u : State N q) u.property.2).1
  have hm : AEMeasurable (fun X : Configuration N =>
      coulombKernel (particlePosition X i) (particlePosition X j)) :=
    (((measurable_particlePosition i).sub
      (measurable_particlePosition j)).norm.ennreal_ofReal.inv).aemeasurable
  have hmeas : AEMeasurable (fun X : Configuration N =>
      coulombKernel (particlePosition X i) (particlePosition X j) *
        (‖(u : State N q) X‖₊ : ℝ≥0∞) ^ 2) :=
    hm.mul ((Lp.aestronglyMeasurable (u : State N q)).nnnorm.aemeasurable.coe_nnreal_ennreal.pow_const 2)
  have hh := integrable_toReal_of_lintegral_ne_top hmeas hfin.ne
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.coe_toReal, coe_nnnorm]
    using hh

theorem integrable_ionization_ordered_pair_density {N q : ℕ} (ε : ℝ) (hε : 0 < ε)
    (i j : Fin N) (hij : i ≠ j) (u : FormDomain N q) :
    Integrable (fun X : Configuration N =>
      (ionizationParticleWeight ε i X / ‖particlePosition X i - particlePosition X j‖) *
        ‖(u : State N q) X‖ ^ 2) := by
  have hc := integrable_pair_coulomb_density i j hij u
  have hw : Integrable (fun X : Configuration N => ionizationParticleWeight ε i X *
      ((coulombKernel (particlePosition X i) (particlePosition X j)).toReal *
        ‖(u : State N q) X‖ ^ 2)) := hc.bdd_mul
    (lipschitzWith_ionizationParticleWeight ε hε.le i).continuous.measurable.aestronglyMeasurable
    (Filter.Eventually.of_forall (norm_ionizationParticleWeight_le ε hε i))
  apply hw.congr
  filter_upwards [] with X
  rw [coulombKernel_toReal, div_eq_mul_inv, mul_assoc]

/-- The numerator with both cutoff weights is an integrable pair density. -/
theorem integrable_ionization_pair_density {N q : ℕ} (ε : ℝ) (hε : 0 < ε)
    (i j : Fin N) (hij : i ≠ j) (u : FormDomain N q) :
    Integrable (fun X : Configuration N =>
      ((ionizationParticleWeight ε i X + ionizationParticleWeight ε j X) /
        ‖particlePosition X i - particlePosition X j‖) * ‖(u : State N q) X‖ ^ 2) := by
  have h := (integrable_ionization_ordered_pair_density ε hε i j hij u).add
    (integrable_ionization_ordered_pair_density ε hε j i hij.symm u)
  apply h.congr
  filter_upwards [] with X
  dsimp only [Pi.add_apply]
  rw [norm_sub_rev (particlePosition X j), ← add_mul, ← add_div]

/-- The selected kernel, expressed as a finite sum over all other original indices. -/
theorem ionization_selected_repulsion_toReal_ae {N : ℕ} (i : Fin (N + 1))
    (e : Fin N ≃ {j : Fin (N + 1) // j ≠ i}) :
    ∀ᵐ X : Configuration (N + 1), (selectedRepulsionKernel i e X).toReal =
      ∑ j ∈ Finset.univ.filter (fun j => j ≠ i),
        ‖particlePosition X i - particlePosition X j‖⁻¹ := by
  classical
  filter_upwards [Sobolev.ae_collision_free (fun _ : Fin 0 => (0 : Position))] with X hX
  rw [selectedRepulsionKernel_eq_sum_full, ENNReal.toReal_sum]
  · simp only [coulombKernel_toReal]
    have he := Equiv.sum_comp e (fun j : {j : Fin (N + 1) // j ≠ i} =>
      ‖particlePosition X i - particlePosition X j.val‖⁻¹)
    exact he.trans (Finset.sum_subtype (Finset.univ.filter (fun j => j ≠ i))
      (fun j => by simp) (fun j => ‖particlePosition X i - particlePosition X j‖⁻¹)).symm
  · intro j _
    rw [coulombKernel, ENNReal.inv_ne_top, ENNReal.ofReal_ne_zero_iff]
    exact norm_pos_iff.mpr (sub_ne_zero.mpr (hX.2 i (e j).val (e j).property.symm))

/-- The finite selected repulsion expectation is the sum of its ordered pair integrals. -/
theorem integral_ionization_selected_repulsion_eq_sum {N q : ℕ} (ε : ℝ) (hε : 0 < ε)
    (i : Fin (N + 1)) (e : Fin N ≃ {j : Fin (N + 1) // j ≠ i})
    (u : FormDomain (N + 1) q) :
    (∫ X : Configuration (N + 1), ionizationParticleWeight ε i X *
      (selectedRepulsionKernel i e X).toReal * ‖(u : State (N + 1) q) X‖ ^ 2) =
      ∑ j ∈ Finset.univ.filter (fun j => j ≠ i), ∫ X : Configuration (N + 1),
        (ionizationParticleWeight ε i X / ‖particlePosition X i - particlePosition X j‖) *
          ‖(u : State (N + 1) q) X‖ ^ 2 := by
  rw [← integral_finsetSum _ (fun j hj =>
    integrable_ionization_ordered_pair_density ε hε i j
      (Finset.mem_filter.mp hj).2.symm u)]
  apply integral_congr_ae
  filter_upwards [ionization_selected_repulsion_toReal_ae i e] with X hX
  rw [hX]
  simp only [div_eq_mul_inv, Finset.mul_sum, Finset.sum_mul]

/-- Regroup the finite ordered pair integrals into increasing unordered pairs. -/
theorem sum_ionization_ordered_pairs_eq_increasing {N q : ℕ} (ε : ℝ) (hε : 0 < ε)
    (u : FormDomain N q) :
    (∑ i : Fin N, ∑ j ∈ Finset.univ.filter (fun j => j ≠ i),
      ∫ X : Configuration N,
        (ionizationParticleWeight ε i X / ‖particlePosition X i - particlePosition X j‖) *
          ‖(u : State N q) X‖ ^ 2) =
      ∑ i : Fin N, ∑ j ∈ Finset.univ.filter (fun j => i < j),
        ∫ X : Configuration N,
          ((ionizationParticleWeight ε i X + ionizationParticleWeight ε j X) /
            ‖particlePosition X i - particlePosition X j‖) * ‖(u : State N q) X‖ ^ 2 := by
  rw [sum_ordered_pairs_eq_sum_increasing]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j hj
  have hij := ne_of_lt (Finset.mem_filter.mp hj).2
  rw [← integral_add (integrable_ionization_ordered_pair_density ε hε i j hij u)
    (integrable_ionization_ordered_pair_density ε hε j i hij.symm u)]
  apply integral_congr_ae
  filter_upwards [] with X
  rw [norm_sub_rev (particlePosition X j), ← add_mul, ← add_div]

end LiebThirring
end
