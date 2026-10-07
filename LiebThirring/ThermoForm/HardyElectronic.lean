/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.ThermoStability.KineticFibres
public import LiebThirring.ThermoStability.CoulombFibres
public import LiebThirring.Assembly.RealFormPairs
import LiebThirring.Variational.FormPairBounds

/-! # Coulomb bounds on electronic fibres of a joint state -/

public section

open MeasureTheory WithLp
open scoped ENNReal NNReal FourierTransform

namespace LiebThirring

open Assembly

local instance : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by norm_num⟩

/-- The additive one-body Hardy estimate after inserting a selected electron. -/
theorem lintegral_nucleus_coulomb_le_mass_add_fourier {N q : ℕ}
    (i : Fin N) (c : Position) (u : State N q) :
    (∫⁻ X : Configuration N, coulombKernel (particlePosition X i) c *
      (‖u X‖₊ : ℝ≥0∞) ^ 2) ≤
      (‖u‖₊ : ℝ≥0∞) ^ 2 + 4 * particleFourierEnergy u i := by
  let v := realFormSwapCurrying (realFormParticleCurrying i u)
  let w : Position → ℝ≥0∞ := fun ξ =>
    ENNReal.ofReal ((2 * Real.pi) ^ 2) * (‖ξ‖₊ : ℝ≥0∞) ^ 2
  have hw : Measurable w :=
    measurable_const.mul (measurable_id.nnnorm.coe_nnreal_ennreal.pow_const 2)
  have henergy : (∫⁻ y : OtherConfiguration i, ∫⁻ ξ : Position, w ξ *
      (‖(Lp.fourierTransformₗᵢ Position (SpinAmplitudes N q) (v y)) ξ‖₊ : ℝ≥0∞) ^ 2) =
      particleFourierEnergy u i :=
    (realFormSwapCurrying_fourier_weighted_norm_sq
      (realFormParticleCurrying i u) w hw).trans
      (realFormParticleCurrying_fourier_energy i u)
  have hmass : (∫⁻ y : OtherConfiguration i, (‖v y‖₊ : ℝ≥0∞) ^ 2) =
      (‖u‖₊ : ℝ≥0∞) ^ 2 := by
    change (∫⁻ y : OtherConfiguration i, ‖v y‖ₑ ^ 2) = ‖u‖ₑ ^ 2
    rw [lintegral_l2_enorm_sq]
    simpa only [← ofReal_norm] using congrArg (fun r : ℝ => ENNReal.ofReal r ^ 2)
      ((LinearIsometryEquiv.norm_map realFormSwapCurrying
          (realFormParticleCurrying i u)).trans (realFormParticleCurrying_norm i u))
  have hmeas : Measurable (fun y : OtherConfiguration i => (‖v y‖₊ : ℝ≥0∞) ^ 2) := by
    simpa only [enorm_eq_nnnorm] using (Lp.stronglyMeasurable v).enorm.pow_const 2
  have hs : (∫⁻ X : Configuration N, coulombKernel (particlePosition X i) c *
      (‖u X‖₊ : ℝ≥0∞) ^ 2) =
      ∫⁻ y : OtherConfiguration i, ∫⁻ x : Position,
        coulombKernel x c * (‖v y x‖₊ : ℝ≥0∞) ^ 2 := by
    simpa only [pow_one] using
      (lintegral_particle_coulomb_pow_eq_slices i (fun _ => c) measurable_const 1 u)
  rw [hs]
  calc
    _ ≤ ∫⁻ y : OtherConfiguration i, (‖v y‖₊ : ℝ≥0∞) ^ 2 +
        4 * ∫⁻ ξ : Position, w ξ *
          (‖(Lp.fourierTransformₗᵢ Position (SpinAmplitudes N q) (v y)) ξ‖₊ : ℝ≥0∞) ^ 2 :=
      lintegral_mono (fun y => lintegral_coulomb_le_of_fourier c (v y))
    _ = _ := by
      rw [lintegral_add_left hmeas, lintegral_const_mul' 4 _ (by norm_num),
        hmass, henergy]

/-- Attraction at fixed nuclei is bounded by electronic mass and kinetic energy. -/
theorem lintegral_attraction_le_mass_add_kinetic {N q M : ℕ}
    (z : Fin M → ℝ≥0) (R : Fin M → Position) (u : State N q) :
    (∫⁻ X : Configuration N, attraction z R X * (‖u X‖₊ : ℝ≥0∞) ^ 2) ≤
      ∑ i : Fin N, ∑ k : Fin M, (z k : ℝ≥0∞) *
        ((‖u‖₊ : ℝ≥0∞) ^ 2 + 4 * particleFourierEnergy u i) := by
  rw [lintegral_attraction_eq_sum]
  exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun k _ => by
    gcongr
    exact lintegral_nucleus_coulomb_le_mass_add_fourier i (R k) u

/-- Electron repulsion is bounded by a finite sum of mass-plus-particle-energy terms. -/
theorem lintegral_electronRepulsion_le_mass_add_kinetic {N q : ℕ} (u : State N q) :
    (∫⁻ X : Configuration N, electronRepulsion X * (‖u X‖₊ : ℝ≥0∞) ^ 2) ≤
      ∑ i : Fin N, ∑ _j ∈ Finset.univ.filter (fun j => i < j),
        ((‖u‖₊ : ℝ≥0∞) ^ 2 + 4 * particleFourierEnergy u i) := by
  classical
  unfold electronRepulsion
  simp_rw [Finset.sum_mul]
  rw [lintegral_finsetSum]
  · exact Finset.sum_le_sum fun i _ => by
      rw [lintegral_finsetSum]
      · exact Finset.sum_le_sum fun j hj =>
          lintegral_pair_coulomb_le_of_one_body_bound
            (fun c v => lintegral_coulomb_le_of_fourier c v)
            i j (ne_of_lt (Finset.mem_filter.mp hj).2) u
      · intro j _
        exact (measurable_coulombKernel.comp
          ((measurable_particlePosition i).prodMk (measurable_particlePosition j))).mul
          (measurable_state_norm_sq u)
  · intro i _
    exact Finset.measurable_sum _ fun j _ =>
      (measurable_coulombKernel.comp
        ((measurable_particlePosition i).prodMk (measurable_particlePosition j))).mul
        (measurable_state_norm_sq u)

/-- Coarse attraction control by total electronic kinetic energy. -/
theorem lintegral_attraction_le_mass_add_totalKinetic {N q M : ℕ}
    (z : Fin M → ℝ≥0) (R : Fin M → Position) (u : State N q) :
    (∫⁻ X : Configuration N, attraction z R X * (‖u X‖₊ : ℝ≥0∞) ^ 2) ≤
      ∑ _i : Fin N, ∑ k : Fin M, (z k : ℝ≥0∞) *
        ((‖u‖₊ : ℝ≥0∞) ^ 2 + 4 * kineticEnergy u) := by
  apply (lintegral_attraction_le_mass_add_kinetic z R u).trans
  exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun k _ => by
    gcongr
    exact Assembly.realForm_particleFourierEnergy_le i u

/-- Coarse electron-repulsion control by total electronic kinetic energy. -/
theorem lintegral_electronRepulsion_le_mass_add_totalKinetic {N q : ℕ} (u : State N q) :
    (∫⁻ X : Configuration N, electronRepulsion X * (‖u X‖₊ : ℝ≥0∞) ^ 2) ≤
      ∑ i : Fin N, ∑ _j ∈ Finset.univ.filter (fun j => i < j),
        ((‖u‖₊ : ℝ≥0∞) ^ 2 + 4 * kineticEnergy u) := by
  apply (lintegral_electronRepulsion_le_mass_add_kinetic u).trans
  exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun _j _ => by
    gcongr
    exact Assembly.realForm_particleFourierEnergy_le i u

end LiebThirring

end
