/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module
public import LiebThirring.Electrostatics.NewtonConsequences
import LiebThirring.Electrostatics.Gaussian
import all LiebThirring.Electrostatics.Basic
/-! # Mixtures of spherical shells

Radialization independently replaces each point by uniform sphere probability
at the same distance from the center. Its Coulomb potential is the Newton
mixture formula, including a possible atom at radius zero.

Mixture-of-spheres step. -/

public section
open MeasureTheory Set Metric
open scoped ENNReal
namespace LiebThirring

theorem measurable_shell_radius (c : Position) : Measurable (shell c) := by
  apply Measure.measurable_of_measurable_coe
  intro s hs
  simp only [shell, Measure.map_apply (measurable_shellMap c _) hs]
  exact measurable_measure_prodMk_left
    (hs.preimage (measurable_const.add (measurable_fst.smul measurable_snd.subtype_val)))

@[expose] noncomputable def radialize (c : Position) (μ : Measure Position) : Measure Position :=
  μ.bind (fun x => shell c ‖x - c‖)

theorem measurable_radialization_kernel (c : Position) :
    Measurable (fun x : Position => shell c ‖x-c‖) :=
  (measurable_shell_radius c).comp (measurable_id.sub measurable_const).norm

theorem radialize_mass (c : Position) (μ : Measure Position) :
    radialize c μ univ = μ univ := by
  rw [radialize, Measure.bind_apply MeasurableSet.univ
    (measurable_radialization_kernel c).aemeasurable]
  simp only [measure_univ, lintegral_one]

theorem shell_zero (c : Position) : shell c 0 = Measure.dirac c := by
  simp only [shell, zero_smul, add_zero]
  rw [Measure.map_const, measure_univ, one_smul]

theorem coulombPotential_shell_nonneg (c : Position) {r : ℝ} (hr : 0 ≤ r)
    (y : Position) :
    coulombPotential (shell c r) y = (ENNReal.ofReal (max ‖y-c‖ r))⁻¹ := by
  rcases hr.eq_or_lt with h | h
  · subst r
    rw [shell_zero]
    rw [coulombPotential, lintegral_dirac' c measurable_coulombKernel.of_uncurry_left]
    rw [max_eq_left (norm_nonneg _)]
    rfl
  · exact coulombPotential_shell c h y

theorem coulombPotential_radialize (c y : Position) (μ : Measure Position) :
    coulombPotential (radialize c μ) y =
      ∫⁻ x, (ENNReal.ofReal (max ‖y-c‖ ‖x-c‖))⁻¹ ∂μ := by
  rw [coulombPotential, radialize, Measure.lintegral_bind
    (measurable_radialization_kernel c).aemeasurable
    measurable_coulombKernel.of_uncurry_left.aemeasurable]
  apply lintegral_congr
  intro x
  exact coulombPotential_shell_nonneg c (norm_nonneg _) y

/-- Invariance under orientation-preserving Euclidean rotations about `c`. -/
@[expose] def IsRadial (c : Position) (μ : Measure Position) : Prop :=
  ∀ Q : Position ≃ₗᵢ[ℝ] Position, Q.toLinearEquiv.det = 1 →
    μ.map (fun x => c + Q (x-c)) = μ

theorem radialize_eq_map_prod (c : Position) (μ : Measure Position) [SFinite μ] :
    radialize c μ = (μ.prod unitSphereMeasure).map
      (fun p => c + ‖p.1-c‖ • (p.2 : Position)) := by
  have hm : Measurable (fun p : Position × sphere (0 : Position) 1 =>
      c + ‖p.1-c‖ • (p.2 : Position)) :=
    measurable_const.add ((measurable_fst.sub measurable_const).norm.smul
      measurable_snd.subtype_val)
  apply Measure.ext
  intro s hs
  rw [radialize, Measure.bind_apply hs (measurable_radialization_kernel c).aemeasurable,
    Measure.map_apply hm hs, Measure.prod_apply (hs.preimage hm)]
  apply lintegral_congr
  intro x
  rw [shell, Measure.map_apply (measurable_shellMap c _) hs]
  rfl

instance instIsFiniteMeasureRadialize (c : Position) (μ : Measure Position)
    [IsFiniteMeasure μ] : IsFiniteMeasure (radialize c μ) :=
  ⟨by rw [radialize_mass]; exact measure_lt_top μ univ⟩

end LiebThirring
end
