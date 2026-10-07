/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFMinimizer.KineticDerivative
public import LiebThirring.TFMinimizer.MixtureConvexity

/-! # First variation of the literal Thomas--Fermi functional

Lieb–Simon (1977) II.10, pp. 40--43. The affine extension is used only
for differentiation; its values on the nonnegative mixture interval equal
the functional of actual TF densities.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology

namespace LiebThirring.TFMinimizer

open TFFunctional

/-- The real first variation, with the full electronic potential. -/
@[expose] noncomputable def tfFirstVariation {M : ℕ} (a : {a : ℝ // 0 < a})
    (z : Fin M → ℝ≥0) (R : Fin M → Position) (ρ : TFDensity) (x : Position) : ℝ :=
  (5 / 3 : ℝ) * a.val * (ρ.val x) ^ ((2 : ℝ) / 3) - tfNuclearPotential z R x +
    (coulombPotential (tfDensityMeasure ρ) x).toReal

theorem integrable_tfFirstVariation_pair {M : ℕ} (a : {a : ℝ // 0 < a})
    (z : Fin M → ℝ≥0) (R : Fin M → Position) (ρ σ : TFDensity) :
    Integrable (fun x : Position => tfFirstVariation a z R ρ x * σ.val x) volume := by
  have h := (((integrable_kinetic_pair ρ σ).const_mul ((5 / 3 : ℝ) * a.val)).sub
    (integrable_tfNuclearPotential_mul z R σ)).add (integrable_potential_pair ρ σ)
  apply h.congr
  filter_upwards [] with x
  dsimp [tfFirstVariation]
  ring

theorem integral_tfFirstVariation_pair {M : ℕ} (a : {a : ℝ // 0 < a})
    (z : Fin M → ℝ≥0) (R : Fin M → Position) (ρ σ : TFDensity) :
    (∫ x : Position, tfFirstVariation a z R ρ x * σ.val x) =
      (5 / 3 : ℝ) * a.val * (∫ x : Position, (ρ.val x) ^ ((2 : ℝ) / 3) * σ.val x) -
        (∫ x : Position, tfNuclearPotential z R x * σ.val x) + 2 * tfCoulombEnergy ρ σ := by
  have hk : Integrable (fun x : Position => (5 / 3 : ℝ) * a.val *
      ((ρ.val x) ^ ((2 : ℝ) / 3) * σ.val x)) volume :=
    (integrable_kinetic_pair ρ σ).const_mul _
  have hs : Integrable (fun x : Position => (5 / 3 : ℝ) * a.val *
      ((ρ.val x) ^ ((2 : ℝ) / 3) * σ.val x) -
      tfNuclearPotential z R x * σ.val x) volume := hk.sub
        (integrable_tfNuclearPotential_mul z R σ)
  calc
    _ = ∫ x : Position, (((5 / 3 : ℝ) * a.val *
        ((ρ.val x) ^ ((2 : ℝ) / 3) * σ.val x) - tfNuclearPotential z R x * σ.val x) +
        (coulombPotential (tfDensityMeasure ρ) x).toReal * σ.val x) := by
      apply integral_congr_ae
      filter_upwards [] with x
      dsimp [tfFirstVariation]
      ring
    _ = _ := by
      rw [integral_add hs (integrable_potential_pair ρ σ),
        integral_sub hk (integrable_tfNuclearPotential_mul z R σ),
        integral_const_mul, integral_potential_pair]

/-- An affine real extension, agreeing with actual mixtures for `0 ≤ t ≤ 1`. -/
@[expose] noncomputable def tfAffineFunctional {M : ℕ} (a : {a : ℝ // 0 < a})
    (z : Fin M → ℝ≥0) (R : Fin M → Position) (ρ σ : TFDensity) (t : ℝ) : ℝ :=
  a.val * (∫ x : Position, (ρ.val x + t * (σ.val x - ρ.val x)) ^ ((5 : ℝ) / 3)) -
    ((1 - t) * (∫ x : Position, tfNuclearPotential z R x * ρ.val x) +
      t * (∫ x : Position, tfNuclearPotential z R x * σ.val x)) +
    ((1 - t) ^ 2 * tfCoulombEnergy ρ ρ +
      2 * (1 - t) * t * tfCoulombEnergy ρ σ + t ^ 2 * tfCoulombEnergy σ σ)

theorem tfAffineFunctional_zero {M : ℕ} (a : {a : ℝ // 0 < a})
    (z : Fin M → ℝ≥0) (R : Fin M → Position) (ρ σ : TFDensity) :
    tfAffineFunctional a z R ρ σ 0 = tfFunctional a z R ρ := by
  simp [tfAffineFunctional, tfFunctional]

theorem tfAffineFunctional_eq_mixture {M : ℕ} (a : {a : ℝ // 0 < a})
    (z : Fin M → ℝ≥0) (R : Fin M → Position) (ρ σ : TFDensity)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    tfAffineFunctional a z R ρ σ t =
      tfFunctional a z R (tfMixture ⟨1 - t, sub_nonneg.mpr ht.2⟩ ⟨t, ht.1⟩ ρ σ) := by
  let b : ℝ≥0 := ⟨1 - t, sub_nonneg.mpr ht.2⟩
  let c : ℝ≥0 := ⟨t, ht.1⟩
  change tfAffineFunctional a z R ρ σ t = tfFunctional a z R (tfMixture b c ρ σ)
  rw [tfFunctional, integral_attraction_tfMixture z R b c ρ σ,
    tfCoulombEnergy_tfMixture b c ρ σ]
  have hk : (∫ x : Position, (ρ.val x + t * (σ.val x - ρ.val x)) ^ ((5 : ℝ) / 3)) =
      ∫ x : Position,
        ((tfMixture ⟨1 - t, sub_nonneg.mpr ht.2⟩ ⟨t, ht.1⟩ ρ σ).val x) ^ ((5 : ℝ) / 3) := by
    apply integral_congr_ae
    filter_upwards [tfMixture_apply_ae ⟨1 - t, sub_nonneg.mpr ht.2⟩ ⟨t, ht.1⟩ ρ σ] with x hx
    rw [hx]
    congr 1
    change ρ.val x + t * (σ.val x - ρ.val x) = (1 - t) * ρ.val x + t * σ.val x
    ring
  unfold tfAffineFunctional
  rw [hk]
  rfl

theorem hasDerivAt_tfAffineFunctional {M : ℕ} (a : {a : ℝ // 0 < a})
    (z : Fin M → ℝ≥0) (R : Fin M → Position) (ρ σ : TFDensity) :
    HasDerivAt (tfAffineFunctional a z R ρ σ)
      ((∫ x : Position, tfFirstVariation a z R ρ x * σ.val x) -
        ∫ x : Position, tfFirstVariation a z R ρ x * ρ.val x) 0 := by
  have hid := hasDerivAt_id (0 : ℝ)
  have hc := hasDerivAt_const (0 : ℝ) (1 : ℝ)
  have h := ((hasDerivAt_integral_kinetic_line ρ σ).const_mul a.val).sub
    (((hc.sub hid).mul_const (∫ x : Position, tfNuclearPotential z R x * ρ.val x)).add
      (hid.mul_const (∫ x : Position, tfNuclearPotential z R x * σ.val x)))
  have hD := ((((hc.sub hid).pow 2).mul_const (tfCoulombEnergy ρ ρ)).add
    ((((hc.sub hid).const_mul 2).mul hid).mul_const (tfCoulombEnergy ρ σ))).add
    ((hid.pow 2).mul_const (tfCoulombEnergy σ σ))
  convert h.add hD using 1
  · rfl
  · rw [integral_tfFirstVariation_pair, integral_tfFirstVariation_pair]
    have he : (∫ x : Position, (ρ.val x) ^ ((2 : ℝ) / 3) * (σ.val x - ρ.val x)) =
        (∫ x : Position, (ρ.val x) ^ ((2 : ℝ) / 3) * σ.val x) -
          ∫ x : Position, (ρ.val x) ^ ((2 : ℝ) / 3) * ρ.val x := by
      simp_rw [mul_sub]
      exact integral_sub (integrable_kinetic_pair ρ σ) (integrable_kinetic_pair ρ ρ)
    rw [he]
    norm_num
    ring

/-- A right local minimum forces a nonnegative derivative, including endpoint minima. -/
theorem nonneg_derivative_of_right_min {f : ℝ → ℝ} {d r : ℝ}
    (hd : HasDerivAt f d 0) (hr : 0 < r)
    (hmin : ∀ t ∈ Ioo (0 : ℝ) r, f 0 ≤ f t) : 0 ≤ d := by
  apply ge_of_tendsto hd.tendsto_slope_zero_right
  have he : ∀ᶠ t in 𝓝[>] (0 : ℝ), t ∈ Ioo (0 : ℝ) r := by
    have hp : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t :=
      eventually_mem_nhdsWithin
    exact hp.and ((eventually_lt_nhds hr).filter_mono nhdsWithin_le_nhds)
  filter_upwards [he] with t ht
  simpa only [zero_add, smul_eq_mul] using
    mul_nonneg (inv_nonneg.mpr ht.1.le) (sub_nonneg.mpr (hmin t ht))

end LiebThirring.TFMinimizer

end
