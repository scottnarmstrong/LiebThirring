/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.ThermoForm.HardyElectronic

/-! # Componentwise Coulomb control for the nuclear block -/

public section

open MeasureTheory WithLp
open scoped ENNReal NNReal FourierTransform

namespace LiebThirring

local instance : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by norm_num⟩

/-- The one-dimensional spin-amplitude space is canonically the scalar field. -/
@[expose] noncomputable def scalarSpinOneEquiv (M : ℕ) :
    ℂ ≃ₗᵢ[ℂ] SpinAmplitudes M 1 where
  toFun z := toLp 2 (fun _ => z)
  invFun v := v default
  left_inv _ := rfl
  right_inv v := by
    apply PiLp.ext
    intro s
    change v default = v s
    rw [Subsingleton.elim s default]
  map_add' _ _ := by ext s; rfl
  map_smul' _ _ := by ext s; rfl
  norm_map' z := by
    change ‖toLp 2 (Function.const (SpinLabels M 1) z)‖ = ‖z‖
    rw [PiLp.norm_toLp_const (by norm_num : (2 : ℝ≥0∞) ≠ ∞)]
    norm_num

/-- A scalar spatial L² class regarded as a one-spin state. -/
@[expose] noncomputable def scalarStateOne (M : ℕ)
    (f : Lp ℂ 2 (volume : Measure (Configuration M))) : State M 1 :=
  l2TargetEquiv volume (scalarSpinOneEquiv M) f

theorem scalarStateOne_ae (M : ℕ) (f : Lp ℂ 2 (volume : Measure (Configuration M))) :
    scalarStateOne M f =ᵐ[volume] fun R => scalarSpinOneEquiv M (f R) :=
  l2TargetEquiv_ae volume (scalarSpinOneEquiv M) f

theorem scalarStateOne_norm (M : ℕ) (f : Lp ℂ 2 (volume : Measure (Configuration M))) :
    ‖scalarStateOne M f‖ = ‖f‖ :=
  (l2TargetEquiv volume (scalarSpinOneEquiv M)).norm_map f

theorem scalarStateOne_nnnorm (M : ℕ) (f : Lp ℂ 2 (volume : Measure (Configuration M))) :
    ‖scalarStateOne M f‖₊ = ‖f‖₊ := by
  exact NNReal.eq (scalarStateOne_norm M f)

theorem scalarStateOne_fourier (M : ℕ)
    (f : Lp ℂ 2 (volume : Measure (Configuration M))) :
    𝓕 (scalarStateOne M f) = scalarStateOne M (𝓕 f) := by
  exact Fourier.fourier_compLp
    (scalarSpinOneEquiv M).toContinuousLinearEquiv.toContinuousLinearMap f

theorem scalarStateOne_lintegral (M : ℕ)
    (f : Lp ℂ 2 (volume : Measure (Configuration M))) (w : Configuration M → ℝ≥0∞) :
    (∫⁻ R, w R * (‖scalarStateOne M f R‖₊ : ℝ≥0∞) ^ 2) =
      ∫⁻ R, w R * (‖f R‖₊ : ℝ≥0∞) ^ 2 := by
  apply lintegral_congr_ae
  filter_upwards [scalarStateOne_ae M f] with R hR
  rw [hR, (scalarSpinOneEquiv M).nnnorm_map]

theorem scalarStateOne_kineticEnergy (M : ℕ)
    (f : Lp ℂ 2 (volume : Measure (Configuration M))) :
    kineticEnergy (scalarStateOne M f) =
      ∫⁻ η : Configuration M, ENNReal.ofReal ((2 * Real.pi) ^ 2) *
        (‖η‖₊ : ℝ≥0∞) ^ 2 * (‖(𝓕 f) η‖₊ : ℝ≥0∞) ^ 2 := by
  unfold kineticEnergy
  change (∫⁻ η : Configuration M, ENNReal.ofReal ((2 * Real.pi) ^ 2) *
    (‖η‖₊ : ℝ≥0∞) ^ 2 * (‖(𝓕 (scalarStateOne M f)) η‖₊ : ℝ≥0∞) ^ 2) = _
  rw [scalarStateOne_fourier]
  exact scalarStateOne_lintegral M (𝓕 f)
    (fun η => ENNReal.ofReal ((2 * Real.pi) ^ 2) * (‖η‖₊ : ℝ≥0∞) ^ 2)

/-- Extract one coordinate from a finite Hilbert-valued spatial class. -/
@[expose] noncomputable def finiteTargetComponent {ι : Type*} [Fintype ι]
    {M : ℕ} (u : Lp (EuclideanSpace ℂ ι) 2 (volume : Measure (Configuration M))) (σ : ι) :
    Lp ℂ 2 (volume : Measure (Configuration M)) :=
  (PiLp.proj (𝕜 := ℂ) (p := 2) (fun _ : ι => ℂ) σ).compLp u

theorem finiteTargetComponent_ae {ι : Type*} [Fintype ι] {M : ℕ}
    (u : Lp (EuclideanSpace ℂ ι) 2 (volume : Measure (Configuration M))) (σ : ι) :
    finiteTargetComponent u σ =ᵐ[volume] fun R => u R σ :=
  (PiLp.proj (𝕜 := ℂ) (p := 2) (fun _ : ι => ℂ) σ).coeFn_compLp u

theorem finiteTargetComponent_fourier {ι : Type*} [Fintype ι] {M : ℕ}
    (u : Lp (EuclideanSpace ℂ ι) 2 (volume : Measure (Configuration M))) (σ : ι) :
    𝓕 (finiteTargetComponent u σ) = finiteTargetComponent (𝓕 u) σ :=
  Fourier.fourier_compLp (PiLp.proj (𝕜 := ℂ) (p := 2) (fun _ : ι => ℂ) σ) u

theorem finiteTarget_enorm_sq_eq_sum {ι : Type*} [Fintype ι]
    (v : EuclideanSpace ℂ ι) :
    ‖v‖ₑ ^ 2 = ∑ σ : ι, ‖v σ‖ₑ ^ 2 := by
  simp only [enorm_eq_nnnorm, ← ENNReal.coe_pow, ← ENNReal.ofNNReal_finsetSum]
  congr 1
  rw [PiLp.nnnorm_eq_of_L2, NNReal.sq_sqrt]

theorem finiteTarget_lintegral_eq_sum {ι : Type*} [Fintype ι] {M : ℕ}
    (u : Lp (EuclideanSpace ℂ ι) 2 (volume : Measure (Configuration M)))
    (w : Configuration M → ℝ≥0∞) (hw : Measurable w) :
    (∫⁻ R, w R * ‖u R‖ₑ ^ 2) =
      ∑ σ : ι, ∫⁻ R, w R * ‖finiteTargetComponent u σ R‖ₑ ^ 2 := by
  have hu : ∀ᵐ R : Configuration M ∂volume, ∀ σ : ι,
      finiteTargetComponent u σ R = u R σ := by
    rw [ae_all_iff]
    intro σ
    exact finiteTargetComponent_ae u σ
  calc
    _ = ∫⁻ R, ∑ σ : ι, w R * ‖finiteTargetComponent u σ R‖ₑ ^ 2 := by
      apply lintegral_congr_ae
      filter_upwards [hu] with R hR
      rw [finiteTarget_enorm_sq_eq_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun σ _ => congrArg (fun a => w R * a ^ 2) (congrArg enorm (hR σ)).symm
    _ = ∑ σ : ι, ∫⁻ R, w R * ‖finiteTargetComponent u σ R‖ₑ ^ 2 := by
      rw [lintegral_finsetSum]
      intro σ _
      exact hw.mul ((Lp.stronglyMeasurable
        (finiteTargetComponent u σ)).enorm.pow_const 2)

/-- Full Fourier kinetic energy for a finite-dimensional target. -/
@[expose] noncomputable def finiteTargetKineticEnergy {ι : Type*} [Fintype ι]
    {M : ℕ} (u : Lp (EuclideanSpace ℂ ι) 2 (volume : Measure (Configuration M))) : ℝ≥0∞ :=
  ∫⁻ η : Configuration M, ENNReal.ofReal ((2 * Real.pi) ^ 2) *
    (‖η‖₊ : ℝ≥0∞) ^ 2 * (‖(𝓕 u) η‖₊ : ℝ≥0∞) ^ 2

theorem finiteTargetKineticEnergy_eq_sum {ι : Type*} [Fintype ι] {M : ℕ}
    (u : Lp (EuclideanSpace ℂ ι) 2 (volume : Measure (Configuration M))) :
    finiteTargetKineticEnergy u = ∑ σ : ι,
      kineticEnergy (scalarStateOne M (finiteTargetComponent u σ)) := by
  unfold finiteTargetKineticEnergy
  change (∫⁻ η : Configuration M,
    (ENNReal.ofReal ((2 * Real.pi) ^ 2) * (‖η‖₊ : ℝ≥0∞) ^ 2) * ‖(𝓕 u) η‖ₑ ^ 2) = _
  rw [finiteTarget_lintegral_eq_sum]
  · apply Finset.sum_congr rfl
    intro σ _
    rw [scalarStateOne_kineticEnergy, finiteTargetComponent_fourier]
    rfl
  · exact measurable_const.mul (measurable_id.nnnorm.coe_nnreal_ennreal.pow_const 2)

theorem finiteTargetComponent_enorm_sq_le {ι : Type*} [Fintype ι] {M : ℕ}
    (u : Lp (EuclideanSpace ℂ ι) 2 (volume : Measure (Configuration M))) (σ : ι) :
    ‖finiteTargetComponent u σ‖ₑ ^ 2 ≤ ‖u‖ₑ ^ 2 := by
  have h := finiteTarget_lintegral_eq_sum u (fun _ => 1) measurable_const
  simp only [one_mul, lintegral_l2_enorm_sq] at h
  rw [h]
  exact Finset.single_le_sum (f := fun τ => ‖finiteTargetComponent u τ‖ₑ ^ 2)
    (fun _ _ => zero_le) (Finset.mem_univ σ)

theorem finiteTargetComponent_kineticEnergy_le {ι : Type*} [Fintype ι] {M : ℕ}
    (u : Lp (EuclideanSpace ℂ ι) 2 (volume : Measure (Configuration M))) (σ : ι) :
    kineticEnergy (scalarStateOne M (finiteTargetComponent u σ)) ≤
      finiteTargetKineticEnergy u := by
  rw [finiteTargetKineticEnergy_eq_sum]
  exact Finset.single_le_sum
    (f := fun τ => kineticEnergy (scalarStateOne M (finiteTargetComponent u τ)))
    (fun _ _ => zero_le) (Finset.mem_univ σ)

/-- Repulsion for a finite-dimensional target, reduced componentwise to scalar states. -/
theorem lintegral_electronRepulsion_finiteTarget_le {ι : Type*} [Fintype ι] {M : ℕ}
    (u : Lp (EuclideanSpace ℂ ι) 2 (volume : Measure (Configuration M))) :
    (∫⁻ R : Configuration M, electronRepulsion R * ‖u R‖ₑ ^ 2) ≤
      ∑ σ : ι, ∑ i : Fin M, ∑ _j ∈ Finset.univ.filter (fun j => i < j),
        ((‖finiteTargetComponent u σ‖₊ : ℝ≥0∞) ^ 2 +
          4 * kineticEnergy (scalarStateOne M (finiteTargetComponent u σ))) := by
  rw [finiteTarget_lintegral_eq_sum]
  · apply Finset.sum_le_sum
    intro σ _
    let f := finiteTargetComponent u σ
    have hp := lintegral_electronRepulsion_le_mass_add_kinetic (scalarStateOne M f)
    rw [scalarStateOne_lintegral M f electronRepulsion, scalarStateOne_nnnorm] at hp
    exact hp.trans (Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => by
      gcongr
      exact Assembly.realForm_particleFourierEnergy_le i (scalarStateOne M f))
  · exact Assembly.measurable_electronRepulsion

/-- A coarser finite-target bound with a common mass and kinetic term. -/
theorem lintegral_electronRepulsion_finiteTarget_le_common {ι : Type*} [Fintype ι]
    {M : ℕ} (u : Lp (EuclideanSpace ℂ ι) 2 (volume : Measure (Configuration M))) :
    (∫⁻ R : Configuration M, electronRepulsion R * ‖u R‖ₑ ^ 2) ≤
      ∑ _σ : ι, ∑ i : Fin M, ∑ _j ∈ Finset.univ.filter (fun j => i < j),
        (‖u‖ₑ ^ 2 + 4 * finiteTargetKineticEnergy u) := by
  apply (lintegral_electronRepulsion_finiteTarget_le u).trans
  exact Finset.sum_le_sum fun σ _ => Finset.sum_le_sum fun _i _ =>
    Finset.sum_le_sum fun _j _ => add_le_add
      (finiteTargetComponent_enorm_sq_le u σ) (by
        gcongr
        exact finiteTargetComponent_kineticEnergy_le u σ)

end LiebThirring

end
