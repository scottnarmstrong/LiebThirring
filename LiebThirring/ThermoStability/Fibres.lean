/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Thermodynamic.QuantumAntisymmetric
public import LiebThirring.Kinetic.CurryingProductSurjective
public import LiebThirring.Kinetic.CurryingTransport
public import Mathlib.MeasureTheory.Measure.SeparableMeasure
import LiebThirring.Kinetic.Permutation
import LiebThirring.Variational.FormIntegral
import LiebThirring.Sobolev.Collisions

/-!
# Electron fibres of joint quantum states

The nuclear coordinates are the outer variable of L² currying. These identities implement
the mass, statistics and collision parts of the quantum stability.
-/

public section

open MeasureTheory WithLp
open scoped ENNReal NNReal

namespace LiebThirring.ThermoStability

local instance : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by norm_num⟩

/-- Insert a nuclear configuration and an electron configuration into the joint carrier. -/
@[expose] noncomputable def nuclearFirstEquiv (N M : ℕ) :
    (Configuration M × Configuration N) ≃ᵐ QuantumConfiguration N M :=
  MeasurableEquiv.prodComm.trans (MeasurableEquiv.toLp 2 _)

theorem measurePreserving_nuclearFirstEquiv (N M : ℕ) :
    MeasurePreserving (nuclearFirstEquiv N M) volume volume :=
  MeasureTheory.Measure.measurePreserving_swap.trans (WithLp.volume_preserving_toLp _ _)

/-- Joint states as an L² field of electronic states, without a choice of normalization. -/
@[expose] noncomputable def electronFibreField {N M q : ℕ} (ψ : QuantumState N M q) :
    Lp (State N q) 2 (volume : Measure (Configuration M)) :=
  l2Curry (Lp.compMeasurePreserving (nuclearFirstEquiv N M)
    (measurePreserving_nuclearFirstEquiv N M) ψ)

theorem electronFibreField_ae {N M q : ℕ} (ψ : QuantumState N M q) :
    ∀ᵐ R : Configuration M, ∀ᵐ x : Configuration N,
      electronFibreField ψ R x = ψ (toLp 2 (x, R)) := by
  have h := Measure.ae_ae_of_ae_prod (Lp.coeFn_compMeasurePreserving ψ
    (measurePreserving_nuclearFirstEquiv N M))
  filter_upwards [l2Curry_ae (Lp.compMeasurePreserving (nuclearFirstEquiv N M)
    (measurePreserving_nuclearFirstEquiv N M) ψ), h] with R hR hψ
  exact Filter.EventuallyEq.trans hR hψ

theorem electronFibreField_norm {N M q : ℕ} (ψ : QuantumState N M q) :
    ‖electronFibreField ψ‖ = ‖ψ‖ := by
  rw [electronFibreField, l2Curry_norm, Lp.norm_compMeasurePreserving]

/-- Currying the nuclear block is a surjective complex linear isometry. -/
@[expose] noncomputable def electronFibreEquiv (N M q : ℕ) :
    QuantumState N M q ≃ₗᵢ[ℂ] Lp (State N q) 2 (volume : Measure (Configuration M)) :=
  (l2PullbackEquiv (E := SpinAmplitudes N q) (nuclearFirstEquiv N M)
    (measurePreserving_nuclearFirstEquiv N M)).trans l2CurryLinearIsometryEquiv

/-- Tonelli disintegration with an arbitrary measurable nonnegative joint weight. -/
theorem lintegral_weight_electronFibreField {N M q : ℕ}
    (ψ : QuantumState N M q) (w : QuantumConfiguration N M → ℝ≥0∞)
    (hw : Measurable w) :
    (∫⁻ X : QuantumConfiguration N M, w X * (‖ψ X‖₊ : ℝ≥0∞) ^ 2) =
      ∫⁻ R : Configuration M, ∫⁻ x : Configuration N,
        w (toLp 2 (x, R)) * (‖electronFibreField ψ R x‖₊ : ℝ≥0∞) ^ 2 := by
  have hf : Measurable (fun X => w X * (‖ψ X‖₊ : ℝ≥0∞) ^ 2) :=
    hw.mul ((Lp.stronglyMeasurable ψ).measurable.nnnorm.coe_nnreal_ennreal.pow_const 2)
  rw [← (measurePreserving_nuclearFirstEquiv N M).lintegral_comp
    hf]
  change (∫⁻ a, w (nuclearFirstEquiv N M a) *
    (‖ψ (nuclearFirstEquiv N M a)‖₊ : ℝ≥0∞) ^ 2 ∂volume.prod volume) = _
  rw [lintegral_prod (fun a : Configuration M × Configuration N =>
    w (nuclearFirstEquiv N M a) * (‖ψ (nuclearFirstEquiv N M a)‖₊ : ℝ≥0∞) ^ 2)
    (hf.comp (nuclearFirstEquiv N M).measurable).aemeasurable]
  apply lintegral_congr_ae
  filter_upwards [electronFibreField_ae ψ] with R hR
  apply lintegral_congr_ae
  filter_upwards [hR] with x hx
  rw [hx]
  rfl

/-- Almost every nuclear configuration has pairwise distinct nuclear positions. -/
theorem ae_injective_nuclearPositions (M : ℕ) :
    ∀ᵐ R : Configuration M, Function.Injective (fun k => particlePosition R k) := by
  have h : ∀ᵐ R : Configuration M, ∀ k l,
      k ≠ l → particlePosition R k ≠ particlePosition R l := by
    simp only [ae_all_iff]
    exact fun k l hkl => Sobolev.ae_particlePosition_ne_particlePosition k l hkl
  filter_upwards [h] with R hR
  intro k l hkl
  by_contra hne
  exact hR k l hne hkl

theorem antisymmetric_electronFibreField_ae {N M q : ℕ}
    (ψ : QuantumState N M q) (hψ : quantum_antisymmetric ψ) :
    ∀ᵐ R : Configuration M, antisymmetric (electronFibreField ψ R) := by
  have hanti : ∀ᵐ R : Configuration M, ∀ σ : Equiv.Perm (Fin N),
      ∀ᵐ x : Configuration N, ∀ s : SpinLabels N q,
        ψ (toLp 2 (permutePositions σ x, R)) (permuteSpins σ s) =
          (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : ℂ) * ψ (toLp 2 (x, R)) s := by
    rw [ae_all_iff]
    intro σ
    exact Measure.ae_ae_of_ae_prod
      ((measurePreserving_nuclearFirstEquiv N M).quasiMeasurePreserving.ae (hψ σ))
  filter_upwards [electronFibreField_ae ψ, hanti] with R hR hA
  intro σ
  filter_upwards [hR, (measurePreserving_permutePositions σ).quasiMeasurePreserving.ae hR, hA σ]
    with x hx hσx ha
  intro s
  rw [hx, hσx]
  exact ha s

end LiebThirring.ThermoStability

end
