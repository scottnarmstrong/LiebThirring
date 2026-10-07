/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Variational.CompactForm
public import LiebThirring.Ionization.ExistenceScalar

/-! # Lower semicontinuity of the Coulomb energy along compact sequences -/

public section

open MeasureTheory Filter WithLp
open scoped ENNReal NNReal Topology

namespace LiebThirring
open Assembly

/-- The nonnegative electron-repulsion expectation is lower semicontinuous along an
almost-everywhere convergent, uniformly form-bounded sequence. -/
theorem repulsion_expectation_le_liminf_of_tendsto_ae {N q : ℕ}
    {u : ℕ → FormDomain N q} {v : FormDomain N q}
    (hu : ∀ᵐ x ∂(volume : Measure (Configuration N)),
      Tendsto (fun n => (u n : State N q) x) atTop (𝓝 ((v : State N q) x)))
    (K : ℝ) (hK : ∀ n, formGraphNorm (u n) ≤ K) :
    (∫⁻ x : Configuration N,
      electronRepulsion x * (‖(v : State N q) x‖₊ : ℝ≥0∞) ^ 2).toReal ≤
      liminf (fun n => (∫⁻ x : Configuration N,
        electronRepulsion x * (‖(u n : State N q) x‖₊ : ℝ≥0∞) ^ 2).toReal) atTop := by
  let I : ℕ → ℝ≥0∞ := fun n => ∫⁻ x : Configuration N,
    electronRepulsion x * (‖(u n : State N q) x‖₊ : ℝ≥0∞) ^ 2
  let Iv : ℝ≥0∞ := ∫⁻ x : Configuration N,
    electronRepulsion x * (‖(v : State N q) x‖₊ : ℝ≥0∞) ^ 2
  have hpoint : ∀ᵐ x ∂(volume : Measure (Configuration N)),
      electronRepulsion x * (‖(v : State N q) x‖₊ : ℝ≥0∞) ^ 2 ≤
        liminf (fun n => electronRepulsion x *
          (‖(u n : State N q) x‖₊ : ℝ≥0∞) ^ 2) atTop := by
    filter_upwards [hu] with x hx
    by_cases hv : (‖(v : State N q) x‖₊ : ℝ≥0∞) ^ 2 = 0
    · rw [hv, mul_zero]
      exact bot_le
    · exact (ENNReal.Tendsto.const_mul
        ((ENNReal.continuous_pow 2).tendsto _ |>.comp
          ((continuous_enorm.tendsto _).comp hx)) (Or.inl hv)).liminf_eq.ge
  have hfat : Iv ≤ liminf I atTop := by
    calc
      Iv ≤ ∫⁻ x : Configuration N,
          liminf (fun n => electronRepulsion x *
            (‖(u n : State N q) x‖₊ : ℝ≥0∞) ^ 2) atTop :=
        lintegral_mono_ae hpoint
      _ ≤ liminf I atTop := lintegral_liminf_le' fun n =>
        measurable_electronRepulsion.aemeasurable.mul
          ((Lp.aestronglyMeasurable (u n : State N q)).nnnorm.aemeasurable.coe_nnreal_ennreal.pow_const 2)
  let C : ℝ := (1 + (N.choose 2 : ℝ) ^ 2) * K ^ 2
  have hC : 0 ≤ C := mul_nonneg (by positivity) (sq_nonneg K)
  have hIb : ∀ n, I n ≤ ENNReal.ofReal C := by
    intro n
    apply (ENNReal.toReal_le_toReal
      (lintegral_electronRepulsion_lt_top (u n : State N q) (u n).property.2).ne
      (ENNReal.ofReal_ne_top)).mp
    rw [ENNReal.toReal_ofReal hC]
    exact (repulsion_le_formGraphNorm_sq (u n)).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (formGraphNorm_nonneg _) (hK n) 2)
        (by positivity))
  have hIvtop : Iv ≠ ⊤ :=
    (lintegral_electronRepulsion_lt_top (v : State N q) v.property.2).ne
  have hlimbound : liminf I atTop ≤ ENNReal.ofReal C := by
    calc
      liminf I atTop ≤ liminf (fun _ : ℕ => ENNReal.ofReal C) atTop :=
        liminf_le_liminf (Eventually.of_forall hIb)
      _ = ENNReal.ofReal C := by simp
  calc
    Iv.toReal ≤ (liminf I atTop).toReal :=
      (ENNReal.toReal_le_toReal hIvtop
        (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hlimbound)).mpr hfat
    _ = liminf (fun n => (I n).toReal) atTop :=
      (ENNReal.liminf_toReal_eq ENNReal.ofReal_ne_top (Eventually.of_forall hIb)).symm

/-- Kinetic energy plus electron repulsion is lower semicontinuous along a bounded weak-graph
sequence that converges almost everywhere in its state coordinate. -/
theorem kinetic_add_repulsion_le_liminf {N q : ℕ}
    {u : ℕ → FormDomain N q} {v : FormDomain N q}
    (hweak : ∀ w : Sobolev.formGraph N q,
      Tendsto (fun n => inner ℂ (formDomainGraph (u n)) w) atTop
        (𝓝 (inner ℂ (formDomainGraph v) w)))
    (hae : ∀ᵐ x ∂(volume : Measure (Configuration N)),
      Tendsto (fun n => (u n : State N q) x) atTop (𝓝 ((v : State N q) x)))
    (K : ℝ) (hK : ∀ n, formGraphNorm (u n) ≤ K) :
    (kineticEnergy (v : State N q)).toReal +
      (∫⁻ x : Configuration N,
        electronRepulsion x * (‖(v : State N q) x‖₊ : ℝ≥0∞) ^ 2).toReal ≤
      liminf (fun n => (kineticEnergy (u n : State N q)).toReal +
        (∫⁻ x : Configuration N,
          electronRepulsion x * (‖(u n : State N q) x‖₊ : ℝ≥0∞) ^ 2).toReal) atTop := by
  let T : ℕ → ℝ := fun n => (kineticEnergy (u n : State N q)).toReal
  let B : ℕ → ℝ := fun n => (∫⁻ x : Configuration N,
    electronRepulsion x * (‖(u n : State N q) x‖₊ : ℝ≥0∞) ^ 2).toReal
  have hT := kineticEnergy_le_liminf_of_formGraph_weak hweak K (fun n => by
    simpa only [norm_formDomainGraph] using hK n)
  have hT' : (kineticEnergy (v : State N q)).toReal ≤ liminf T atTop := by
    simpa only [T, formDomainGraph_state] using hT
  have hB := repulsion_expectation_le_liminf_of_tendsto_ae hae K hK
  apply (add_le_add hT' hB).trans
  apply liminf_add_le_liminf_of_nonneg_bounded T B (K ^ 2)
    ((1 + (N.choose 2 : ℝ) ^ 2) * K ^ 2)
  · exact fun _ => ENNReal.toReal_nonneg
  · intro n
    calc
      T n ≤ formGraphNorm (u n) ^ 2 := by
        rw [formGraphNorm_sq]
        exact le_add_of_nonneg_left (sq_nonneg _)
      _ ≤ K ^ 2 := pow_le_pow_left₀ (formGraphNorm_nonneg _) (hK n) 2
  · exact fun _ => ENNReal.toReal_nonneg
  · intro n
    exact (repulsion_le_formGraphNorm_sq (u n)).trans
      (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (formGraphNorm_nonneg _) (hK n) 2) (by positivity))

end LiebThirring

end
