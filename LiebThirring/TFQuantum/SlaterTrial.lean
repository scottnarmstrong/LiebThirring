/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFQuantum.SlaterKinetic
public import LiebThirring.TFQuantum.SlaterMarginalsTwoBody
public import LiebThirring.TFQuantum.SlaterPairs
public import LiebThirring.TFQuantum.ElectronicInfimum

/-! # Actual Slater pair marginals, Coulomb energies and electronic trials

The exact ordered-pair marginal descends to the L² state, and every
nonnegative two-position observable tests it. Its Coulomb test gives precisely
direct minus nonnegative exchange, including the conventional factor one half.
Finite occupied-orbital kinetic energies give genuine normalized form-domain
trials and the real variational upper bound. All orbitals retain their full
complex spatial-spin dependence. Proof: Slater determinant identities; Lieb–Simon (1977) III.11 (60),
journal p. 66. Representative transport and trial packaging are direct proof.
-/

public section
open MeasureTheory
open scoped ENNReal NNReal
namespace LiebThirring

theorem slaterAmplitude_pair_testing {N q : ℕ} (u : Fin N → State 1 q)
    (i k : Fin N) (hik : i ≠ k) (w : Position × Position → ℝ≥0∞) (hw : Measurable w) :
    (∫⁻ p : Position × Position, w p * ∫⁻ Z : OtherPairConfiguration i k,
      (‖slaterAmplitude u (insertParticlePair i k p.1 p.2 Z)‖₊ : ℝ≥0∞)^2) =
      ∫⁻ X : Configuration N, w (particlePosition X i, particlePosition X k) *
        (‖slaterAmplitude u X‖₊ : ℝ≥0∞)^2 := by
  let e := pairInsertionMeasurableEquiv i k hik
  have hf : Measurable (fun X : Configuration N =>
      w (particlePosition X i, particlePosition X k) *
        (‖slaterAmplitude u X‖₊ : ℝ≥0∞)^2) :=
    (hw.comp ((measurable_particlePosition i).prodMk (measurable_particlePosition k))).mul
      ((measurable_slaterAmplitude u).nnnorm.coe_nnreal_ennreal.pow_const 2)
  have hm : Measurable (fun z : Position × (Position × OtherPairConfiguration i k) =>
      w (z.1, z.2.1) * (‖slaterAmplitude u (insertParticlePair i k z.1 z.2.1 z.2.2)‖₊ : ℝ≥0∞)^2) := by
    simpa only [Function.comp_def, e, pairInsertionMeasurableEquiv_apply,
      particlePosition_insertParticlePair_left, particlePosition_insertParticlePair_right i k hik]
      using hf.comp e.measurable
  have hnorm : Measurable (fun z : Position × (Position × OtherPairConfiguration i k) =>
      (‖slaterAmplitude u (insertParticlePair i k z.1 z.2.1 z.2.2)‖₊ : ℝ≥0∞)^2) := by
    simpa only [Function.comp_def, e, pairInsertionMeasurableEquiv_apply] using
      ((measurable_slaterAmplitude u).nnnorm.coe_nnreal_ennreal.pow_const 2).comp e.measurable
  have hpair : Measurable (fun p : Position × Position => w p * ∫⁻ Z : OtherPairConfiguration i k,
      (‖slaterAmplitude u (insertParticlePair i k p.1 p.2 Z)‖₊ : ℝ≥0∞)^2) := by
    exact hw.mul ((hnorm.comp ((measurable_fst.comp measurable_fst).prodMk
      ((measurable_snd.comp measurable_fst).prodMk measurable_snd))).lintegral_prod_right')
  rw [Measure.volume_eq_prod, lintegral_prod _ hpair.aemeasurable]
  have hinner (x : Position) :
      (∫⁻ y : Position, w (x,y) * ∫⁻ Z : OtherPairConfiguration i k,
        (‖slaterAmplitude u (insertParticlePair i k x y Z)‖₊ : ℝ≥0∞)^2) =
      ∫⁻ z : Position × OtherPairConfiguration i k,
        w (x,z.1) * (‖slaterAmplitude u (insertParticlePair i k x z.1 z.2)‖₊ : ℝ≥0∞)^2 := by
    rw [Measure.volume_eq_prod]
    have hprod := lintegral_prod (μ := (volume : Measure Position))
      (ν := (volume : Measure (OtherPairConfiguration i k))) _
      (hm.comp (measurable_prodMk_left (x := x))).aemeasurable
    simp only [Function.comp_def] at hprod
    rw [hprod]
    apply lintegral_congr
    intro y
    have hy : Measurable (fun Z : OtherPairConfiguration i k =>
        (‖slaterAmplitude u (insertParticlePair i k x y Z)‖₊ : ℝ≥0∞)^2) := by
      simpa only [Function.comp_def] using hnorm.comp
        (show Measurable (fun Z : OtherPairConfiguration i k => (x, (y, Z))) from
          measurable_const.prodMk (measurable_const.prodMk measurable_id))
    exact (lintegral_const_mul (w (x,y)) hy).symm
  simp_rw [hinner]
  rw [← lintegral_prod _ hm.aemeasurable]
  rw [← Measure.volume_eq_prod]
  have ht := (measurePreserving_pairInsertion i k hik).lintegral_comp hf
  simpa only [Function.comp_def, pairInsertionMeasurableEquiv_apply,
    particlePosition_insertParticlePair_left, particlePosition_insertParticlePair_right i k hik] using ht

theorem measurable_slaterAmplitude_pair_marginal {N q : ℕ} (u : Fin N → State 1 q)
    (i k : Fin N) (hik : i ≠ k) : Measurable (fun p : Position × Position =>
      ∫⁻ Z : OtherPairConfiguration i k,
        (‖slaterAmplitude u (insertParticlePair i k p.1 p.2 Z)‖₊ : ℝ≥0∞)^2) := by
  have he : Measurable (fun z : (Position × Position) × OtherPairConfiguration i k =>
      insertParticlePair i k z.1.1 z.1.2 z.2) := by
    simpa only [Function.comp_def, pairInsertionMeasurableEquiv_apply] using
      (pairInsertionMeasurableEquiv i k hik).measurable.comp
        ((measurable_fst.comp measurable_fst).prodMk
          ((measurable_snd.comp measurable_fst).prodMk measurable_snd))
  exact (((measurable_slaterAmplitude u).comp he).nnnorm.coe_nnreal_ennreal.pow_const 2).lintegral_prod_right'

/-- Every nonnegative two-position observable tests the actual ordered Slater pair density. -/
theorem slaterState_pair_testing {N q : ℕ} (u : Fin N → State 1 q)
    (hu : Orthonormal ℂ u) (w : Position × Position → ℝ≥0∞) (hw : Measurable w) :
    (∫⁻ p : Position × Position, w p * ENNReal.ofReal
      (slaterOrbitalDensity u p.1 * slaterOrbitalDensity u p.2 - slaterExchangeDensity u p.1 p.2)) =
      ∑ i : Fin N, ∑ k : Fin N, if i = k then 0 else
        ∫⁻ X : Configuration N, w (particlePosition X i, particlePosition X k) *
          (‖slaterState u X‖₊ : ℝ≥0∞)^2 := by
  classical
  have hm (i k : Fin N) : Measurable (fun p : Position × Position =>
      w p * (if hik : i = k then (0 : ℝ≥0∞) else ∫⁻ Z : OtherPairConfiguration i k,
        (‖slaterAmplitude u (insertParticlePair i k p.1 p.2 Z)‖₊ : ℝ≥0∞)^2)) := by
    by_cases hik : i = k
    · simp only [dite_eq_left hik, mul_zero]; exact measurable_const
    · simp only [dite_eq_right hik]
      exact hw.mul (measurable_slaterAmplitude_pair_marginal u i k hik)
  simp_rw [← sum_lintegral_slaterAmplitude_pair_norm_sq u hu, Finset.mul_sum]
  rw [lintegral_finsetSum Finset.univ (fun i _ =>
    Finset.measurable_sum _ (fun k _ => hm i k))]
  apply Finset.sum_congr rfl
  intro i _
  rw [lintegral_finsetSum Finset.univ (fun k _ => hm i k)]
  apply Finset.sum_congr rfl
  intro k _
  by_cases hik : i = k
  · simp [hik]
  · simp only [dite_eq_right hik, ite_eq_right hik]
    rw [slaterAmplitude_pair_testing u i k hik w hw]
    apply lintegral_congr_ae
    filter_upwards [coeFn_slaterState u] with X hX
    rw [hX]

/-- The electron repulsion is the direct-minus-exchange pair integral. -/
theorem electronRepulsion_slaterState {N q : ℕ} (u : Fin N → State 1 q)
    (hu : Orthonormal ℂ u) :
    (∫⁻ X : Configuration N, electronRepulsion X * (‖slaterState u X‖₊ : ℝ≥0∞)^2) =
      slaterPairCoulomb u := by
  classical
  have hm (i k : Fin N) : Measurable (fun X : Configuration N =>
      (if i = k then (0 : ℝ≥0∞) else coulombKernel (particlePosition X i) (particlePosition X k)) *
        (‖slaterState u X‖₊ : ℝ≥0∞)^2) := by
    by_cases hik : i = k
    · simp only [ite_eq_left hik, zero_mul]; exact measurable_const
    · simp only [ite_eq_right hik]
      exact (measurable_coulombKernel.comp
        ((measurable_particlePosition i).prodMk (measurable_particlePosition k))).mul
          (measurable_state_norm_sq (slaterState u))
  simp_rw [electronRepulsion_eq_half_ordered_sum, mul_assoc, Finset.sum_mul]
  rw [lintegral_const_mul _ (Finset.measurable_sum _ (fun i _ =>
    Finset.measurable_sum _ (fun k _ => hm i k))),
    lintegral_finsetSum Finset.univ (fun i _ =>
      Finset.measurable_sum _ (fun k _ => hm i k))]
  simp_rw [lintegral_finsetSum Finset.univ (fun k _ => hm _ k)]
  unfold slaterPairCoulomb
  rw [slaterState_pair_testing u hu
    (fun p : Position × Position => coulombKernel p.1 p.2) measurable_coulombKernel]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro k _
  by_cases hik : i = k
  · simp [hik]
  · simp [hik]

/-- A finite orthonormal family of one-particle form states gives an actual
many-particle form-domain member. -/
@[expose] noncomputable def slaterFormDomain {N q : ℕ} (u : Fin N → State 1 q)
    (hu : Orthonormal ℂ u) (hT : ∀ j, kineticEnergy (u j) < ⊤) : FormDomain N q :=
  ⟨slaterState u, antisymmetric_slaterState u,
    kineticEnergy_slaterState_lt_top u hu hT⟩

/-- The normalized electronic trial associated with the occupied orbitals. -/
@[expose] noncomputable def slaterElectronicTrial {N q : ℕ} (u : Fin N → State 1 q)
    (hu : Orthonormal ℂ u) (hT : ∀ j, kineticEnergy (u j) < ⊤) : ElectronicTrial N q :=
  ⟨slaterFormDomain u hu hT, by
    change ‖slaterState u‖ = 1
    exact norm_slaterState_of_orthonormal u hu⟩

end LiebThirring
end
