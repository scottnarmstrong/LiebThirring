/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module
public import LiebThirring.TFQuantum.SlaterTensorProduct
public import LiebThirring.Variational.SpectatorCoulomb
public import LiebThirring.TFQuantum.SlaterMarginals
/-! # Ordered products of arbitrary L² spatial-spin orbitals

The literal product amplitude belongs to L² by finite product integration of
one-particle contractions. Its State class is a tensor append
at each successor step. Consequently its full Fourier transform is the
ordered product of the Fourier-transformed orbitals, including the empty
product sector. Proof: Slater determinant identities; direct proof product integration
and the proved arbitrary L² particle tensor Fourier identity.
-/

public section
open MeasureTheory WithLp
open scoped ComplexConjugate FourierTransform
namespace LiebThirring

@[expose] noncomputable def orbitalProductAmplitude {N q : ℕ}
    (u : Fin N → State 1 q) (X : Configuration N) : SpinAmplitudes N q :=
  toLp 2 (fun s => ∏ i : Fin N, orbitalValue (u i) (particlePosition X i) (s i))

theorem measurable_orbitalProductAmplitude {N q : ℕ} (u : Fin N → State 1 q) :
    Measurable (orbitalProductAmplitude u) := by
  apply (PiLp.continuous_toLp 2 (fun _ : SpinLabels N q => ℂ)).measurable.comp
  rw [measurable_pi_iff]
  intro s
  exact Finset.measurable_prod _ fun i _ =>
    (measurable_orbitalValue (u i) (s i)).comp (measurable_particlePosition i)

theorem orbitalProductAmplitude_norm_sq_complex {N q : ℕ}
    (u : Fin N → State 1 q) (X : Configuration N) :
    ((‖orbitalProductAmplitude u X‖^2 : ℝ) : ℂ) =
      ∏ i : Fin N, orbitalContraction (u i) (u i) (particlePosition X i) := by
  rw [PiLp.norm_sq_eq_of_L2, Complex.ofReal_sum,
    ← sum_prod_orbital_eq_prod_contraction u u X]
  apply Finset.sum_congr rfl
  intro s _
  simp only [orbitalProductAmplitude, PiLp.toLp_apply]
  rw [Complex.ofReal_pow, ← Complex.conj_mul', map_prod, Finset.prod_mul_distrib]

theorem memLp_orbitalProductAmplitude {N q : ℕ} (u : Fin N → State 1 q) :
    MemLp (orbitalProductAmplitude u) 2 volume := by
  have hc : Integrable (fun X : Configuration N =>
      ((‖orbitalProductAmplitude u X‖^2 : ℝ) : ℂ)) := by
    refine (integrable_prod_orbitalContraction u u).congr ?_
    filter_upwards [] with X
    exact (orbitalProductAmplitude_norm_sq_complex u X).symm
  have hr : Integrable (fun X : Configuration N => ‖orbitalProductAmplitude u X‖^2) := by
    refine hc.norm.congr ?_
    filter_upwards [] with X
    simp
  exact (memLp_two_iff_integrable_sq_norm
    (measurable_orbitalProductAmplitude u).aestronglyMeasurable).2 hr

@[expose] noncomputable def orbitalProductState {N q : ℕ} (u : Fin N → State 1 q) :
    State N q := (memLp_orbitalProductAmplitude u).toLp (orbitalProductAmplitude u)

theorem coeFn_orbitalProductState {N q : ℕ} (u : Fin N → State 1 q) :
    orbitalProductState u =ᵐ[volume] orbitalProductAmplitude u := MemLp.coeFn_toLp _

theorem orbitalProductState_succ {N q : ℕ} (u : Fin (N+1) → State 1 q) :
    orbitalProductState u =
      orbitalTensorAppend (u (Fin.last N)) (orbitalProductState (fun j => u j.castSucc)) := by
  let i := Fin.last N
  let e := finSuccAboveEquiv i
  have hm := (MeasurePreserving.symm (insertionMeasurableEquiv i)
    (measurePreserving_insertion i)).quasiMeasurePreserving
  rw [Measure.volume_eq_prod] at hm
  have he := (MeasurePreserving.symm (Sobolev.configurationReindexMeasurableEquiv e)
    (Sobolev.measurePreserving_configurationReindex e)).quasiMeasurePreserving
  have hp := he.comp (Measure.quasiMeasurePreserving_snd.comp hm)
  have htail := hp.ae (coeFn_orbitalProductState (fun j => u j.castSucc))
  apply Lp.ext
  filter_upwards [coeFn_orbitalProductState u,
    orbitalTensorAppend_apply_ae (u (Fin.last N))
      (orbitalProductState (fun j => u j.castSucc)), htail] with X hX ha ht
  simp only [Function.comp_apply] at ht
  change orbitalProductState (fun j => u j.castSucc) (Variational.residualProjection i e X) =
    orbitalProductAmplitude (fun j => u j.castSucc) (Variational.residualProjection i e X) at ht
  ext s
  rw [hX, ha s, ht]
  change (∏ j : Fin (N+1), orbitalValue (u j) (particlePosition X j) (s j)) =
    orbitalValue (u (Fin.last N)) (particlePosition X (Fin.last N)) (s (Fin.last N)) *
      (∏ j : Fin N, orbitalValue (u j.castSucc)
        (particlePosition (Variational.residualProjection i e X) j) (s j.castSucc))
  rw [Fin.prod_univ_castSucc]
  simp_rw [Variational.particlePosition_residualProjection]
  simp only [e, i, finSuccAboveEquiv_apply, Fin.succAbove_last]
  exact mul_comm _ _

theorem fourier_orbitalProductState {N q : ℕ} (u : Fin N → State 1 q) :
    𝓕 (orbitalProductState u) = orbitalProductState (fun j => 𝓕 (u j)) := by
  induction N with
  | zero =>
      rw [fourier_zeroParticleState]
      congr 1
      funext j
      exact Fin.elim0 j
  | succ N ih =>
      rw [orbitalProductState_succ, fourier_orbitalTensorAppend, ih,
        orbitalProductState_succ]

end LiebThirring
end
