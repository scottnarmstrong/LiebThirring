/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Ionization.IMSRamp
public import LiebThirring.Variational.SlicesSubsetForm
public import LiebThirring.Variational.SpectatorVariational

/-! # Selected-particle slices of an IMS sector

An IMS sector is antisymmetric only under permutations which preserve its inside block.
This is exactly the symmetry needed to make almost every inside-particle slice an
antisymmetric form-domain state.
-/

public section

open MeasureTheory WithLp
open scoped ENNReal NNReal Classical

namespace LiebThirring

open Sobolev
open Variational

/-- A sector product vanishes if one of its outside coordinates lies in the closed
inside ball. -/
theorem imsSectorWeight_eq_zero_of_outside_norm_le {N : ℕ} {R : ℝ} (hR : 0 < R)
    (S : Finset (Fin N)) {x : Configuration N} {i : Fin N} (hi : i ∉ S)
    (hx : ‖particlePosition x i‖ ≤ R) :
    imsSectorWeight (imsChi R) (imsEta R) S x = 0 := by
  rw [imsSectorWeight]
  rw [Finset.prod_eq_zero (Finset.mem_sdiff.mpr ⟨Finset.mem_univ i, hi⟩)
    (imsEta_eq_zero_of_norm_le hR hx), mul_zero]

/-- At every point where an IMS sector product is nonzero, all complementary
particles have radius greater than the cutoff radius. -/
theorem norm_lt_particlePosition_of_imsSectorWeight_ne_zero {N : ℕ} {R : ℝ}
    (hR : 0 < R) (S : Finset (Fin N)) {x : Configuration N}
    (hx : imsSectorWeight (imsChi R) (imsEta R) S x ≠ 0)
    {i : Fin N} (hi : i ∉ S) : R < ‖particlePosition x i‖ := by
  exact lt_of_not_ge fun h => hx (imsSectorWeight_eq_zero_of_outside_norm_le hR S hi h)

/-- Stabilizer antisymmetry of a full state induces full antisymmetry on almost every
selected-block slice. -/
theorem subsetParticleSlice_antisymmetric_ae_of_stabilizer {N k q : ℕ}
    (S : Set (Fin N)) (e : Fin k ≃ S) (v : State N q)
    (hv : ∀ σ : Equiv.Perm (Fin N), (∀ i, i ∈ S ↔ σ i ∈ S) →
      ∀ᵐ x ∂(volume : Measure (Configuration N)), ∀ s : SpinLabels N q,
        v (permutePositions σ x) (permuteSpins σ s) =
          (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : ℂ) * v x s) :
    ∀ᵐ y : SubsetSpectatorConfiguration S, ∀ α : SubsetSpectatorSpins S q,
      antisymmetric (subsetParticleSlice S e v y α) := by
  have hslices := subsetParticleSlice_ae S e v
  have hfull (σ : Equiv.Perm (Fin k)) :
      ∀ᵐ z : SubsetSpectatorConfiguration S × Configuration k,
        ∀ t : SpinLabels N q,
          v (permutePositions (σ.extendDomain e) (subsetOrderedInsertion S e z))
              (permuteSpins (σ.extendDomain e) t) =
            (((Equiv.Perm.sign (σ.extendDomain e) : ℤˣ) : ℤ) : ℂ) *
              v (subsetOrderedInsertion S e z) t := by
    exact (measurePreserving_subsetOrderedInsertion S e).quasiMeasurePreserving.ae
      (hv (σ.extendDomain e) (fun i => by
      constructor
      · intro hi
        obtain ⟨j, hj⟩ := e.surjective ⟨i, hi⟩
        have heval : (e j).val = i := congrArg Subtype.val hj
        rw [← heval, Equiv.Perm.extendDomain_apply_image]
        exact (e (σ j)).property
      · intro hi
        by_contra hnot
        have hfix : σ.extendDomain e i = i := by
          apply Equiv.Perm.extendDomain_apply_not_subtype
          simpa using hnot
        exact hnot (hfix ▸ hi)))
  have hcurried (σ : Equiv.Perm (Fin k)) :
      ∀ᵐ y : SubsetSpectatorConfiguration S, ∀ᵐ x : Configuration k,
        ∀ t : SpinLabels N q,
          v (permutePositions (σ.extendDomain e) (subsetOrderedInsertion S e (y, x)))
              (permuteSpins (σ.extendDomain e) t) =
            (((Equiv.Perm.sign (σ.extendDomain e) : ℤˣ) : ℤ) : ℂ) *
              v (subsetOrderedInsertion S e (y, x)) t :=
    Measure.ae_ae_of_ae_prod (hfull σ)
  have hall : ∀ᵐ y : SubsetSpectatorConfiguration S, ∀ σ : Equiv.Perm (Fin k),
      ∀ᵐ x : Configuration k, ∀ t : SpinLabels N q,
        v (permutePositions (σ.extendDomain e) (subsetOrderedInsertion S e (y, x)))
            (permuteSpins (σ.extendDomain e) t) =
          (((Equiv.Perm.sign (σ.extendDomain e) : ℤˣ) : ℤ) : ℂ) *
            v (subsetOrderedInsertion S e (y, x)) t :=
    eventually_countable_forall.mpr hcurried
  filter_upwards [hslices, hall] with y hy hall_y
  intro α σ
  have hxperm := (measurePreserving_permutePositions σ).quasiMeasurePreserving.ae (hy α)
  filter_upwards [hy α, hxperm, hall_y σ] with x hx hpx hvx
  intro s
  rw [hpx (permuteSpins σ s), hx s]
  have h := hvx (subsetOrderedSpinEquiv S e (α, s))
  rw [permutePositions_subsetOrderedInsertion,
    permuteSpins_subsetOrderedSpinEquiv] at h
  rw [h, Equiv.Perm.sign_extendDomain σ e]

/-- A total form-domain representative for a slice of a blockwise antisymmetric state. -/
@[expose] noncomputable def stabilizerSubsetParticleFormSlice {N k q : ℕ}
    (S : Set (Fin N)) (e : Fin k ≃ S) (v : State N q)
    (y : SubsetSpectatorConfiguration S) (α : SubsetSpectatorSpins S q) :
    FormDomain k q :=
  if h : antisymmetric (subsetParticleSlice S e v y α) ∧
      kineticEnergy (subsetParticleSlice S e v y α) < ⊤ then
    ⟨subsetParticleSlice S e v y α, h⟩
  else 0

/-- The stabilizer form-slice represents almost every selected-block slice when the state
has finite kinetic energy and stabilizer antisymmetry. -/
theorem stabilizerSubsetParticleFormSlice_ae {N k q : ℕ}
    (S : Set (Fin N)) (e : Fin k ≃ S) (v : State N q) (hvkin : kineticEnergy v < ⊤)
    (hv : ∀ σ : Equiv.Perm (Fin N), (∀ i, i ∈ S ↔ σ i ∈ S) →
      ∀ᵐ x ∂(volume : Measure (Configuration N)), ∀ s : SpinLabels N q,
        v (permutePositions σ x) (permuteSpins σ s) =
          (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : ℂ) * v x s) :
    ∀ᵐ y : SubsetSpectatorConfiguration S, ∀ α : SubsetSpectatorSpins S q,
      ((stabilizerSubsetParticleFormSlice S e v y α : FormDomain k q) : State k q) =
        subsetParticleSlice S e v y α := by
  filter_upwards [subsetParticleSlice_antisymmetric_ae_of_stabilizer S e v hv,
    subsetParticleSlice_kineticEnergy_lt_top_ae S e v hvkin] with y hanti hkin
  intro α
  simp [stabilizerSubsetParticleFormSlice, hanti α, hkin α]

/-- The atomic variational lower bound for every total stabilizer slice. -/
theorem atomicGroundStateEnergy_mul_norm_sq_le_stabilizerSliceEnergy
    (q : ℕ) (hq : 1 ≤ q) {N k : ℕ} (Z : ℝ≥0)
    (S : Set (Fin N)) (e : Fin k ≃ S) (v : State N q)
    (y : SubsetSpectatorConfiguration S) (α : SubsetSpectatorSpins S q) :
    (atomicGroundStateEnergy k q Z).toReal *
        ‖((stabilizerSubsetParticleFormSlice S e v y α : FormDomain k q) : State k q)‖ ^ 2 ≤
      fullRealEnergy (fun _ : Fin 1 => Z) (fun _ => 0)
        ((stabilizerSubsetParticleFormSlice S e v y α : FormDomain k q) : State k q) := by
  rw [fullRealEnergy_eq_realEnergy _ _ Variational.atomicPositionInjective]
  exact Variational.atomicGroundStateEnergy_toReal_mul_norm_sq_le_realEnergy
    q hq k Z (stabilizerSubsetParticleFormSlice S e v y α)

end LiebThirring

end
