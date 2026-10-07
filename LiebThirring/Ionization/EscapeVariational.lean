/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Ionization.EscapeWedge
public import LiebThirring.Ionization.AtomicGroundStateEnergy
public import LiebThirring.Variational.TrialVariational
public import LiebThirring.Variational.FormContinuity

/-!
# Compact near-minimizers from the normalized form core

This module isolates the compact spatial core input from the compact smooth form core/normalized trial construction.
Its conditional near-minimizer lemma is consumed with the proved normalized
compact-core theorem in `EscapeCore`. The approximation uses the actual
Fourier graph norm.
-/

public section

open MeasureTheory
open scoped ENNReal NNReal SchwartzMap

namespace LiebThirring

/-- Regard a pointwise antisymmetric Schwartz amplitude as a form-domain state. -/
@[expose] noncomputable def escapeSchwartzForm {N q : ℕ}
    (f : 𝓢(Configuration N, SpinAmplitudes N q))
    (hf : ∀ (σ : Equiv.Perm (Fin N)) (x : Configuration N) (s : SpinLabels N q),
      f (permutePositions σ x) (permuteSpins σ s) =
        escapePermutationSign σ * f x s) : FormDomain N q :=
  ⟨f.toLp 2 (volume : Measure (Configuration N)),
    antisymmetric_toLp_of_pointwise f hf, kineticEnergy_schwartz_lt_top f⟩

/-- Conditional normalized compact trials consequence of normalized compact spatial core density.
`EscapeCore` proves and discharges this hypothesis. -/
theorem escape_exists_compact_near_minimizer_of_normalized_core_dense
    (q : ℕ) (hq : 1 ≤ q) (N : ℕ) (Z : ℝ≥0)
    (hdense : ∀ u : FormDomain N q, ‖(u : State N q)‖ = 1 →
      ∀ δ : ℝ, 0 < δ →
        ∃ (f : 𝓢(Configuration N, SpinAmplitudes N q))
          (hf : ∀ (σ : Equiv.Perm (Fin N)) (x : Configuration N) (s : SpinLabels N q),
            f (permutePositions σ x) (permuteSpins σ s) =
              escapePermutationSign σ * f x s),
          HasCompactSupport (fun x => f x) ∧
          ‖f.toLp 2 (volume : Measure (Configuration N))‖ = 1 ∧
          formGraphNorm (escapeSchwartzForm f hf - u) < δ)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (f : 𝓢(Configuration N, SpinAmplitudes N q))
      (hf : ∀ (σ : Equiv.Perm (Fin N)) (x : Configuration N) (s : SpinLabels N q),
        f (permutePositions σ x) (permuteSpins σ s) = escapePermutationSign σ * f x s),
      HasCompactSupport (fun x => f x) ∧
      ‖f.toLp 2 (volume : Measure (Configuration N))‖ = 1 ∧
      realEnergy (fun _ : Fin 1 => Z) (fun _ => 0)
        (fun _ _ _ => Subsingleton.elim _ _) (escapeSchwartzForm f hf) <
          (atomicGroundStateEnergy N q Z).toReal + ε := by
  let z : Fin 1 → ℝ≥0 := fun _ => Z
  let R : Fin 1 → Position := fun _ => 0
  have hR : Function.Injective R := fun _ _ _ => Subsingleton.elim _ _
  obtain ⟨u, hu, he⟩ := exists_normalized_realEnergy_lt q hq N 1 z R hR
    (ε / 2) (half_pos hε)
  obtain ⟨δ, hδ, hc⟩ := realEnergy_continuous_formGraphNorm z R hR u (half_pos hε)
  obtain ⟨f, hf, hcompact, hnorm, hgraph⟩ := hdense u hu δ hδ
  refine ⟨f, hf, hcompact, hnorm, ?_⟩
  have he' := (abs_lt.mp (hc (escapeSchwartzForm f hf) hgraph)).2
  change realEnergy z R hR (escapeSchwartzForm f hf) <
    (groundStateEnergy N q 1 z R hR).toReal + ε
  linarith only [he, he']

end LiebThirring

end
