/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Variational.TrialSlater
public import LiebThirring.Variational.TrialBasic

/-! # Existence of compact smooth antisymmetric trials -/

public section

open MeasureTheory WithLp
open scoped ENNReal NNReal ContDiff SchwartzMap

namespace LiebThirring

/-- A compact smooth Slater function is nonzero: its orbital evaluation matrix is the identity. -/
theorem trialSlater_ne_zero {N q : ℕ} (a : Fin N → Position)
    (b : Fin N → Position → ℝ) (t : Fin q)
    (hb : ∀ i j, b j (a i) = if i = j then 1 else 0) : trialSlater b t ≠ 0 := by
  classical
  let x : Configuration N := toLp 2 (fun ia => a ia.1 ia.2)
  have hx (i : Fin N) : particlePosition x i = a i := by
    ext j
    rfl
  have hmatrix : (fun i j : Fin N => b j (particlePosition x i)) =
      (1 : Matrix (Fin N) (Fin N) ℝ) := by
    funext i j
    rw [hx, hb]
    exact Matrix.one_apply.symm
  have hvalue : trialSlater b t x (fun _ => t) = 1 := by
    change (trialSlaterSpatial b x : ℂ) * trialSpinVector N q t (fun _ => t) = 1
    have hd : trialSlaterSpatial b x = 1 := by
      unfold trialSlaterSpatial
      rw [hmatrix, Matrix.det_one]
    rw [hd]
    simp only [trialSpinVector, PiLp.toLp_apply, ite_true, Complex.ofReal_one, mul_one]
  intro h
  have hz := congrArg (fun f : Configuration N → SpinAmplitudes N q =>
    f x (fun _ => t)) h
  rw [hvalue] at hz
  exact one_ne_zero hz

/-- Nonzero compact smooth fermionic functions exist for every particle number and nonempty
spin space. For zero particles the empty determinant is the vacuum scalar one. -/
theorem exists_compact_schwartz_antisymmetric (q : ℕ) (hq : 1 ≤ q) (N : ℕ) :
    ∃ f : 𝓢(Configuration N, SpinAmplitudes N q), f ≠ 0 ∧
      HasCompactSupport (fun x => f x) ∧
      ∀ (σ : Equiv.Perm (Fin N)) (x : Configuration N) (s : SpinLabels N q),
        f (permutePositions σ x) (permuteSpins σ s) =
          (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : ℂ) * f x s := by
  obtain ⟨a, b, hc, hs, _, hv⟩ := exists_disjoint_trial_orbitals N
  let t : Fin q := ⟨0, lt_of_lt_of_le Nat.zero_lt_one hq⟩
  let f : 𝓢(Configuration N, SpinAmplitudes N q) :=
    (hasCompactSupport_trialSlater b hc t).toSchwartzMap (contDiff_trialSlater b hs t)
  refine ⟨f, ?_, hasCompactSupport_trialSlater b hc t, trialSlater_permute b t⟩
  intro hf
  apply trialSlater_ne_zero a b t hv
  exact congrArg (fun g : 𝓢(Configuration N, SpinAmplitudes N q) => (fun x => g x)) hf

/-- The normalized form domain is nonempty, via compact smooth Slater states. -/
theorem exists_normalized_formDomain_trial (q : ℕ) (hq : 1 ≤ q) (N : ℕ) :
    ∃ ψ : FormDomain N q, ‖(ψ : State N q)‖ = 1 := by
  obtain ⟨f, hf, _, hanti⟩ := exists_compact_schwartz_antisymmetric q hq N
  exact exists_normalized_formDomain_of_schwartz f hf hanti

end LiebThirring

end
