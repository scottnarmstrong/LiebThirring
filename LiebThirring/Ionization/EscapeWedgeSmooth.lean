/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Ionization.EscapeWedge
public import LiebThirring.Variational.TrialSlater

/-! # Compact smooth amplitudes for the one-orbital wedge -/

public section

open WithLp Set Function
open scoped ContDiff SchwartzMap

namespace LiebThirring

/-- Bundle one omitted-particle summand over all spin configurations. -/
@[expose] noncomputable def escapeWedgeTermAmplitudes {N q : ℕ}
    (f : Configuration N → SpinAmplitudes N q)
    (h : Position → EuclideanSpace ℂ (Fin q)) (i : Fin (N + 1))
    (x : Configuration (N + 1)) : SpinAmplitudes (N + 1) q :=
  toLp 2 (fun s => escapeWedgeTerm (fun y t => f y t) (fun y t => h y t) i x s)

/-- Bundle the normalized wedge over all spin configurations. -/
@[expose] noncomputable def escapeWedgeAmplitudes {N q : ℕ}
    (f : Configuration N → SpinAmplitudes N q)
    (h : Position → EuclideanSpace ℂ (Fin q))
    (x : Configuration (N + 1)) : SpinAmplitudes (N + 1) q :=
  toLp 2 (fun s => escapeWedge (fun y t => f y t) (fun y t => h y t) x s)

theorem contDiff_escapeOmitPositions {N : ℕ} (i : Fin (N + 1)) :
    ContDiff ℝ ∞ (escapeOmitPositions i) := by
  apply (contDiff_piLp 2).mpr
  intro ja
  exact (contDiff_apply ℝ ℝ (Equiv.swap 0 i ja.1.succ, ja.2)).comp
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin (N + 1) × Fin 3 => ℝ)).contDiff

theorem contDiff_escapeWedgeTermAmplitudes {N q : ℕ}
    (f : Configuration N → SpinAmplitudes N q)
    (h : Position → EuclideanSpace ℂ (Fin q))
    (hf : ContDiff ℝ ∞ f) (hh : ContDiff ℝ ∞ h) (i : Fin (N + 1)) :
    ContDiff ℝ ∞ (escapeWedgeTermAmplitudes f h i) := by
  apply (contDiff_piLp 2).mpr
  intro s
  exact (contDiff_const.mul (((contDiff_piLp 2).mp hf (escapeOmitSpins i s)).comp
    (contDiff_escapeOmitPositions i))).mul
      (((contDiff_piLp 2).mp hh (s i)).comp (contDiff_particlePosition i))

theorem contDiff_escapeWedgeAmplitudes {N q : ℕ}
    (f : Configuration N → SpinAmplitudes N q)
    (h : Position → EuclideanSpace ℂ (Fin q))
    (hf : ContDiff ℝ ∞ f) (hh : ContDiff ℝ ∞ h) :
    ContDiff ℝ ∞ (escapeWedgeAmplitudes f h) := by
  apply (contDiff_piLp 2).mpr
  intro s
  apply contDiff_const.mul
  apply ContDiff.sum
  intro i _
  exact (contDiff_piLp 2).mp (contDiff_escapeWedgeTermAmplitudes f h hf hh i) s

/-- A nonzero summand lies in both original topological supports. -/
theorem escapeWedgeTerm_mem_tsupport {N q : ℕ}
    (f : Configuration N → SpinAmplitudes N q)
    (h : Position → EuclideanSpace ℂ (Fin q)) (i : Fin (N + 1))
    (x : Configuration (N + 1)) (s : SpinLabels (N + 1) q)
    (hx : escapeWedgeTerm (fun y t => f y t) (fun y t => h y t) i x s ≠ 0) :
    escapeOmitPositions i x ∈ tsupport f ∧ particlePosition x i ∈ tsupport h := by
  have hfs : f (escapeOmitPositions i x) (escapeOmitSpins i s) ≠ 0 := by
    intro he
    apply hx
    simp only [escapeWedgeTerm, he, mul_zero, zero_mul]
  have hhs : h (particlePosition x i) (s i) ≠ 0 := by
    intro he
    apply hx
    simp only [escapeWedgeTerm, he, mul_zero]
  constructor
  · apply subset_closure
    intro he
    apply hfs
    rw [he]
    rfl
  · apply subset_closure
    intro he
    apply hhs
    rw [he]
    rfl

theorem escape_omitted_index {N : ℕ} (i j : Fin (N + 1)) (hji : j ≠ i) :
    ∃ k : Fin N, Equiv.swap 0 i k.succ = j := by
  have hu : Equiv.swap 0 i j ≠ 0 := by
    intro he
    have he' := congrArg (Equiv.swap 0 i) he
    simp only [Equiv.swap_apply_self, Equiv.swap_apply_left] at he'
    exact hji he'
  rcases Fin.eq_zero_or_eq_succ (Equiv.swap 0 i j) with he | ⟨k, he⟩
  · exact (hu he).elim
  · refine ⟨k, ?_⟩
    rw [← he, Equiv.swap_apply_self]

/-- Compact support in both original factors gives compact support of a summand. -/
theorem hasCompactSupport_escapeWedgeTermAmplitudes {N q : ℕ}
    (f : Configuration N → SpinAmplitudes N q)
    (h : Position → EuclideanSpace ℂ (Fin q))
    (hf : HasCompactSupport f) (hh : HasCompactSupport h) (i : Fin (N + 1)) :
    HasCompactSupport (escapeWedgeTermAmplitudes f h i) := by
  classical
  let K : Set Position := tsupport h ∪
    ⋃ j : Fin N, (fun y : Configuration N => particlePosition y j) '' tsupport f
  have hK : IsCompact K := hh.union (isCompact_iUnion fun j =>
    hf.image (contDiff_particlePosition j).continuous)
  have hprod : IsCompact (Set.pi Set.univ (fun _ : Fin (N + 1) => K)) :=
    isCompact_univ_pi (fun _ => hK)
  apply HasCompactSupport.of_support_subset_isCompact
    ((trialConfigurationHomeomorph (N + 1)).isCompact_preimage.mpr hprod)
  intro x hx
  have hs : ∃ s, escapeWedgeTerm (fun y t => f y t) (fun y t => h y t) i x s ≠ 0 := by
    by_contra he
    apply hx
    apply PiLp.ext
    intro s
    change escapeWedgeTerm (fun y t => f y t) (fun y t => h y t) i x s = 0
    by_contra ht
    exact he ⟨s, ht⟩
  obtain ⟨s, hs⟩ := hs
  have hmem := escapeWedgeTerm_mem_tsupport f h i x s hs
  change ∀ j ∈ (Set.univ : Set (Fin (N + 1))), particlePosition x j ∈ K
  intro j _
  by_cases hji : j = i
  · rw [hji]
    exact Or.inl hmem.2
  · obtain ⟨k, hk⟩ := escape_omitted_index i j hji
    have hp : particlePosition (escapeOmitPositions i x) k = particlePosition x j := by
      ext a
      change x (Equiv.swap 0 i k.succ, a) = x (j, a)
      rw [hk]
    exact Or.inr (mem_iUnion_of_mem k ⟨escapeOmitPositions i x, hmem.1, hp⟩)

theorem escapeWedgeAmplitudes_eq_sum {N q : ℕ}
    (f : Configuration N → SpinAmplitudes N q)
    (h : Position → EuclideanSpace ℂ (Fin q)) :
    escapeWedgeAmplitudes f h = fun x =>
      (((Real.sqrt (N + 1))⁻¹ : ℝ) : ℂ) • ∑ i, escapeWedgeTermAmplitudes f h i x := by
  funext x
  apply PiLp.ext
  intro s
  simp only [escapeWedgeAmplitudes, escapeWedge, escapeWedgeTermAmplitudes,
    PiLp.toLp_apply, PiLp.smul_apply, smul_eq_mul, WithLp.ofLp_sum,
    Finset.sum_apply]

theorem hasCompactSupport_escapeWedgeAmplitudes {N q : ℕ}
    (f : Configuration N → SpinAmplitudes N q)
    (h : Position → EuclideanSpace ℂ (Fin q))
    (hf : HasCompactSupport f) (hh : HasCompactSupport h) :
    HasCompactSupport (escapeWedgeAmplitudes f h) := by
  rw [escapeWedgeAmplitudes_eq_sum]
  have hs : HasCompactSupport (fun x => ∑ i, escapeWedgeTermAmplitudes f h i x) := by
    have hs := HasCompactSupport.finset_sum (s := Finset.univ) (fun i _ =>
      hasCompactSupport_escapeWedgeTermAmplitudes f h hf hh i)
    have heq : (∑ i, escapeWedgeTermAmplitudes f h i) =
        fun x => ∑ i, escapeWedgeTermAmplitudes f h i x :=
      funext fun x => Finset.sum_apply x Finset.univ (escapeWedgeTermAmplitudes f h)
    rw [heq] at hs
    exact hs
  exact HasCompactSupport.smul_left (f := fun _ : Configuration (N + 1) =>
    (((Real.sqrt (N + 1))⁻¹ : ℝ) : ℂ)) hs

/-- The normalized compactly supported smooth wedge as a Schwartz function. -/
@[expose] noncomputable def escapeWedgeSchwartz {N q : ℕ}
    (f : 𝓢(Configuration N, SpinAmplitudes N q))
    (h : 𝓢(Position, EuclideanSpace ℂ (Fin q)))
    (hf : HasCompactSupport (fun x => f x)) (hh : HasCompactSupport (fun x => h x)) :
    𝓢(Configuration (N + 1), SpinAmplitudes (N + 1) q) :=
  (hasCompactSupport_escapeWedgeAmplitudes (fun x => f x) (fun x => h x) hf hh).toSchwartzMap
    (contDiff_escapeWedgeAmplitudes (fun x => f x) (fun x => h x) (f.smooth ⊤) (h.smooth ⊤))

@[simp] theorem escapeWedgeSchwartz_apply {N q : ℕ}
    (f : 𝓢(Configuration N, SpinAmplitudes N q))
    (h : 𝓢(Position, EuclideanSpace ℂ (Fin q)))
    (hf : HasCompactSupport (fun x => f x)) (hh : HasCompactSupport (fun x => h x))
    (x : Configuration (N + 1)) (s : SpinLabels (N + 1) q) :
    escapeWedgeSchwartz f h hf hh x s =
      escapeWedge (fun y t => f y t) (fun y t => h y t) x s := by
  rfl

end LiebThirring

end
