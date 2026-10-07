/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFLattice.Indices
import Mathlib.Tactic

/-!
# Finite occupations of the lowest cube modes

The occupation condition compares every occupied mode with every omitted
admissible mode. Equality is allowed, so this includes every partial filling
of a degenerate last shell. Source: Lieb–Simon (1977) III.13, pp. 67–69 (sharp eigenvalue sums).
-/

@[expose] public section

namespace LiebThirring.TFLattice

/-- Occupation of the lowest modes of an admissible lattice. -/
def IsFilled {q : ℕ} (admissible : ModeIndex q → Prop) (s : Finset (ModeIndex q)) : Prop :=
  (∀ p ∈ s, admissible p) ∧
    ∀ p ∈ s, ∀ r, admissible r → r ∉ s → squaredRadius p.1 ≤ squaredRadius r.1

theorem isFilled_empty {q : ℕ} (admissible : ModeIndex q → Prop) :
    IsFilled admissible ∅ := by
  simp [IsFilled]

/-- Finite occupations exist whenever the admissible lattice has an omitted
mode outside every finite set. The proof chooses a least integer energy at
each step, retaining freedom within equal-energy shells. -/
theorem exists_isFilled_of_exists_omitted {q : ℕ}
    (admissible : ModeIndex q → Prop)
    (homit : ∀ s : Finset (ModeIndex q), ∃ p, admissible p ∧ p ∉ s) (n : ℕ) :
    ∃ s : Finset (ModeIndex q), s.card = n ∧ IsFilled admissible s := by
  classical
  induction n with
  | zero => exact ⟨∅, rfl, isFilled_empty admissible⟩
  | succ n ih =>
    obtain ⟨s, hcard, hs⟩ := ih
    have hex : ∃ w : ℕ, ∃ p : ModeIndex q,
        admissible p ∧ p ∉ s ∧ squaredRadius p.1 = w := by
      obtain ⟨p, hp, hps⟩ := homit s
      exact ⟨squaredRadius p.1, p, hp, hps, rfl⟩
    obtain ⟨p, hp, hps, hweight⟩ := Nat.find_spec hex
    refine ⟨insert p s, by simp [hps, hcard], ?_⟩
    constructor
    · intro r hr
      rcases Finset.mem_insert.mp hr with rfl | hr
      · exact hp
      · exact hs.1 r hr
    · intro r hr t ht hts
      have hts' : t ∉ s := fun h => hts (Finset.mem_insert_of_mem h)
      rcases Finset.mem_insert.mp hr with rfl | hr
      · rw [hweight]
        exact Nat.find_min' hex ⟨t, ht, hts', rfl⟩
      · exact hs.2 r hr t ht hts'

theorem exists_omitted_modeBox {q : ℕ} (hq : 0 < q) (a : ℕ)
    (s : Finset (ModeIndex q)) : ∃ p ∈ modeBox q a (s.card + 1), p ∉ s := by
  classical
  have hpow : s.card + 1 ≤ (s.card + 1) ^ 3 :=
    le_self_pow (by omega) (by decide)
  have hmul : (s.card + 1) ^ 3 ≤ q * (s.card + 1) ^ 3 := by
    have hq' : 1 ≤ q := hq
    simpa only [one_mul] using Nat.mul_le_mul_right ((s.card + 1) ^ 3) hq'
  have hnot : ¬modeBox q a (s.card + 1) ⊆ s := by
    intro h
    have hc := Finset.card_le_card h
    rw [card_modeBox] at hc
    omega
  exact Finset.not_subset.mp hnot

theorem exists_isFilled_neumann {q : ℕ} (hq : 0 < q) (n : ℕ) :
    ∃ s : Finset (ModeIndex q), s.card = n ∧ IsFilled (fun _ => True) s := by
  apply exists_isFilled_of_exists_omitted
  intro s
  obtain ⟨p, _, hps⟩ := exists_omitted_modeBox hq 0 s
  exact ⟨p, trivial, hps⟩

theorem exists_isFilled_dirichlet {q : ℕ} (hq : 0 < q) (n : ℕ) :
    ∃ s : Finset (ModeIndex q), s.card = n ∧ IsFilled IsDirichletIndex s := by
  apply exists_isFilled_of_exists_omitted
  intro s
  obtain ⟨p, hp, hps⟩ := exists_omitted_modeBox hq 1 s
  exact ⟨p, isDirichletIndex_of_mem_modeBox (by decide) hp, hps⟩

/-- A comparison box containing more modes than the occupation provides an
omitted competitor. This uses strict cardinal inequality and therefore also
works for a partially filled energy shell. -/
theorem squaredRadius_le_of_isFilled {q a m : ℕ}
    {admissible : ModeIndex q → Prop} {s : Finset (ModeIndex q)}
    (hs : IsFilled admissible s)
    (hbox : ∀ r ∈ modeBox q a m, admissible r)
    (hcard : s.card < q * m ^ 3) {p : ModeIndex q} (hp : p ∈ s) :
    squaredRadius p.1 ≤ 3 * (a + m) ^ 2 := by
  classical
  have hnot : ¬modeBox q a m ⊆ s := by
    intro h
    have hc := Finset.card_le_card h
    rw [card_modeBox] at hc
    omega
  obtain ⟨r, hr, hrs⟩ := Finset.not_subset.mp hnot
  exact (hs.2 p hp r (hbox r hr) hrs).trans (squaredRadius_le_of_mem_modeBox hr)

theorem coordinate_sq_le_squaredRadius (k : Fin 3 → ℕ) (i : Fin 3) :
    k i ^ 2 ≤ squaredRadius k := by
  exact Finset.single_le_sum (fun j _ => Nat.zero_le (k j ^ 2)) (Finset.mem_univ i)

/-- A coarse enclosing box, sufficient for the density collision estimate.
This is not the sharp Weyl estimate of sharp eigenvalue sums. -/
theorem subset_modeBox_of_isFilled {q a m : ℕ}
    {admissible : ModeIndex q → Prop} {s : Finset (ModeIndex q)}
    (hs : IsFilled admissible s)
    (hbox : ∀ r ∈ modeBox q a m, admissible r)
    (hcard : s.card < q * m ^ 3) : s ⊆ modeBox q 0 (2 * (a + m) + 1) := by
  intro p hp
  apply mem_modeBox.mpr
  intro i
  have hsq := (coordinate_sq_le_squaredRadius p.1 i).trans
    (squaredRadius_le_of_isFilled hs hbox hcard hp)
  constructor
  · exact Nat.zero_le _
  · have hi : p.1 i ≤ 2 * (a + m) := by nlinarith
    omega

theorem sum_cubeEigenvalue {q : ℕ} (ℓ : {ℓ : ℝ // 0 < ℓ})
    (s : Finset (ModeIndex q)) :
    (∑ p ∈ s, cubeEigenvalue ℓ p) =
      (Real.pi ^ 2 / ℓ.val ^ 2) * (∑ p ∈ s, (squaredRadius p.1 : ℝ)) := by
  rw [Finset.mul_sum]
  simp only [cubeEigenvalue]
  apply Finset.sum_congr rfl
  intro p _
  ring

end LiebThirring.TFLattice

end
