/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Packing.LatticeCounting

/-!
# Selecting an exact number of lattice balls

An internal finite-selection lemma. Its volume budget must be established by
geometric estimates before it can be used; it does not assert Swiss-cheese
capacity.
-/

public section

open Set MeasureTheory Metric

namespace LiebThirring

/-- A proved volume budget produces the requested finite family of disjoint balls. -/
theorem exists_lattice_balls_of_volume_budget {ℓ : ℝ} {Ω : Set Position}
    (hℓ : 0 < ℓ) (hΩ : Bornology.IsBounded Ω) (n : ℕ)
    (hbudget : (n : ℝ) * ℓ ^ 3 ≤
      volume.real Ω - volume.real (latticeBoundaryLayer ℓ Ω)) :
    ∃ c : Fin n → Position,
      (∀ i, closedBall (c i) (ℓ / 2) ⊆ Ω) ∧
      Pairwise (fun i j => Disjoint (ball (c i) (ℓ / 2)) (ball (c j) (ℓ / 2))) := by
  classical
  have hcap := lattice_volume_deficit_le_boundaryLayer hℓ hΩ
  have hn : n ≤ (eligibleLatticeCubes ℓ Ω hℓ hΩ).card := by
    apply Nat.cast_le (α := ℝ) |>.mp
    apply (mul_le_mul_iff_left₀ (by positivity : 0 < ℓ ^ 3)).mp
    linarith only [hbudget, hcap]
  obtain ⟨s, hsub, hcard⟩ := Finset.exists_subset_card_eq hn
  let e : Fin n ≃ s := (Finset.equivFinOfCardEq hcard).symm
  refine ⟨fun i => latticeCenter ℓ (e i).val, ?_, ?_⟩
  · intro i x hx
    have hz := mem_eligibleLatticeCubes.mp (hsub (e i).property)
    apply hz
    intro a
    have hcoord := PiLp.norm_apply_le (x - latticeCenter ℓ (e i).val) a
    have habs : |x a - ℓ * (((e i).val a : ℝ) + 1 / 2)| ≤ ℓ / 2 := by
      change |(x - latticeCenter ℓ (e i).val) a| ≤ ℓ / 2
      rw [← Real.norm_eq_abs]
      exact hcoord.trans (by simpa only [mem_closedBall, dist_eq_norm] using hx)
    rcases abs_le.mp habs with ⟨hlo, hhi⟩
    constructor <;> linarith only [hlo, hhi]
  · intro i j hij
    apply lattice_inscribed_balls_pairwiseDisjoint hℓ
    intro heq
    apply hij
    exact e.injective (Subtype.ext heq)

end LiebThirring

end
