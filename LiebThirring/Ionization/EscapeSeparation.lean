/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Ionization.EscapeWedgeSmooth
public import LiebThirring.Ionization.EscapeGeometry
public import LiebThirring.Ionization.EscapeDisjoint

/-! # Closed support separation of the actual wedge summands -/

public section

open MeasureTheory Set Function
open scoped ENNReal NNReal SchwartzMap

namespace LiebThirring

/-- The support conditions for a summand with its selected particle far away. -/
theorem escape_disjoint_remote_summands {H : Type*} {n : ℕ}
    [NormedAddCommGroup H] (f : Fin (n + 1) → Configuration (n + 1) → H)
    {R L : ℝ} (hR : 0 ≤ R) (hL : 0 < L)
    (hf : ∀ i x, f i x ≠ 0 →
      ‖particlePosition x i - escapeCenter R L‖ ≤ L ∧
        ∀ j, j ≠ i → ‖particlePosition x j‖ ≤ R) :
    Pairwise (Disjoint on fun i => tsupport (f i)) := by
  let S (i : Fin (n + 1)) : Set (Configuration (n + 1)) :=
    {x | ‖particlePosition x i - escapeCenter R L‖ ≤ L} ∩
      ⋂ j : Fin (n + 1), {x | j ≠ i → ‖particlePosition x j‖ ≤ R}
  have hc (i : Fin (n + 1)) : IsClosed (S i) := by
    apply IsClosed.inter
    · exact isClosed_le (((contDiff_particlePosition i).continuous.sub continuous_const).norm)
        continuous_const
    · have hcj (j : Fin (n + 1)) :
          IsClosed {x : Configuration (n + 1) | j ≠ i → ‖particlePosition x j‖ ≤ R} := by
        by_cases hji : j ≠ i
        · have he : {x : Configuration (n + 1) | j ≠ i → ‖particlePosition x j‖ ≤ R} =
              {x : Configuration (n + 1) | ‖particlePosition x j‖ ≤ R} :=
            Set.ext (fun _ => ⟨fun h => h hji, fun h _ => h⟩)
          rw [he]
          exact isClosed_le (contDiff_particlePosition j).continuous.norm continuous_const
        · have he : {x : Configuration (n + 1) | j ≠ i → ‖particlePosition x j‖ ≤ R} =
              Set.univ := Set.ext (fun _ => ⟨fun _ => mem_univ _, fun _ h => (hji h).elim⟩)
          rw [he]
          exact isClosed_univ
      exact isClosed_iInter hcj
  have hs (i : Fin (n + 1)) : tsupport (f i) ⊆ S i := by
    apply closure_minimal _ (hc i)
    intro x hx
    exact ⟨(hf i x hx).1, mem_iInter.mpr (fun j => (hf i x hx).2 j)⟩
  intro i j hij
  apply Set.disjoint_left.mpr
  intro x hi hj
  have hix := hs i hi
  have hjx := hs j hj
  have hbound := escape_remote_distance hR hL.le
    (mem_iInter.mp hjx.2 i hij) hix.1
  rw [sub_self, norm_zero] at hbound
  exact (not_le.mpr (mul_pos (by norm_num : (0 : ℝ) < 3) hL)) hbound

/-- The actual omitted-particle tensor terms have separated closed supports. -/
theorem escape_disjoint_wedgeTermAmplitudes {N q : ℕ}
    (f : Configuration N → SpinAmplitudes N q)
    (h : Position → EuclideanSpace ℂ (Fin q)) {R L : ℝ}
    (hR : 0 ≤ R) (hL : 0 < L)
    (hf : ∀ x ∈ tsupport f, ∀ j, ‖particlePosition x j‖ ≤ R)
    (hh : ∀ y ∈ tsupport h, ‖y - escapeCenter R L‖ ≤ L) :
    Pairwise (Disjoint on fun i => tsupport (escapeWedgeTermAmplitudes f h i)) := by
  apply escape_disjoint_remote_summands (escapeWedgeTermAmplitudes f h) hR hL
  intro i x hx
  have he : ∃ s, escapeWedgeTerm (fun y t => f y t) (fun y t => h y t) i x s ≠ 0 := by
    by_contra he
    apply hx
    apply PiLp.ext
    intro s
    change escapeWedgeTerm (fun y t => f y t) (fun y t => h y t) i x s = 0
    exact not_not.mp (fun hs => he ⟨s, hs⟩)
  obtain ⟨s, hs⟩ := he
  obtain ⟨hfx, hhx⟩ := escapeWedgeTerm_mem_tsupport f h i x s hs
  refine ⟨hh _ hhx, ?_⟩
  intro j hji
  obtain ⟨k, hk⟩ := escape_omitted_index i j hji
  have hp : particlePosition (escapeOmitPositions i x) k = particlePosition x j := by
    ext a
    change x (Equiv.swap 0 i k.succ, a) = x (j, a)
    rw [hk]
  exact hp ▸ hf _ hfx k

end LiebThirring

end
