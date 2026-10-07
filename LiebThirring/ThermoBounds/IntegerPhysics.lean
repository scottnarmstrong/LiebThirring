/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.ThermoBounds.PackingInterpolation
public import LiebThirring.ThermoBounds.Energy

/-!
# Integer physics inputs in the arbitrary-radius argument

These conditional helpers use the neutral-sector specialization of neutral variational packing
on the union of finitely many disjoint balls, and domain monotonicity
and ball translation equality. The geometric hypotheses describe the
particular family to which those laws are applied; no packing is assumed
to exist. coupled integer interpolation's proved coupled rounding lifts the integer inequality.

The global physical hypotheses used later quantify over every finite family.
Taking the union as the containing region is a direct specialization of
neutral variational packing; domain inclusion then gives any larger containing ball. All regions
here are neutral balls, so no exceptional-region screening premise is needed.
-/

public section

open Finset Metric Set
open LiebThirring.ThermoLimit

namespace LiebThirring.ThermoBounds

/-- Integer neutral variational packing plus domain inclusion and exact coupled integer interpolation rounding, for a
specified geometric family. This is an internal conditional helper. -/
theorem interpolate_ball_packing_of_integer_inputs
    {ι : Type} [DecidableEq ι] {E : Set Position → ℕ → ℝ}
    (hmono : ∀ Ω Ω', IsOpen Ω → Ω.Nonempty → Bornology.IsBounded Ω →
      IsOpen Ω' → Ω'.Nonempty → Bornology.IsBounded Ω' →
      Ω ⊆ Ω' → ∀ m, E Ω' m ≤ E Ω m)
    (htranslation : ∀ c R, 0 < R → ∀ m,
      E (ball c R) m = E (ball (0 : Position) R) m)
    (hpacking : ∀ (s : Finset ι) (c : ι → Position) (r : ι → ℝ) (m : ι → ℕ),
      s.Nonempty →
      (∀ i ∈ s, 0 < r i) →
      (s : Set ι).PairwiseDisjoint (fun i => ball (c i) (r i)) →
      E (⋃ i ∈ s, ball (c i) (r i)) (∑ i ∈ s, m i) ≤
        ∑ i ∈ s, E (ball (c i) (r i)) (m i))
    (s : Finset ι) (c : ι → Position) (r x : ι → ℝ) (L : ℝ)
    (hs : s.Nonempty) (hL : 0 < L)
    (hpos : ∀ i ∈ s, 0 < r i)
    (hsub : ∀ i ∈ s, ball (c i) (r i) ⊆ ball (0 : Position) L)
    (hdisj : (s : Set ι).PairwiseDisjoint (fun i => ball (c i) (r i)))
    (hx : ∀ i ∈ s, 0 ≤ x i) :
    interpolate (E (ball (0 : Position) L)) (∑ i ∈ s, x i) ≤
      ∑ i ∈ s, interpolate (E (ball (0 : Position) (r i))) (x i) := by
  have hsubUnion : (⋃ i ∈ s, ball (c i) (r i)) ⊆ ball (0 : Position) L :=
    iUnion₂_subset hsub
  have hopen : IsOpen (⋃ i ∈ s, ball (c i) (r i)) :=
    isOpen_iUnion fun _ => isOpen_iUnion fun _ => isOpen_ball
  have hnonempty : (⋃ i ∈ s, ball (c i) (r i)).Nonempty := by
    obtain ⟨i, hi⟩ := hs
    exact ⟨c i, mem_iUnion₂.mpr ⟨i, hi, mem_ball_self (hpos i hi)⟩⟩
  have hp := interpolate_finset_packing s (E (ball (0 : Position) L))
    (fun i => E (ball (c i) (r i))) x hx (fun m =>
      (hmono _ _ hopen hnonempty (isBounded_ball.subset hsubUnion)
        isOpen_ball (nonempty_ball.mpr hL) isBounded_ball hsubUnion _).trans
          (hpacking s c r m hs hpos hdisj))
  calc
    _ ≤ ∑ i ∈ s, interpolate (E (ball (c i) (r i))) (x i) := hp
    _ = _ := by
      apply sum_congr rfl
      intro i hi
      have he : E (ball (c i) (r i)) = E (ball (0 : Position) (r i)) := by
        funext m
        exact htranslation _ _ (hpos i hi) m
      rw [he]

end LiebThirring.ThermoBounds

end
