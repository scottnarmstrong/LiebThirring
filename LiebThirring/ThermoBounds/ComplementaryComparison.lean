/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.ThermoBounds.IntegerPhysics
public import LiebThirring.ThermoBounds.TruncatedAlgebra
public import LiebThirring.ThermoBounds.LatticeSwissCheese
public import LiebThirring.ThermoBounds.ComparisonLimits
import Mathlib.Tactic

/-!
# Finite complementary comparison

This is the finite inequality in complementary packing comparison. The target ball is one member of an actual finite
packing, and the remaining members are the truncated Swiss-cheese families in lattice cubes
inside the complementary annulus. The only physical assumptions are integer energy laws;
coupled interpolation is supplied by coupled integer interpolation.
-/

public section

open Finset Metric Set
open LiebThirring.ThermoLimit

namespace LiebThirring.ThermoBounds

/-- The finite complementary comparison used in complementary packing comparison. -/
theorem finite_complementary_comparison_of_integer_inputs
    {E : Set Position → ℕ → ℝ}
    (hmono : ∀ Ω Ω', IsOpen Ω → Ω.Nonempty → Bornology.IsBounded Ω →
      IsOpen Ω' → Ω'.Nonempty → Bornology.IsBounded Ω' →
      Ω ⊆ Ω' → ∀ m, E Ω' m ≤ E Ω m)
    (htranslation : ∀ c R, 0 < R → ∀ m,
      E (ball c R) m = E (ball (0 : Position) R) m)
    (hpacking : ∀ (ι : Type) (s : Finset ι) (c : ι → Position)
      (r : ι → ℝ) (m : ι → ℕ), s.Nonempty →
      (∀ i ∈ s, 0 < r i) →
      (s : Set ι).PairwiseDisjoint (fun i => ball (c i) (r i)) →
      E (⋃ i ∈ s, ball (c i) (r i)) (∑ i ∈ s, m i) ≤
        ∑ i ∈ s, E (ball (c i) (r i)) (m i))
    {ell L : ℝ} (hell : 0 < ell) (hL : 0 < L) {K k t : ℕ}
    (hK : 0 < K) (htk : t < k)
    (hcover : L ≤ (28 : ℝ) ^ K)
    (hvol : ell ^ 3 = standardVolume ballVolumeConstant k) (m : ℕ) :
    neutralStandardSequence E K
        (((m : ℝ) / neutralBallVolume L) *
          (neutralBallVolume L / standardVolume ballVolumeConstant K +
            retainedFraction t *
              (annulusLatticeCount ell L ((28 : ℝ) ^ K) hell * ell ^ 3 /
                standardVolume ballVolumeConstant K))) ≤
      (neutralBallVolume L / standardVolume ballVolumeConstant K) *
          neutralBallDensity E L m +
        (annulusLatticeCount ell L ((28 : ℝ) ^ K) hell * ell ^ 3 /
            standardVolume ballVolumeConstant K) *
          ∑ j ∈ range t, ((1 / 28 : ℝ) * swissCheeseGamma ^ j) *
            neutralStandardSequence E (k - j - 1)
              ((m : ℝ) / neutralBallVolume L) := by
  classical
  let R : ℝ := (28 : ℝ) ^ K
  let Ω : Set Position := openAnnulus (0 : Position) L R
  let P := (interiorLatticeCubes ell Ω hell (isBounded_ball.subset sdiff_subset)).product
    (swissCheeseLevels t)
  let S : Finset (Option (LatticeIndex × SwissCheeseLabel)) :=
    insert none (P.map Function.Embedding.some)
  let r : Option (LatticeIndex × SwissCheeseLabel) → ℝ
    | none => L
    | some p => (28 : ℝ) ^ (k - p.2.1 - 1)
  let s : ℝ := (m : ℝ) / neutralBallVolume L
  let x : Option (LatticeIndex × SwissCheeseLabel) → ℝ
    | none => m
    | some p => s * standardVolume ballVolumeConstant (k - p.2.1 - 1)
  let n : ℕ := annulusLatticeCount ell L R hell
  let Vk : ℝ := standardVolume ballVolumeConstant k
  let VK : ℝ := standardVolume ballVolumeConstant K
  have hR : 0 < R := pow_pos (by norm_num) _
  have hΩ : Bornology.IsBounded Ω := isBounded_ball.subset sdiff_subset
  have hgeom : ell ^ 3 = ballVolumeConstant * ((28 : ℝ) ^ k) ^ 3 := by
    rw [hvol, ← neutralBallVolume_standard]
    rfl
  obtain ⟨c₀, hc₀, hd₀⟩ := exists_lattice_swissCheese_packing hell hΩ htk.le hgeom
  let c : Option (LatticeIndex × SwissCheeseLabel) → Position
    | none => 0
    | some p => c₀ p
  have hnone : none ∉ P.map Function.Embedding.some := by simp
  have hS : S.Nonempty := ⟨none, mem_insert_self none _⟩
  have hpos : ∀ i ∈ S, 0 < r i := by
    intro i _
    cases i with
    | none => exact hL
    | some p => exact pow_pos (by norm_num) _
  have hsub : ∀ i ∈ S, ball (c i) (r i) ⊆ ball (0 : Position) R := by
    intro i hi
    cases i with
    | none =>
        dsimp [c, r]
        exact ball_subset_ball hcover
    | some p =>
        have hpmap : some p ∈ P.map Function.Embedding.some := by
          simpa [S, hnone] using hi
        have hp : p ∈ P := by simpa using hpmap
        exact ball_subset_closedBall.trans ((hc₀ p hp).trans sdiff_subset)
  have htarget_disjoint : ∀ p ∈ P,
      Disjoint (ball (0 : Position) L)
        (ball (c₀ p) ((28 : ℝ) ^ (k - p.2.1 - 1))) := by
    intro p hp
    apply Set.disjoint_left.mpr
    intro y hyL hyp
    have hyΩ : y ∈ Ω := hc₀ p hp (ball_subset_closedBall hyp)
    exact hyΩ.2 (ball_subset_closedBall hyL)
  have hdisj : (S : Set (Option (LatticeIndex × SwissCheeseLabel))).PairwiseDisjoint
      (fun i => ball (c i) (r i)) := by
    intro i hi j hj hij
    cases i with
    | none =>
        cases j with
        | none => exact (hij rfl).elim
        | some p =>
            have hpmap : some p ∈ P.map Function.Embedding.some := by
              simpa [S, hnone] using hj
            have hp : p ∈ P := by simpa using hpmap
            exact htarget_disjoint p hp
    | some p =>
        cases j with
        | none =>
            have hpmap : some p ∈ P.map Function.Embedding.some := by
              simpa [S, hnone] using hi
            have hp : p ∈ P := by simpa using hpmap
            exact (htarget_disjoint p hp).symm
        | some q =>
            have hpmap : some p ∈ P.map Function.Embedding.some := by
              simpa [S, hnone] using hi
            have hqmap : some q ∈ P.map Function.Embedding.some := by
              simpa [S, hnone] using hj
            have hp : p ∈ P := by simpa using hpmap
            have hq : q ∈ P := by simpa using hqmap
            have hpq : p ≠ q := by simpa using hij
            exact hd₀ hp hq hpq
  have hs : 0 ≤ s := div_nonneg (Nat.cast_nonneg m) (neutralBallVolume_pos hL).le
  have hx : ∀ i ∈ S, 0 ≤ x i := by
    intro i _
    cases i with
    | none => exact Nat.cast_nonneg m
    | some p => exact mul_nonneg hs (standardVolume_pos ballVolumeConstant_pos _).le
  have hp := interpolate_ball_packing_of_integer_inputs hmono htranslation
    (hpacking (Option (LatticeIndex × SwissCheeseLabel))) S c r x R hS hR hpos hsub hdisj hx
  have hbudgetFill : ∑ p ∈ P,
      s * standardVolume ballVolumeConstant (k - p.2.1 - 1) =
      (n : ℝ) * (s * Vk * retainedFraction t) := by
    dsimp only [P, n, Vk, Ω, R]
    rw [show (∑ p ∈ P, s * standardVolume ballVolumeConstant (k - p.2.1 - 1)) =
        (n : ℝ) * ∑ j ∈ range t, (swissCheeseMultiplicity j : ℝ) *
          (s * standardVolume ballVolumeConstant (k - j - 1)) from
      sum_lattice_swissCheese_levels hell hΩ t
        (fun j => s * standardVolume ballVolumeConstant (k - j - 1))]
    rw [sum_truncatedBudget htk.le]
    rw [retainedFraction]
  have hbudget : (∑ i ∈ S, x i) =
      (m : ℝ) + (n : ℝ) * (s * Vk * retainedFraction t) := by
    calc
      ∑ i ∈ S, x i = x none + ∑ i ∈ P.map Function.Embedding.some, x i := by
        exact sum_insert hnone
      _ = x none + ∑ p ∈ P, x (some p) := by
        simp only [sum_map, Function.Embedding.some_apply]
      _ = (m : ℝ) + ∑ p ∈ P,
          s * standardVolume ballVolumeConstant (k - p.2.1 - 1) := by rfl
      _ = _ := by rw [hbudgetFill]
  have henergyFill : ∑ p ∈ P,
      interpolate (E (ball (0 : Position) ((28 : ℝ) ^ (k - p.2.1 - 1))))
        (s * standardVolume ballVolumeConstant (k - p.2.1 - 1)) =
      (n : ℝ) * (Vk * ∑ j ∈ range t,
        ((1 / 28 : ℝ) * swissCheeseGamma ^ j) *
          neutralStandardSequence E (k - j - 1) s) := by
    dsimp only [P, n, Vk, Ω, R]
    rw [show (∑ p ∈ P,
        interpolate (E (ball (0 : Position) ((28 : ℝ) ^ (k - p.2.1 - 1))))
          (s * standardVolume ballVolumeConstant (k - p.2.1 - 1))) =
        (n : ℝ) * ∑ j ∈ range t, (swissCheeseMultiplicity j : ℝ) *
          interpolate (E (ball (0 : Position) ((28 : ℝ) ^ (k - j - 1))))
            (s * standardVolume ballVolumeConstant (k - j - 1)) from
      sum_lattice_swissCheese_levels (Ω := Ω) hell hΩ t
        (fun j => interpolate (E (ball (0 : Position) ((28 : ℝ) ^ (k - j - 1))))
          (s * standardVolume ballVolumeConstant (k - j - 1)))]
    rw [sum_truncatedEnergy htk]
  have henergy : (∑ i ∈ S,
      interpolate (E (ball (0 : Position) (r i))) (x i)) =
      E (ball (0 : Position) L) m +
        (n : ℝ) * (Vk * ∑ j ∈ range t,
          ((1 / 28 : ℝ) * swissCheeseGamma ^ j) *
            neutralStandardSequence E (k - j - 1) s) := by
    calc
      ∑ i ∈ S, interpolate (E (ball (0 : Position) (r i))) (x i) =
          interpolate (E (ball (0 : Position) (r none))) (x none) +
            ∑ i ∈ P.map Function.Embedding.some,
              interpolate (E (ball (0 : Position) (r i))) (x i) := by
        exact sum_insert hnone
      _ = interpolate (E (ball (0 : Position) L)) m +
          ∑ p ∈ P, interpolate
            (E (ball (0 : Position) ((28 : ℝ) ^ (k - p.2.1 - 1))))
            (s * standardVolume ballVolumeConstant (k - p.2.1 - 1)) := by
        simp only [sum_map]
        rfl
      _ = _ := by rw [interpolate_nat, henergyFill]
  rw [hbudget, henergy] at hp
  have hVK : 0 < VK := standardVolume_pos ballVolumeConstant_pos K
  have hVKn : standardVolume ballVolumeConstant K ≠ 0 :=
    (standardVolume_pos ballVolumeConstant_pos K).ne'
  have htotal : (m : ℝ) + (n : ℝ) * (s * Vk * retainedFraction t) =
      (s * (neutralBallVolume L / VK + retainedFraction t *
        ((n : ℝ) * ell ^ 3 / VK))) * VK := by
    dsimp [s, Vk, VK]
    rw [← hvol]
    field_simp [hVKn, neutralBallVolume_pos hL |>.ne']
  rw [htotal] at hp
  rw [neutralStandardSequence_eq hK]
  apply (div_le_iff₀ hVK).2
  calc
    interpolate (E (ball (0 : Position) R))
        ((s * (neutralBallVolume L / VK + retainedFraction t *
          ((n : ℝ) * ell ^ 3 / VK))) * VK) ≤
      E (ball (0 : Position) L) m +
        (n : ℝ) * (Vk * ∑ j ∈ range t,
          ((1 / 28 : ℝ) * swissCheeseGamma ^ j) *
            neutralStandardSequence E (k - j - 1) s) := hp
    _ = ((neutralBallVolume L / VK) * neutralBallDensity E L m +
        ((n : ℝ) * ell ^ 3 / VK) * ∑ j ∈ range t,
          ((1 / 28 : ℝ) * swissCheeseGamma ^ j) *
            neutralStandardSequence E (k - j - 1) s) * VK := by
      dsimp [neutralBallDensity, n, Vk, VK, s]
      rw [← hvol]
      field_simp [hVKn, neutralBallVolume_pos hL |>.ne']
  
end LiebThirring.ThermoBounds

end
