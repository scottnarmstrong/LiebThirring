/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFLattice.FilledModes
public import LiebThirring.ThomasFermi.KineticConstant

/-! # Lowest occupations minimize the finite Neumann eigenvalue sum -/

@[expose] public section
namespace LiebThirring.TFSectors
open TFLattice

theorem sum_le_sum_of_card_eq_of_le_sdiff {A : Type*} [DecidableEq A]
    (f : A → ℝ) {s t : Finset A} (hc : s.card = t.card)
    (horder : ∀ p ∈ s \ t, ∀ r ∈ t \ s, f p ≤ f r) :
    ∑ p ∈ s, f p ≤ ∑ r ∈ t, f r := by
  classical
  let e := Finset.equivOfCardEq (Finset.card_sdiff_comm hc)
  have hd : ∑ p ∈ s \ t, f p ≤ ∑ r ∈ t \ s, f r := by
    rw [← Finset.sum_coe_sort (s \ t), ← Finset.sum_coe_sort (t \ s)]
    calc
      _ ≤ ∑ p : ↥(s \ t), f (e p) := Finset.sum_le_sum (fun p _ => horder p p.property _ (e p).property)
      _ = _ := e.sum_comp (fun r : ↥(t \ s) => f r)
  have hdiff := Finset.sum_sdiff_sub_sum_sdiff (s₁ := t) (s₂ := s) (f := f)
  linarith

theorem sum_cubeEigenvalue_le_of_isFilled {q : ℕ} (ℓ : {ℓ : ℝ // 0 < ℓ})
    {s t : Finset (ModeIndex q)} (hs : IsFilled (fun _ => True) s)
    (hc : s.card = t.card) :
    ∑ p ∈ s, cubeEigenvalue ℓ p ≤ ∑ p ∈ t, cubeEigenvalue ℓ p := by
  rw [sum_cubeEigenvalue, sum_cubeEigenvalue]
  apply mul_le_mul_of_nonneg_left _ (div_nonneg (sq_nonneg _) (sq_nonneg _))
  apply sum_le_sum_of_card_eq_of_le_sdiff _ hc
  intro p hp r hr
  exact_mod_cast hs.2 p (Finset.mem_sdiff.mp hp).1 r trivial (Finset.mem_sdiff.mp hr).2

/-- The sharp eigenvalue sums sharp lower estimate for filled sets implies the same estimate for
every finite set of distinct one-particle spatial-and-spin labels. -/
theorem sum_cubeEigenvalue_ge_of_filled_bound {q : ℕ} (hq : 1 ≤ q)
    (ℓ : {ℓ : ℝ // 0 < ℓ}) (Cq : ℝ)
    (hsharp : ∀ s : Finset (ModeIndex q), IsFilled (fun _ => True) s →
      (tfKineticConstant ⟨q, hq⟩).val * ℓ.val⁻¹ ^ 2 * (s.card : ℝ) ^ ((5 : ℝ) / 3) -
        Cq * ℓ.val⁻¹ ^ 2 * (s.card : ℝ) ^ ((4 : ℝ) / 3) ≤
          ∑ p ∈ s, cubeEigenvalue ℓ p)
    (t : Finset (ModeIndex q)) :
    (tfKineticConstant ⟨q, hq⟩).val * ℓ.val⁻¹ ^ 2 * (t.card : ℝ) ^ ((5 : ℝ) / 3) -
      Cq * ℓ.val⁻¹ ^ 2 * (t.card : ℝ) ^ ((4 : ℝ) / 3) ≤
        ∑ p ∈ t, cubeEigenvalue ℓ p := by
  obtain ⟨s, hc, hs⟩ := exists_isFilled_neumann hq t.card
  have h := hsharp s hs
  rw [hc] at h
  exact h.trans (sum_cubeEigenvalue_le_of_isFilled ℓ hs hc)

end LiebThirring.TFSectors
end
