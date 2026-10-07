/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.ThermoLimit.RoundingExpectation

/-! # Interpolation of finite integer packing inequalities -/

@[expose] public section

open MeasureTheory Set

namespace LiebThirring.ThermoLimit

/-- A packing inequality for every integer allocation passes to arbitrary nonnegative real
budgets by one common balanced rounding. -/
theorem interpolate_fin_packing {k : ℕ} (F : ℕ → ℝ) (G : Fin k → ℕ → ℝ)
    (x : Fin k → ℝ) (hx : ∀ i, 0 ≤ x i)
    (hpack : ∀ m : Fin k → ℕ, F (∑ i, m i) ≤ ∑ i, G i (m i)) :
    interpolate F (∑ i, x i) ≤ ∑ i, interpolate (G i) (x i) := by
  have hsumx : 0 ≤ ∑ i, x i := Finset.sum_nonneg fun i _ => hx i
  let m : ℝ → Fin k → ℕ := fun u i => balancedRoundNat x u i
  have hleft : IntegrableOn (fun u => F (natFloor ((∑ i, x i) + u))) (Ico 0 1) :=
    integrableOn_comp_natFloor_add F hsumx
  have hright : IntegrableOn (fun u => ∑ i, G i (m u i)) (Ico 0 1) := by
    apply integrable_finsetSum Finset.univ
    intro i _
    exact integrableOn_comp_balancedRoundNat (G i) hx i
  have hpoint : ∀ u ∈ Ico (0 : ℝ) 1,
      F (natFloor ((∑ i, x i) + u)) ≤ ∑ i, G i (m u i) := by
    intro u hu
    rw [← sum_balancedRoundNat hx hu]
    exact hpack (m u)
  have hae : ∀ᵐ u ∂volume.restrict (Ico (0 : ℝ) 1),
      F (natFloor ((∑ i, x i) + u)) ≤ ∑ i, G i (m u i) := by
    exact (ae_restrict_iff' measurableSet_Ico).2 (ae_of_all _ fun u hu => hpoint u hu)
  have hint := integral_mono_ae hleft hright hae
  rw [integral_comp_natFloor_add F hsumx] at hint
  have hrw : (∫ u in Ico (0 : ℝ) 1, ∑ i, G i (m u i)) =
      ∑ i, interpolate (G i) (x i) := by
    rw [integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro i _
      exact integral_comp_balancedRoundNat (G i) hx i
    · intro i _
      exact integrableOn_comp_balancedRoundNat (G i) hx i
  rwa [hrw] at hint

/-- Finset-indexed form of `interpolate_fin_packing`, used by geometric packings whose labels
live in an ambient type. -/
theorem interpolate_finset_packing {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (F : ℕ → ℝ) (G : ι → ℕ → ℝ) (x : ι → ℝ)
    (hx : ∀ i ∈ s, 0 ≤ x i)
    (hpack : ∀ m : ι → ℕ, F (∑ i ∈ s, m i) ≤ ∑ i ∈ s, G i (m i)) :
    interpolate F (∑ i ∈ s, x i) ≤ ∑ i ∈ s, interpolate (G i) (x i) := by
  classical
  let e := Fintype.equivFin s
  let x' : Fin (Fintype.card s) → ℝ := fun j => x (e.symm j).val
  let G' : Fin (Fintype.card s) → ℕ → ℝ := fun j => G (e.symm j).val
  have hx' : ∀ j, 0 ≤ x' j := fun j => hx _ (e.symm j).property
  have hpack' : ∀ m : Fin (Fintype.card s) → ℕ,
      F (∑ j, m j) ≤ ∑ j, G' j (m j) := by
    intro m
    let m' : ι → ℕ := fun i => if hi : i ∈ s then m (e ⟨i, hi⟩) else 0
    have h := hpack m'
    have hm : (∑ i ∈ s, m' i) = ∑ j, m j := by
      calc
        _ = ∑ a : s, m' a.val := Finset.sum_subtype s (by simp) m'
        _ = ∑ a : s, m (e a) := by apply Finset.sum_congr rfl; intro a _; simp [m']
        _ = ∑ j, m j := e.sum_comp m
    have hG : (∑ i ∈ s, G i (m' i)) = ∑ j, G' j (m j) := by
      calc
        _ = ∑ a : s, G a.val (m' a.val) :=
          Finset.sum_subtype s (by simp) (fun i => G i (m' i))
        _ = ∑ a : s, G a.val (m (e a)) := by
          apply Finset.sum_congr rfl
          intro a _
          simp [m']
        _ = ∑ j, G (e.symm j).val (m j) := by
          simpa using e.sum_comp (fun j => G (e.symm j).val (m j))
        _ = _ := by rfl
    rwa [hm, hG] at h
  have h := interpolate_fin_packing F G' x' hx' hpack'
  have hxsum : (∑ i ∈ s, x i) = ∑ j, x' j := by
    calc
      _ = ∑ a : s, x a.val := Finset.sum_subtype s (by simp) x
      _ = ∑ j, x (e.symm j).val := by
        simpa using e.sum_comp (fun j => x (e.symm j).val)
      _ = _ := by rfl
  have hGsum : (∑ i ∈ s, interpolate (G i) (x i)) =
      ∑ j, interpolate (G' j) (x' j) := by
    calc
      _ = ∑ a : s, interpolate (G a.val) (x a.val) :=
        Finset.sum_subtype s (by simp) (fun i => interpolate (G i) (x i))
      _ = ∑ j, interpolate (G (e.symm j).val) (x (e.symm j).val) := by
        simpa using e.sum_comp (fun j => interpolate (G (e.symm j).val) (x (e.symm j).val))
      _ = _ := by rfl
  rwa [hxsum, hGsum]

end LiebThirring.ThermoLimit

end
