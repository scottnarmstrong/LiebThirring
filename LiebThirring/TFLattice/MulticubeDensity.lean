/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFLattice.ScaledDensity
public import LiebThirring.TFLattice.FiniteSupportLp

/-!
# Floor occupations on finitely many translated cubes

Filled-density convergence: normalized filled Dirichlet densities converge to the prescribed cube
step function in Lp for `1 ≤ p ≤ 2`, including L¹ and L⁵ᐟ³. The finite sum
argument requires no separation hypothesis; disjoint cubes are a special case.
Source: Lieb–Simon (1977) III.14, pp. 69–71.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace LiebThirring.TFLattice

noncomputable def multicubeDensity {q B : ℕ} (ℓ : {ℓ : ℝ // 0 < ℓ})
    (b : Fin B → Position) (s : Fin B → Finset (ModeIndex q)) : Position → ℝ :=
  fun x => ∑ i, physicalFilledDensity ℓ (b i) (s i) x

noncomputable def multicubeStep {B : ℕ} (ℓ : {ℓ : ℝ // 0 < ℓ})
    (b : Fin B → Position) (m : Fin B → ℝ) : Position → ℝ :=
  fun x => ∑ i, (physicalCube ℓ (b i)).indicator (fun _ => m i / ℓ.val ^ 3) x

theorem multicube_error_eq_sum {q B : ℕ} (ℓ : {ℓ : ℝ // 0 < ℓ})
    (b : Fin B → Position) (s : Fin B → Finset (ModeIndex q)) (a : ℝ) (m : Fin B → ℝ) :
    (fun x => multicubeDensity ℓ b s x / a - multicubeStep ℓ b m x) =
    ∑ i, (fun x => physicalFilledDensity ℓ (b i) (s i) x / a -
      (physicalCube ℓ (b i)).indicator (fun _ => m i / ℓ.val ^ 3) x) := by
  ext x
  simp only [multicubeDensity, multicubeStep, Finset.sum_apply,
    Finset.sum_sub_distrib, Finset.sum_div]

theorem multicube_error_zero_off {q B : ℕ} (ℓ : {ℓ : ℝ // 0 < ℓ})
    (b : Fin B → Position) (s : Fin B → Finset (ModeIndex q)) (a : ℝ) (m : Fin B → ℝ)
    {x : Position} (hx : x ∉ ⋃ i, physicalCube ℓ (b i)) :
    multicubeDensity ℓ b s x / a - multicubeStep ℓ b m x = 0 := by
  classical
  have hn (i : Fin B) : x ∉ physicalCube ℓ (b i) := fun hi => hx (mem_iUnion.mpr ⟨i, hi⟩)
  simp [multicubeDensity, multicubeStep, physicalFilledDensity, hn]

theorem volume_iUnion_physicalCube_ne_top {B : ℕ} (ℓ : {ℓ : ℝ // 0 < ℓ})
    (b : Fin B → Position) : volume (⋃ i, physicalCube ℓ (b i)) ≠ ∞ := by
  apply ne_of_lt
  apply lt_of_le_of_lt (measure_iUnion_fintype_le volume (fun i => physicalCube ℓ (b i)))
  exact ENNReal.sum_lt_top.mpr fun i _ => lt_top_iff_ne_top.mpr (volume_physicalCube_ne_top ℓ (b i))

theorem memLp_normalized_multicube_error {q B : ℕ}
    (ℓ : {ℓ : ℝ // 0 < ℓ}) (b : Fin B → Position)
    (s : Fin B → Finset (ModeIndex q)) (a : ℝ) (m : Fin B → ℝ)
    {p : ℝ≥0∞} (hp : p ≤ 2) :
    MemLp (fun x => multicubeDensity ℓ b s x / a - multicubeStep ℓ b m x) p volume := by
  have hf : MemLp (fun x => multicubeDensity ℓ b s x / a - multicubeStep ℓ b m x) 2 volume := by
    rw [multicube_error_eq_sum]
    exact memLp_finsetSum' _ fun i _ => memLp_normalized_physicalFilledDensity_sub_two ℓ (b i) (s i) a (m i)
  exact memLp_of_two_of_zero_off (MeasurableSet.iUnion fun i => measurableSet_physicalCube ℓ (b i))
    (volume_iUnion_physicalCube_ne_top ℓ b)
    (fun x hx => multicube_error_zero_off ℓ b s a m hx) hf hp

/-- Filled-density convergence's floor and finite-cube convergence, uniform over choices within the last shell. -/
theorem tendsto_lpNorm_floor_multicube_density {q B : ℕ} (hq : 0 < q)
    (ℓ : {ℓ : ℝ // 0 < ℓ}) (b : Fin B → Position) {ι : Type*} {l : Filter ι}
    {a : ι → ℝ} (ha : Tendsto a l atTop) (m : Fin B → ℝ) (hm : ∀ i, 0 ≤ m i)
    (s : ι → Fin B → Finset (ModeIndex q))
    (hs : ∀ j i, IsFilled IsDirichletIndex (s j i))
    (hcard : ∀ j i, (s j i).card = ⌊a j * m i⌋₊)
    {p : ℝ≥0∞} (hp1 : 1 ≤ p) (hp2 : p ≤ 2) :
    Tendsto (fun j => lpNorm (fun x => multicubeDensity ℓ b (s j) x / a j -
      multicubeStep ℓ b m x) p volume) l (𝓝 0) := by
  have ht2 : Tendsto (fun j => lpNorm (fun x => multicubeDensity ℓ b (s j) x / a j -
      multicubeStep ℓ b m x) 2 volume) l (𝓝 0) := by
    have hsum := tendsto_finsetSum Finset.univ (fun i _ =>
      tendsto_lpNorm_floor_density_two hq ℓ (b i) ha (hm i) (fun j => s j i)
        (fun j => hs j i) (fun j => hcard j i))
    simp only [Finset.sum_const_zero] at hsum
    apply squeeze_zero' (Eventually.of_forall fun _ => lpNorm_nonneg)
      (Eventually.of_forall fun j => ?_) hsum
    rw [multicube_error_eq_sum]
    exact lpNorm_sum_le
      (fun i _ => memLp_normalized_physicalFilledDensity_sub_two ℓ (b i) (s j i) (a j) (m i))
      (by norm_num)
  exact tendsto_lpNorm_of_two_of_zero_off
    (MeasurableSet.iUnion fun i => measurableSet_physicalCube ℓ (b i))
    (volume_iUnion_physicalCube_ne_top ℓ b)
    (fun j x hx => multicube_error_zero_off ℓ b (s j) (a j) m hx)
    (fun j => memLp_normalized_multicube_error ℓ b (s j) (a j) m (le_refl 2)) ht2 hp1 hp2

end LiebThirring.TFLattice

end
