/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFLattice.MulticubeDensity
public import LiebThirring.Packing.LatticeGeometry

/-!
# Changing half-open cube boundaries

The filled density uses Ioc cubes; packing and TF upper trials use Ico
cubes. They agree almost everywhere, including their step indicators.
Source: Lieb–Simon (1977) III.14, pp. 69–71 (filled-density convergence); coordinate faces are null.
-/

public section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace LiebThirring.TFLattice

theorem physicalCube_ae_eq_latticeCell (ℓ : {ℓ : ℝ // 0 < ℓ}) (z : LatticeIndex) :
    physicalCube ℓ (latticeCorner ℓ.val z) =ᵐ[volume] latticeCell ℓ.val z := by
  have he : (Set.univ.pi fun _ : Fin 3 => Ioc (0 : ℝ) ℓ.val) =ᵐ[volume]
      Set.univ.pi fun _ : Fin 3 => Ico (0 : ℝ) ℓ.val :=
    Measure.ae_eq_set_pi fun _ _ => Ico_ae_eq_Ioc.symm
  have hp := (measurePreserving_cubeCoordinates (latticeCorner ℓ.val z)).quasiMeasurePreserving.preimage_ae_eq he
  have hset : cubeCoordinates (latticeCorner ℓ.val z) ⁻¹'
      (Set.univ.pi fun _ : Fin 3 => Ico (0 : ℝ) ℓ.val) = latticeCell ℓ.val z := by
    ext x
    change (∀ i ∈ Set.univ, 0 ≤ x i - ℓ.val * (z i : ℝ) ∧
      x i - ℓ.val * (z i : ℝ) < ℓ.val) ↔ _
    simp only [Set.mem_univ, forall_const, latticeCell, Set.mem_ofPred_eq]
    constructor <;> intro hx i <;> obtain ⟨h1, h2⟩ := hx i <;> constructor <;> nlinarith
  rw [hset] at hp
  exact hp

theorem multicubeStep_ae_eq_latticeStep {B : ℕ} (ℓ : {ℓ : ℝ // 0 < ℓ})
    (z : Fin B → LatticeIndex) (m : Fin B → ℝ) :
    multicubeStep ℓ (fun i => latticeCorner ℓ.val (z i)) m =ᵐ[volume]
      (fun x => ∑ i, (latticeCell ℓ.val (z i)).indicator (fun _ => m i / ℓ.val ^ 3) x) := by
  have he (i : Fin B) := physicalCube_ae_eq_latticeCell ℓ (z i)
  filter_upwards [ae_all_iff.mpr he] with x hx
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hm : x ∈ physicalCube ℓ (latticeCorner ℓ.val (z i))
  · rw [indicator_of_mem hm, indicator_of_mem ((hx i).mp hm)]
  · rw [indicator_of_notMem hm, indicator_of_notMem (fun hi => hm ((hx i).mpr hi))]

/-- Filled-density convergence in the exact Ico cell convention used by TFUpper. -/
theorem tendsto_lpNorm_floor_lattice_density {q B : ℕ} (hq : 0 < q)
    (ℓ : {ℓ : ℝ // 0 < ℓ}) (z : Fin B → LatticeIndex) {ι : Type*} {l : Filter ι}
    {a : ι → ℝ} (ha : Tendsto a l atTop) (m : Fin B → ℝ) (hm : ∀ i, 0 ≤ m i)
    (s : ι → Fin B → Finset (ModeIndex q))
    (hs : ∀ j i, IsFilled IsDirichletIndex (s j i))
    (hcard : ∀ j i, (s j i).card = ⌊a j * m i⌋₊)
    {p : ℝ≥0∞} (hp1 : 1 ≤ p) (hp2 : p ≤ 2) :
    (∀ j, MemLp (fun x =>
      multicubeDensity ℓ (fun i => latticeCorner ℓ.val (z i)) (s j) x / a j -
      ∑ i, (latticeCell ℓ.val (z i)).indicator (fun _ => m i / ℓ.val ^ 3) x) p volume) ∧
    Tendsto (fun j => lpNorm (fun x =>
      multicubeDensity ℓ (fun i => latticeCorner ℓ.val (z i)) (s j) x / a j -
      ∑ i, (latticeCell ℓ.val (z i)).indicator (fun _ => m i / ℓ.val ^ 3) x) p volume) l (𝓝 0) := by
  have he (j : ι) :
      (fun x => multicubeDensity ℓ (fun i => latticeCorner ℓ.val (z i)) (s j) x / a j -
        multicubeStep ℓ (fun i => latticeCorner ℓ.val (z i)) m x) =ᵐ[volume]
      (fun x => multicubeDensity ℓ (fun i => latticeCorner ℓ.val (z i)) (s j) x / a j -
        ∑ i, (latticeCell ℓ.val (z i)).indicator (fun _ => m i / ℓ.val ^ 3) x) :=
    (Filter.EventuallyEq.refl _ _).sub (multicubeStep_ae_eq_latticeStep ℓ z m)
  constructor
  · intro j
    exact (memLp_normalized_multicube_error ℓ _ (s j) (a j) m hp2).ae_eq (he j)
  · have ht := tendsto_lpNorm_floor_multicube_density hq ℓ (fun i => latticeCorner ℓ.val (z i)) ha m hm s hs hcard hp1 hp2
    convert ht using 1
    ext j
    exact congrArg ENNReal.toReal (eLpNorm_congr_ae (he j).symm)

end LiebThirring.TFLattice

end
