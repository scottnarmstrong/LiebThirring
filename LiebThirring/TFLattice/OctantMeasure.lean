/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Defs.Configuration

/-!
# Lebesgue measure of the positive octant

Coordinatewise absolute value folds the eight orthants onto the positive
octant, with multiplicity eight. Coordinate faces have measure zero.
Source: the unit-cell comparison in Lieb–Simon (1977) III.13, pp. 67–69 (sharp eigenvalue sums).
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace LiebThirring.TFLattice

theorem map_abs_volume : Measure.map (fun x : ℝ => |x|) volume =
    (2 : ℝ≥0∞) • volume.restrict (Ici 0) := by
  have hm : Measurable (fun x : ℝ => |x|) := by fun_prop
  ext s hs
  rw [Measure.map_apply hm hs, Measure.smul_apply, Measure.restrict_apply hs]
  have hae : (fun x : ℝ => |x|) ⁻¹' s =ᵐ[volume]
      (s ∩ Ioi 0) ∪ ((fun x : ℝ => -x) ⁻¹' (s ∩ Ioi 0)) := by
    filter_upwards [volume.ae_ne (0 : ℝ)] with x hx
    by_cases hp : 0 < x
    · simp only [mem_preimage, mem_union, mem_inter_iff, mem_Ioi,
        abs_of_pos hp]
      have hn : ¬0 < -x := by linarith
      simp [hp, hn]
    · have hn : x < 0 := lt_of_le_of_ne (le_of_not_gt hp) hx
      simp only [mem_preimage, mem_union, mem_inter_iff, mem_Ioi,
        abs_of_neg hn]
      have hneg : 0 < -x := by linarith
      simp [hp, hneg]
  have hd : Disjoint (s ∩ Ioi (0 : ℝ)) ((fun x : ℝ => -x) ⁻¹' (s ∩ Ioi 0)) := by
    apply disjoint_left.mpr
    intro x hx hy
    have hx' : 0 < x := hx.2
    have hy' : 0 < -x := hy.2
    linarith
  rw [measure_congr hae, measure_union hd ((hs.inter measurableSet_Ioi).preimage (by fun_prop)),
    Measure.measure_preimage_neg (volume : Measure ℝ) (s ∩ Ioi 0)]
  have he : volume (s ∩ Ioi (0 : ℝ)) = volume (s ∩ Ici 0) :=
    measure_congr (ae_eq_set_inter (Filter.EventuallyEq.refl _ _) Ioi_ae_eq_Ici)
  rw [he, smul_eq_mul, two_mul]

noncomputable def absoluteCoordinates (x : Fin 3 → ℝ) : Fin 3 → ℝ := fun i => |x i|

theorem measurable_absoluteCoordinates : Measurable absoluteCoordinates := by
  unfold absoluteCoordinates
  fun_prop

def coordinateOctant : Set (Fin 3 → ℝ) := Set.univ.pi fun _ => Ici 0

theorem map_absoluteCoordinates_volume :
    Measure.map absoluteCoordinates (volume : Measure (Fin 3 → ℝ)) =
      (8 : ℝ≥0∞) • volume.restrict coordinateOctant := by
  let : SigmaFinite (Measure.map (fun x : ℝ => |x|) volume) := by
    rw [map_abs_volume]
    rw [show (2 : ℝ≥0∞) = ((2 : ℝ≥0) : ℝ≥0∞) by norm_num]
    rw [Measure.coe_nnreal_smul]
    infer_instance
  have hmap : (Measure.pi fun _ : Fin 3 => (volume : Measure ℝ)).map absoluteCoordinates =
      Measure.pi fun _ : Fin 3 => (2 : ℝ≥0∞) • volume.restrict (Ici 0) := by
    unfold absoluteCoordinates
    rw [Measure.pi_map_pi (fun _ => (by fun_prop : Measurable (fun x : ℝ => |x|)).aemeasurable)]
    simp only [map_abs_volume]
  change (Measure.pi fun _ : Fin 3 => (volume : Measure ℝ)).map absoluteCoordinates = _
  rw [hmap]
  have : SigmaFinite ((2 : ℝ≥0∞) • (volume : Measure ℝ).restrict (Ici 0)) := by
    rw [show (2 : ℝ≥0∞) = ((2 : ℝ≥0) : ℝ≥0∞) by norm_num]
    rw [Measure.coe_nnreal_smul]
    infer_instance
  apply Measure.pi_eq
  intro s hs
  unfold coordinateOctant
  rw [Measure.smul_apply, Measure.restrict_apply (MeasurableSet.univ_pi hs),
    ← Set.pi_inter_distrib]
  change 8 • (Measure.pi fun _ : Fin 3 => (volume : Measure ℝ))
    (Set.univ.pi fun i => s i ∩ Ici 0) = _
  rw [Measure.pi_pi]
  simp only [Measure.smul_apply, smul_eq_mul, Measure.restrict_apply (hs _),
    Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  norm_num

end LiebThirring.TFLattice

end
