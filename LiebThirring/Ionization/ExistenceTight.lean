/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Ionization.EscapingInside
public import LiebThirring.Variational.CompactForm

/-! # Coercivity and quantitative particle-tail estimates for minimizing sequences

The scalar tail estimate records the dependence on the binding gap in estimate.
-/

public section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology

namespace LiebThirring

/-- Strict atomic binding is a positive gap between finite real energies. -/
theorem atomicGroundStateEnergy_toReal_lt_of_lt (q : ℕ) (hq : 1 ≤ q)
    (N : ℕ) (Z : ℝ≥0)
    (hbind : atomicGroundStateEnergy N q Z < atomicGroundStateEnergy (N - 1) q Z) :
    (atomicGroundStateEnergy N q Z).toReal <
      (atomicGroundStateEnergy (N - 1) q Z).toReal := by
  have hN := trial_groundStateEnergy_finite q hq N 1
    (fun _ => Z) (fun _ => 0) (fun _ _ _ => Subsingleton.elim _ _)
  have hpred := trial_groundStateEnergy_finite q hq (N - 1) 1
    (fun _ => Z) (fun _ => 0) (fun _ _ _ => Subsingleton.elim _ _)
  change atomicGroundStateEnergy N q Z ≠ ⊤ ∧ atomicGroundStateEnergy N q Z ≠ ⊥ at hN
  change atomicGroundStateEnergy (N - 1) q Z ≠ ⊤ ∧
    atomicGroundStateEnergy (N - 1) q Z ≠ ⊥ at hpred
  rw [← EReal.coe_toReal hN.1 hN.2, ← EReal.coe_toReal hpred.1 hpred.2] at hbind
  exact EReal.coe_lt_coe_iff.mp hbind

/-- Every normalized energy-convergent atomic sequence is bounded in the exact form norm. -/
theorem exists_formGraphNorm_bound_of_atomic_energy_tendsto {N q : ℕ} (Z : ℝ≥0)
    (u : ℕ → FormDomain N q) (hu : ∀ n, ‖(u n : State N q)‖ = 1)
    {e : ℝ} (he : Tendsto (fun n => realEnergy (fun _ : Fin 1 => Z) (fun _ => 0)
      (fun _ _ _ => Subsingleton.elim _ _) (u n)) atTop (𝓝 e)) :
    ∃ K : ℝ, ∀ n, formGraphNorm (u n) ≤ K := by
  obtain ⟨C, hC⟩ := he.bddAbove_range
  let K := Real.sqrt (2 * (C + (2 * (N : ℝ) * (Z : ℝ) ^ 2 + 1)))
  refine ⟨K, fun n => ?_⟩
  have hshift := realEnergy_shift_ge (fun _ : Fin 1 => Z) (fun _ => 0)
    (fun _ _ _ => Subsingleton.elim _ _) (u n)
  simp only [hu n, one_pow, mul_one, Fin.sum_univ_one] at hshift
  have hCn : realEnergy (fun _ : Fin 1 => Z) (fun _ => 0)
      (fun _ _ _ => Subsingleton.elim _ _) (u n) ≤ C := hC (Set.mem_range_self n)
  have hsq : formGraphNorm (u n) ^ 2 ≤
      2 * (C + (2 * (N : ℝ) * (Z : ℝ) ^ 2 + 1)) := by linarith only [hshift, hCn]
  calc
    formGraphNorm (u n) = Real.sqrt (formGraphNorm (u n) ^ 2) :=
      (Real.sqrt_sq (formGraphNorm_nonneg _)).symm
    _ ≤ K := Real.sqrt_le_sqrt hsq

/-- A normalized state's literal particle-tail integral lies in `[0,1]`. -/
theorem particle_tail_mass_bounds {N q : ℕ} (R : ℝ) (u : State N q) (hu : ‖u‖ = 1) :
    0 ≤ (∫ x in {x : Configuration N | ∃ i : Fin N, R < ‖particlePosition x i‖},
      ‖u x‖ ^ 2) ∧
    (∫ x in {x : Configuration N | ∃ i : Fin N, R < ‖particlePosition x i‖},
      ‖u x‖ ^ 2) ≤ 1 := by
  constructor
  · exact integral_nonneg (fun _ => sq_nonneg _)
  · have h := setIntegral_le_integral (s :=
      {x : Configuration N | ∃ i : Fin N, R < ‖particlePosition x i‖})
      (integrable_state_norm_sq u) (Eventually.of_forall fun _ => sq_nonneg _)
    simpa only [integral_state_norm_sq, hu, one_pow] using h

/-- Quantitative limsup control from an elementary positive-gap estimate.  -/
theorem limsup_le_error_div_gap {t E : ℕ → ℝ} {e g err : ℝ} (hg : 0 < g)
    (ht0 : ∀ n, 0 ≤ t n) (ht1 : ∀ n, t n ≤ 1)
    (hE : Tendsto E atTop (𝓝 e))
    (hgap : ∀ n, g * t n ≤ E n - e + err) :
    0 ≤ limsup t atTop ∧ limsup t atTop ≤ err / g := by
  have hb : IsBoundedUnder (· ≤ ·) atTop t := by
    refine ⟨1, ?_⟩
    change ∀ᶠ n : ℕ in atTop, t n ≤ 1
    exact Eventually.of_forall ht1
  have hlo : IsBoundedUnder (· ≥ ·) atTop t := by
    refine ⟨0, ?_⟩
    change ∀ᶠ n : ℕ in atTop, 0 ≤ t n
    exact Eventually.of_forall ht0
  have hnonneg : 0 ≤ limsup t atTop := by
    apply le_limsup_of_le hb
    intro b h
    obtain ⟨n, hn⟩ := h.exists
    exact (ht0 n).trans hn
  have hbound : ∀ᶠ n in atTop, t n ≤ (E n - e + err) / g :=
    Eventually.of_forall fun n => (le_div_iff₀ hg).mpr (by
      simpa only [mul_comm] using hgap n)
  have hlim : Tendsto (fun n => (E n - e + err) / g) atTop (𝓝 (err / g)) := by
    simpa only [sub_self, zero_add] using
      ((hE.sub_const e).add_const err).div_const g
  refine ⟨hnonneg, ?_⟩
  rw [← hlim.limsup_eq]
  exact limsup_le_limsup hbound hlo.isCoboundedUnder_le hlim.isBoundedUnder_le

/-- The exact radial error divided by any positive gap tends to zero. -/
theorem tendsto_atomic_localization_error_div_gap (N : ℕ) (Z : ℝ≥0)
    (g : ℝ) :
    Tendsto (fun R : ℝ =>
      ((N : ℝ) * (Z : ℝ) / R + (N : ℝ) * Real.pi ^ 2 / (4 * R ^ 2)) / g)
      atTop (𝓝 0) := by
  have h1 : Tendsto (fun R : ℝ => (N : ℝ) * (Z : ℝ) / R) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have h2 : Tendsto (fun R : ℝ => (N : ℝ) * Real.pi ^ 2 / (4 * R ^ 2))
      atTop (𝓝 0) := by
    have h := ((tendsto_inv_atTop_zero : Tendsto (fun R : ℝ => R⁻¹) atTop (𝓝 0)).pow 2).const_mul
      ((N : ℝ) * Real.pi ^ 2 / 4)
    convert h using 1
    · funext R
      simp only [div_eq_mul_inv, mul_inv_rev, inv_pow]
      ring
    · simp only [zero_pow (by decide : 2 ≠ 0), mul_zero]
  simpa only [zero_add, zero_div] using (h1.add h2).div_const g

/-- Quantitative escaping-sector bounds imply particle tightness. -/
theorem atomic_particle_tight_of_localization_bounds {N q : ℕ} (Z : ℝ≥0)
    (u : ℕ → FormDomain N q) (hu : ∀ n, ‖(u n : State N q)‖ = 1)
    {e b : ℝ} (hgap : e < b)
    (hE : Tendsto (fun n => realEnergy (fun _ : Fin 1 => Z) (fun _ => 0)
      (fun _ _ _ => Subsingleton.elim _ _) (u n)) atTop (𝓝 e))
    (hloc : ∀ (R : ℝ) (hR : 0 < R) (n : ℕ),
      e * imsInsideMass hR (u n : State N q) +
        b * (1 - imsInsideMass hR (u n : State N q)) -
        (N : ℝ) * (Z : ℝ) / R - (N : ℝ) * Real.pi ^ 2 / (4 * R ^ 2) ≤
      realEnergy (fun _ : Fin 1 => Z) (fun _ => 0)
        (fun _ _ _ => Subsingleton.elim _ _) (u n)) :
    Tendsto (fun R : ℝ => limsup (fun n =>
      ∫ x in {x : Configuration N | ∃ i : Fin N, R < ‖particlePosition x i‖},
        ‖(u n : State N q) x‖ ^ 2) atTop) atTop (𝓝 0) := by
  let g := b - e
  have hg : 0 < g := sub_pos.mpr hgap
  let tail := fun (R : ℝ) (n : ℕ) =>
    ∫ x in {x : Configuration N | ∃ i : Fin N, R < ‖particlePosition x i‖},
      ‖(u n : State N q) x‖ ^ 2
  have hlim (R : ℝ) (hR : 0 < R) :
      0 ≤ limsup (tail (2 * R)) atTop ∧
      limsup (tail (2 * R)) atTop ≤
        ((N : ℝ) * (Z : ℝ) / R + (N : ℝ) * Real.pi ^ 2 / (4 * R ^ 2)) / g := by
    apply limsup_le_error_div_gap hg
      (fun n => (particle_tail_mass_bounds _ _ (hu n)).1)
      (fun n => (particle_tail_mass_bounds _ _ (hu n)).2) hE
    intro n
    have htail := particle_tail_le_one_sub_inside_mass hR (u n : State N q) (hu n)
    have hm := mul_le_mul_of_nonneg_left htail hg.le
    have h := hloc R hR n
    change g * tail (2 * R) n ≤ _ at hm
    dsimp only [g] at hm
    linarith only [hm, h]
  have hupper : ∀ᶠ R : ℝ in atTop,
      limsup (tail R) atTop ≤
        ((N : ℝ) * (Z : ℝ) / (R / 2) +
          (N : ℝ) * Real.pi ^ 2 / (4 * (R / 2) ^ 2)) / g := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
    have h := (hlim (R / 2) (by positivity)).2
    simpa only [mul_div_cancel₀ _ (by norm_num : (2 : ℝ) ≠ 0)] using h
  have hnonneg : ∀ᶠ R : ℝ in atTop, 0 ≤ limsup (tail R) atTop := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
    have h := (hlim (R / 2) (by positivity)).1
    simpa only [mul_div_cancel₀ _ (by norm_num : (2 : ℝ) ≠ 0)] using h
  exact squeeze_zero' hnonneg hupper
    ((tendsto_atomic_localization_error_div_gap N Z g).comp
      (tendsto_id.atTop_div_const (by norm_num : (0 : ℝ) < 2)))

end LiebThirring
end
