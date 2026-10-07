/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFFunctional.CubeSamplingBounds
public import LiebThirring.TFFunctional.CubeNormalization
public import LiebThirring.TFFunctional.CompactApproximation

/-! # Positive finite cube approximation in both density norms

Compact approximation and literal lattice sampling give simultaneous L1 and
L5/3 convergence. Rescaling cell masses enforces the original exact mass.
direct proof.
-/

public section

open MeasureTheory Filter
open scoped NNReal ENNReal Topology

namespace LiebThirring.TFFunctional

local instance : Fact (1 ≤ (5 : ℝ≥0∞) / 3) := ⟨by
  apply (ENNReal.toReal_le_toReal (by simp)
    (ENNReal.div_ne_top (by norm_num) (by norm_num))).mp
  norm_num [ENNReal.toReal_div]⟩

theorem exists_cubeDensity_joint_approximation (ρ : TFDensity) (ε : ℝ) (hε : 0 < ε) :
    ∃ (B : ℕ) (g : TFUpper.CubeMesh B),
      eLpNorm (g.stepFunction - (ρ.val : Position → ℝ)) ((5 : ℝ≥0∞) / 3) volume ≤ ENNReal.ofReal ε ∧
      eLpNorm (g.stepFunction - (ρ.val : Position → ℝ)) 1 volume ≤ ENNReal.ofReal ε := by
  obtain ⟨f, hf, hc, hs, hp, h1⟩ :=
    exists_compact_nonneg_joint_approximation ρ (ε / 2) (half_pos hε)
  obtain ⟨B, g, hgp, hg1⟩ :=
    exists_cubeMesh_eLpNorm_approximation f hf hc hs (ε / 2) (half_pos hε)
  have heq : (g.stepFunction - (ρ.val : Position → ℝ)) =
      (g.stepFunction - f) + (f - (ρ.val : Position → ℝ)) := by
    ext x
    simp only [Pi.sub_apply, Pi.add_apply]
    ring
  have hsum : ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) = ENNReal.ofReal ε := by
    rw [← ENNReal.ofReal_add (half_pos hε).le (half_pos hε).le]
    congr 1
    ring
  refine ⟨B, g, ?_, ?_⟩
  · rw [heq]
    exact (eLpNorm_add_le (Fact.out : 1 ≤ (5 : ℝ≥0∞) / 3)).trans
      ((add_le_add hgp hp).trans_eq hsum)
  · rw [heq]
    exact (eLpNorm_add_le (le_refl (1 : ℝ≥0∞))).trans
      ((add_le_add hg1 h1).trans_eq hsum)

theorem exists_cubeDensity_joint_sequence (ρ : TFDensity) :
    ∃ (B : ℕ → ℕ) (g : (j : ℕ) → TFUpper.CubeMesh (B j)),
      Tendsto (fun j => (tfCubeDensity (g j)).val) atTop (𝓝 ρ.val) ∧
      Tendsto (fun j => ∫ x : Position, |(tfCubeDensity (g j)).val x - ρ.val x|)
        atTop (𝓝 (0 : ℝ)) := by
  classical
  have hex (j : ℕ) := exists_cubeDensity_joint_approximation ρ
    (1 / ((j : ℝ) + 1)) (by positivity)
  choose B g hp h1 using hex
  have herr : Tendsto (fun j : ℕ => ENNReal.ofReal (1 / ((j : ℝ) + 1)))
      atTop (𝓝 (0 : ℝ≥0∞)) := by
    simpa only [ENNReal.ofReal_zero] using
      ENNReal.tendsto_ofReal (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have heq (j : ℕ) (p : ℝ≥0∞) :
      eLpNorm (((tfCubeDensity (g j)).val : Position → ℝ) - (ρ.val : Position → ℝ)) p volume =
        eLpNorm ((g j).stepFunction - (ρ.val : Position → ℝ)) p volume := by
    have hg : ((tfCubeDensity (g j)).val : Position → ℝ) =ᵐ[volume]
        (g j).stepFunction := cubeMesh_represents_tfCubeDensity (g j)
    exact eLpNorm_congr_ae (hg.sub Filter.EventuallyEq.rfl)
  have hpn : Tendsto (fun j => eLpNorm (((tfCubeDensity (g j)).val : Position → ℝ) - (ρ.val : Position → ℝ))
      ((5 : ℝ≥0∞) / 3) volume) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds herr
      (fun _ => bot_le) (fun j => (heq j _).le.trans (hp j))
  have h1n : Tendsto (fun j => eLpNorm (((tfCubeDensity (g j)).val : Position → ℝ) - (ρ.val : Position → ℝ))
      1 volume) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds herr
      (fun _ => bot_le) (fun j => (heq j _).le.trans (h1 j))
  refine ⟨B, g, (Lp.tendsto_Lp_iff_tendsto_eLpNorm' _ _).mpr hpn, ?_⟩
  have hint (j : ℕ) :
      (∫ x : Position, |(tfCubeDensity (g j)).val x - ρ.val x|) =
        (eLpNorm (((tfCubeDensity (g j)).val : Position → ℝ) - (ρ.val : Position → ℝ)) 1 volume).toReal := by
    rw [eLpNorm_one_eq_lintegral_enorm
      ((Lp.aestronglyMeasurable (tfCubeDensity (g j)).val).sub
        (Lp.aestronglyMeasurable ρ.val))]
    simpa only [Real.norm_eq_abs, Pi.sub_apply] using
      integral_norm_eq_lintegral_enorm
        ((Lp.aestronglyMeasurable (tfCubeDensity (g j)).val).sub
          (Lp.aestronglyMeasurable ρ.val))
  simp_rw [hint]
  simpa only [Function.comp_def, ENNReal.toReal_zero] using
    (ENNReal.continuousAt_toReal ENNReal.zero_ne_top).tendsto.comp h1n

/-- Every positive exact-mass density is the joint density limit of finite
nonnegative regular cube step densities with that same exact mass. -/
theorem exists_same_mass_cubeDensity_sequence (ρ : TFDensity)
    (ν : ℝ≥0) (hν : 0 < ν) (hmass : tfMass ρ = (ν : ℝ)) :
    ∃ (B : ℕ → ℕ) (g : (j : ℕ) → TFUpper.CubeMesh (B j)) (σ : ℕ → TFDensity),
      (∀ j, (g j).represents (σ j)) ∧ (∀ j, tfMass (σ j) = (ν : ℝ)) ∧
      Tendsto (fun j => (σ j).val) atTop (𝓝 ρ.val) ∧
      Tendsto (fun j => ∫ x : Position, |(σ j).val x - ρ.val x|) atTop (𝓝 (0 : ℝ)) := by
  obtain ⟨B, g, hp, h1⟩ := exists_cubeDensity_joint_sequence ρ
  have hm := tendsto_tfMass_of_tendsto_L1 (fun j => tfCubeDensity (g j)) ρ h1
  rw [hmass] at hm
  have hνr : (0 : ℝ) < ν := hν
  obtain ⟨J, hJ⟩ := eventually_atTop.mp (hm.eventually (lt_mem_nhds hνr))
  let b (j : ℕ) : ℝ≥0 := ⟨(ν : ℝ) / tfMass (tfCubeDensity (g (j + J))),
    div_nonneg ν.property (tfMass_nonneg _)⟩
  let σ (j : ℕ) := tfDensitySMul (b j) (tfCubeDensity (g (j + J)))
  have hb : Tendsto (fun j => (b j : ℝ)) atTop (𝓝 1) := by
    have h := (tendsto_const_nhds : Tendsto (fun _ : ℕ => (ν : ℝ))
      atTop (𝓝 (ν : ℝ))).div (hm.comp (tendsto_add_atTop_nat J)) hνr.ne'
    change Tendsto (fun j => (ν : ℝ) / tfMass (tfCubeDensity (g (j + J)))) atTop (𝓝 1)
    simpa only [Function.comp_def, Pi.div_def, div_self hνr.ne'] using h
  have hconv := tendsto_tfDensitySMul_joint (fun j => tfCubeDensity (g (j + J))) ρ b hb
    (hp.comp (tendsto_add_atTop_nat J)) (h1.comp (tendsto_add_atTop_nat J))
  refine ⟨fun j => B (j + J), fun j => normalizedCubeMesh ν (g (j + J)), σ,
    ?_, ?_, hconv.1, hconv.2⟩
  · intro j
    exact normalizedCubeMesh_represents ν (g (j + J))
  · intro j
    exact tfMass_normalizedCubeDensity ν (g (j + J))
      (hJ (j + J) (Nat.le_add_left J j))

end LiebThirring.TFFunctional

end
