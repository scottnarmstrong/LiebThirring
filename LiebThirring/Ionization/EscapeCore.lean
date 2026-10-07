/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Ionization.EscapeCoreGraph
public import LiebThirring.Ionization.EscapeVariational
public import LiebThirring.Sobolev.FormDensityCore

/-! # Normalized compact smooth near-minimizers from proved form density -/

public section

open MeasureTheory WithLp
open scoped ENNReal NNReal SchwartzMap

namespace LiebThirring

/-- Almost-everywhere fermionic covariance of a Schwartz state holds everywhere. -/
theorem escapeSchwartz_pointwise_of_antisymmetric {N q : ℕ}
    (f : 𝓢(Configuration N, SpinAmplitudes N q))
    (hf : antisymmetric (f.toLp 2 (volume : Measure (Configuration N))))
    (σ : Equiv.Perm (Fin N)) (x : Configuration N) (s : SpinLabels N q) :
    f (permutePositions σ x) (permuteSpins σ s) = escapePermutationSign σ * f x s := by
  have he : (fun y => f (permutePositions σ y) (permuteSpins σ s)) =ᵐ[volume]
      (fun y => escapePermutationSign σ * f y s) := by
    filter_upwards [hf σ, f.coeFn_toLp 2 (volume : Measure (Configuration N)),
      (measurePreserving_permutePositions σ).quasiMeasurePreserving.ae
        (f.coeFn_toLp 2 (volume : Measure (Configuration N)))] with y ha hy hσy
    rw [← hy, ← hσy]
    exact ha s
  have hl : Continuous (fun y => f (permutePositions σ y) (permuteSpins σ s)) :=
    ((contDiff_piLp 2).mp (f.smooth ⊤) (permuteSpins σ s)).continuous.comp
      (permutationLinearIsometryEquiv σ).continuous
  have hr : Continuous (fun y => escapePermutationSign σ * f y s) :=
    continuous_const.mul ((contDiff_piLp 2).mp (f.smooth ⊤) s).continuous
  exact congrFun (Measure.eq_of_ae_eq he hl hr) x

/-- Quantitative compact smooth density in the literal form graph norm. -/
theorem escape_exists_compact_form_approximation {N q : ℕ} (u : FormDomain N q)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (f : 𝓢(Configuration N, SpinAmplitudes N q))
      (hf : ∀ (σ : Equiv.Perm (Fin N)) (x : Configuration N) (s : SpinLabels N q),
        f (permutePositions σ x) (permuteSpins σ s) = escapePermutationSign σ * f x s),
      HasCompactSupport (fun x => f x) ∧
      formGraphNorm (escapeSchwartzForm f hf - u) ≤ (1 + 2 * Real.pi) * ε := by
  obtain ⟨f, hc, ha, hm, hT⟩ := Sobolev.exists_antisymmetric_compact_smooth_form_approximation
    (u : State N q) u.property.2 u.property.1 hε
  let hf := escapeSchwartz_pointwise_of_antisymmetric f ha
  let v := escapeSchwartzForm f hf
  refine ⟨f, hf, hc, ?_⟩
  rw [escape_formGraphNorm_sub_comm]
  have hTreal := ENNReal.toReal_mono (ENNReal.ofReal_ne_top) hT
  rw [ENNReal.toReal_ofReal (sq_nonneg _)] at hTreal
  have hmsq := pow_le_pow_left₀ (norm_nonneg _) hm 2
  have hG := formGraphNorm_sq (u - v)
  change formGraphNorm (u - v) ≤ (1 + 2 * Real.pi) * ε
  change formGraphNorm (u - v) ^ 2 =
    ‖(u : State N q) - f.toLp 2 volume‖ ^ 2 +
      (kineticEnergy ((u : State N q) - f.toLp 2 volume)).toReal at hG
  apply (sq_le_sq₀ (formGraphNorm_nonneg _) (mul_nonneg (by positivity) hε.le)).mp
  nlinarith only [hG, hmsq, hTreal, Real.pi_pos, sq_nonneg ε]

/-- The compact smooth antisymmetric form core can be normalized while
remaining arbitrarily close in the literal graph norm. -/
theorem escape_exists_normalized_compact_form_approximation {N q : ℕ}
    (u : FormDomain N q) (hu : ‖(u : State N q)‖ = 1) (δ : ℝ) (hδ : 0 < δ) :
    ∃ (f : 𝓢(Configuration N, SpinAmplitudes N q))
      (hf : ∀ (σ : Equiv.Perm (Fin N)) (x : Configuration N) (s : SpinLabels N q),
        f (permutePositions σ x) (permuteSpins σ s) = escapePermutationSign σ * f x s),
      HasCompactSupport (fun x => f x) ∧ ‖f.toLp 2 volume‖ = 1 ∧
      formGraphNorm (escapeSchwartzForm f hf - u) < δ := by
  let C : ℝ := 1 + 2 * Real.pi
  have hC : 0 < C := by dsimp only [C]; positivity
  have hA : 0 < 1 + formGraphNorm u := add_pos_of_pos_of_nonneg (by norm_num) (formGraphNorm_nonneg _)
  let η : ℝ := min (1 / 4) (δ / (8 * (1 + formGraphNorm u)))
  have hη : 0 < η := lt_min (by norm_num) (div_pos hδ (mul_pos (by norm_num) hA))
  obtain ⟨f, hf, hc, hgraph⟩ := escape_exists_compact_form_approximation u (η / C) (div_pos hη hC)
  let v := escapeSchwartzForm f hf
  have hdη : formGraphNorm (v - u) ≤ η := by
    have he : C * (η / C) = η := by field_simp
    change formGraphNorm (v - u) ≤ C * (η / C) at hgraph
    exact hgraph.trans_eq he
  have hdhalf : formGraphNorm (v - u) ≤ 1 / 2 :=
    hdη.trans ((min_le_left _ _).trans (by norm_num : (1 / 4 : ℝ) ≤ 1 / 2))
  have hnormdiff : |‖(v : State N q)‖ - 1| ≤ formGraphNorm (v - u) := by
    rw [← hu]
    exact (abs_norm_sub_norm_le (v : State N q) (u : State N q)).trans
      (norm_state_le_formGraphNorm (v - u))
  have hva : 0 < ‖(v : State N q)‖ := by
    have hl := (abs_le.mp hnormdiff).1
    linarith only [hl, hdhalf]
  let c : ℂ := ((‖(v : State N q)‖⁻¹ : ℝ) : ℂ)
  let g : 𝓢(Configuration N, SpinAmplitudes N q) := c • f
  have hg : ∀ (σ : Equiv.Perm (Fin N)) (x : Configuration N) (s : SpinLabels N q),
      g (permutePositions σ x) (permuteSpins σ s) = escapePermutationSign σ * g x s := by
    intro σ x s
    change c * f (permutePositions σ x) (permuteSpins σ s) = escapePermutationSign σ * (c * f x s)
    rw [hf]
    ring
  have hgp : g.toLp 2 volume = c • (v : State N q) := by
    exact (SchwartzMap.toLpCLM ℂ (SpinAmplitudes N q) 2 volume).map_smul c f
  have hgv : escapeSchwartzForm g hg = c • v := by
    apply Subtype.ext
    exact hgp
  refine ⟨g, hg, ?_, ?_, ?_⟩
  · change HasCompactSupport (fun x => c • f x)
    exact HasCompactSupport.smul_left (f := fun _ : Configuration N => c) hc
  · rw [hgp, norm_smul]
    change ‖((‖(v : State N q)‖⁻¹ : ℝ) : ℂ)‖ * ‖(v : State N q)‖ = 1
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hva.le)]
    exact inv_mul_cancel₀ hva.ne'
  · rw [hgv]
    calc
      _ ≤ 4 * formGraphNorm (v - u) * (1 + formGraphNorm u) :=
        escape_formGraphNorm_normalize_le u v hu hdhalf
      _ ≤ 4 * η * (1 + formGraphNorm u) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hdη (by norm_num)) hA.le
      _ ≤ δ / 2 := by
        have hb : η ≤ δ / (8 * (1 + formGraphNorm u)) := min_le_right _ _
        have hb' := (le_div_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 8) hA)).mp hb
        nlinarith only [hb']
      _ < δ := half_lt_self hδ

/-- Unconditional normalized compact smooth atomic near-minimizers. -/
theorem escape_exists_normalized_compact_near_minimizer (q : ℕ) (hq : 1 ≤ q) (N : ℕ) (Z : ℝ≥0)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (f : 𝓢(Configuration N, SpinAmplitudes N q))
      (hf : ∀ (σ : Equiv.Perm (Fin N)) (x : Configuration N) (s : SpinLabels N q),
        f (permutePositions σ x) (permuteSpins σ s) = escapePermutationSign σ * f x s),
      HasCompactSupport (fun x => f x) ∧ ‖f.toLp 2 volume‖ = 1 ∧
      realEnergy (fun _ : Fin 1 => Z) (fun _ => 0)
        (fun _ _ _ => Subsingleton.elim _ _) (escapeSchwartzForm f hf) <
          (atomicGroundStateEnergy N q Z).toReal + ε := by
  exact escape_exists_compact_near_minimizer_of_normalized_core_dense q hq N Z
    escape_exists_normalized_compact_form_approximation ε hε

end LiebThirring

end
