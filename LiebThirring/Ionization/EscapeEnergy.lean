/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module
public import LiebThirring.Ionization.EscapeNorm
public import LiebThirring.Variational.FormFinite
public import LiebThirring.Variational.RealEnergy
import LiebThirring.Variational.TrialVacuum
import LiebThirring.Variational.TrialScaling
/-! # Atomic quadratic energy of Schwartz escape trials

The full-domain Schwartz form uses the literal Fourier kinetic term and the
finite Coulomb expectations. Separated closed supports give exact energy
additivity, and the prescribed `1 / sqrt(n)` coefficient gives the energy average.
-/

public section
open MeasureTheory Set Function
open scoped ENNReal NNReal SchwartzMap
namespace LiebThirring
/-- The atomic quadratic energy of a Schwartz function, without an antisymmetry requirement. -/
@[expose] noncomputable def escapeAtomicSchwartzEnergy {N q : ℕ} (Z : ℝ≥0)
    (f : 𝓢(Configuration N, SpinAmplitudes N q)) : ℝ :=
  (kineticEnergy (f.toLp 2 (volume : Measure (Configuration N)))).toReal +
    (∫⁻ x : Configuration N, electronRepulsion x * (‖f x‖₊ : ℝ≥0∞) ^ 2).toReal -
    (∫⁻ x : Configuration N,
      attraction (fun _ : Fin 1 => Z) (fun _ => 0) x * (‖f x‖₊ : ℝ≥0∞) ^ 2).toReal

/-- Pointwise Schwartz representatives and their L² states have identical weighted expectations. -/
theorem escape_schwartz_lintegral_weight_toLp {N q : ℕ}
    (p : Configuration N → ℝ≥0∞) (f : 𝓢(Configuration N, SpinAmplitudes N q)) :
    (∫⁻ x, p x * (‖f x‖₊ : ℝ≥0∞) ^ 2) =
      ∫⁻ x, p x * (‖(f.toLp 2 (volume : Measure (Configuration N))) x‖₊ : ℝ≥0∞) ^ 2 := by
  apply lintegral_congr_ae
  filter_upwards [f.coeFn_toLp 2 (volume : Measure (Configuration N))] with x hx
  rw [hx]

/-- The atomic attractive expectation is finite on every Schwartz function. -/
theorem escape_schwartz_attraction_lt_top {N q : ℕ} (Z : ℝ≥0)
    (f : 𝓢(Configuration N, SpinAmplitudes N q)) :
    (∫⁻ x : Configuration N,
      attraction (fun _ : Fin 1 => Z) (fun _ => 0) x * (‖f x‖₊ : ℝ≥0∞) ^ 2) < ⊤ := by
  rw [escape_schwartz_lintegral_weight_toLp]
  exact lintegral_attraction_lt_top _ _ _ (kineticEnergy_schwartz_lt_top f)

/-- The electron repulsive expectation is finite on every Schwartz function. -/
theorem escape_schwartz_repulsion_lt_top {N q : ℕ}
    (f : 𝓢(Configuration N, SpinAmplitudes N q)) :
    (∫⁻ x : Configuration N, electronRepulsion x * (‖f x‖₊ : ℝ≥0∞) ^ 2) < ⊤ := by
  rw [escape_schwartz_lintegral_weight_toLp]
  exact lintegral_electronRepulsion_lt_top _ (kineticEnergy_schwartz_lt_top f)

/-- The literal Schwartz energy agrees with the form-domain energy on its L² state. -/
theorem escapeAtomicSchwartzEnergy_eq_realEnergy {N q : ℕ} (Z : ℝ≥0)
    (f : 𝓢(Configuration N, SpinAmplitudes N q)) (u : FormDomain N q)
    (hu : (u : State N q) = f.toLp 2 (volume : Measure (Configuration N))) :
    escapeAtomicSchwartzEnergy Z f =
      realEnergy (fun _ : Fin 1 => Z) (fun _ => 0)
        (fun _ _ _ => Subsingleton.elim _ _) u := by
  unfold escapeAtomicSchwartzEnergy realEnergy
  rw [nuclearRepulsion_single, hu]
  simp only [ENNReal.toReal_zero, zero_mul, add_zero]
  rw [escape_schwartz_lintegral_weight_toLp, escape_schwartz_lintegral_weight_toLp]

/-- Every pointwise weighted Schwartz expectation is homogeneous in a real scalar. -/
theorem escape_schwartz_lintegral_weight_smul {N q : ℕ}
    (p : Configuration N → ℝ≥0∞) (c : ℝ) (f : 𝓢(Configuration N, SpinAmplitudes N q)) :
    (∫⁻ x, p x * (‖(c • f) x‖₊ : ℝ≥0∞) ^ 2) =
      (‖c‖₊ : ℝ≥0∞) ^ 2 * ∫⁻ x, p x * (‖f x‖₊ : ℝ≥0∞) ^ 2 := by
  calc
    _ = ∫⁻ x, (‖c‖₊ : ℝ≥0∞) ^ 2 * (p x * (‖f x‖₊ : ℝ≥0∞) ^ 2) := by
      apply lintegral_congr
      intro x
      simp only [smul_apply, nnnorm_smul, ENNReal.coe_mul, mul_pow]
      ring
    _ = _ := lintegral_const_mul' _ _ (ENNReal.pow_ne_top ENNReal.coe_ne_top)

/-- The Fourier kinetic form of a Schwartz trial scales by squared scalar norm. -/
theorem escape_schwartz_kinetic_smul {N q : ℕ} (c : ℝ)
    (f : 𝓢(Configuration N, SpinAmplitudes N q)) :
    kineticEnergy ((c • f).toLp 2 (volume : Measure (Configuration N))) =
      (‖c‖₊ : ℝ≥0∞) ^ 2 * kineticEnergy (f.toLp 2 (volume : Measure (Configuration N))) := by
  change kineticEnergy (SchwartzMap.toLpCLM ℝ (SpinAmplitudes N q) 2
    (volume : Measure (Configuration N)) (c • f)) = _
  rw [map_smul]
  change kineticEnergy ((c : ℂ) • f.toLp 2 (volume : Measure (Configuration N))) = _
  rw [trial_kineticEnergy_smul]
  have hc : ‖(c : ℂ)‖₊ = ‖c‖₊ := by
    apply NNReal.coe_injective
    exact Complex.norm_real c
  rw [hc]

/-- Real scalar multiplication scales the atomic Schwartz energy by `c²`. -/
theorem escapeAtomicSchwartzEnergy_smul {N q : ℕ} (Z : ℝ≥0) (c : ℝ)
    (f : 𝓢(Configuration N, SpinAmplitudes N q)) :
    escapeAtomicSchwartzEnergy Z (c • f) = c ^ 2 * escapeAtomicSchwartzEnergy Z f := by
  unfold escapeAtomicSchwartzEnergy
  rw [escape_schwartz_kinetic_smul, escape_schwartz_lintegral_weight_smul,
    escape_schwartz_lintegral_weight_smul]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.coe_toReal,
    coe_nnnorm, Real.norm_eq_abs, sq_abs]
  ring

/-- The complete atomic Schwartz energy is additive on spatially separated summands. -/
theorem escapeAtomicSchwartzEnergy_sum {ι N q : ℕ} (Z : ℝ≥0)
    (f : Fin ι → 𝓢(Configuration N, SpinAmplitudes N q))
    (hf : Pairwise (Disjoint on fun i => tsupport (fun x => f i x))) :
    escapeAtomicSchwartzEnergy Z (∑ i, f i) = ∑ i, escapeAtomicSchwartzEnergy Z (f i) := by
  unfold escapeAtomicSchwartzEnergy
  rw [escape_kineticEnergy_sum f hf,
    escape_schwartz_lintegral_weight_sum electronRepulsion Assembly.measurable_electronRepulsion f hf,
    escape_schwartz_lintegral_weight_sum _ (measurable_attraction _ _) f hf,
    ENNReal.toReal_sum (fun i _ => (kineticEnergy_schwartz_lt_top (f i)).ne),
    ENNReal.toReal_sum (fun i _ => (escape_schwartz_repulsion_lt_top (f i)).ne),
    ENNReal.toReal_sum (fun i _ => (escape_schwartz_attraction_lt_top Z (f i)).ne)]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]

/-- The `1 / sqrt(n)` normalized separated sum has exactly the average energy. -/
theorem escapeAtomicSchwartzEnergy_normalized_sum {ι N q : ℕ} (Z : ℝ≥0)
    (f : Fin ι → 𝓢(Configuration N, SpinAmplitudes N q))
    (hf : Pairwise (Disjoint on fun i => tsupport (fun x => f i x))) :
    escapeAtomicSchwartzEnergy Z ((Real.sqrt ι)⁻¹ • ∑ i, f i) =
      (ι : ℝ)⁻¹ * ∑ i, escapeAtomicSchwartzEnergy Z (f i) := by
  rw [escapeAtomicSchwartzEnergy_smul, escapeAtomicSchwartzEnergy_sum Z f hf,
    inv_pow, Real.sq_sqrt (Nat.cast_nonneg ι)]


/-- The actual remote-orbital wedge has exactly the average energy of its separated terms. -/
theorem escapeAtomicSchwartzEnergy_wedge {N q : ℕ} (Z : ℝ≥0)
    (f : 𝓢(Configuration N, SpinAmplitudes N q))
    (h : 𝓢(Position, EuclideanSpace ℂ (Fin q)))
    (hf : HasCompactSupport (fun x => f x)) (hh : HasCompactSupport (fun x => h x))
    {R L : ℝ} (hR : 0 ≤ R) (hL : 0 < L)
    (hRf : ∀ x ∈ tsupport (fun y => f y), ∀ j, ‖particlePosition x j‖ ≤ R)
    (hLh : ∀ y ∈ tsupport (fun p => h p), ‖y - escapeCenter R L‖ ≤ L) :
    escapeAtomicSchwartzEnergy Z (escapeWedgeSchwartz f h hf hh) =
      ((N + 1 : ℕ) : ℝ)⁻¹ *
        ∑ i, escapeAtomicSchwartzEnergy Z (escapeWedgeTermSchwartz f h hf hh i) := by
  rw [escapeWedgeSchwartz_eq_sum]
  have hd : Pairwise (Disjoint on fun i =>
      tsupport (fun x => escapeWedgeTermSchwartz f h hf hh i x)) :=
    escape_disjoint_wedgeTermAmplitudes (fun y => f y) (fun p => h p) hR hL hRf hLh
  simpa only [Nat.cast_add, Nat.cast_one] using
    escapeAtomicSchwartzEnergy_normalized_sum Z (escapeWedgeTermSchwartz f h hf hh) hd

end LiebThirring
end
