/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module
public import LiebThirring.Ionization.EscapeEnergy
public import LiebThirring.Ionization.EscapeKineticTensor
public import LiebThirring.Ionization.EscapeCoulombTensor
public import LiebThirring.Ionization.EscapeMass
/-! # The complete remote-wedge energy bound

The tensor kinetic identity, repulsive support-separation bound and attractive
monotonicity give the full atomic energy estimate with the exact `N / (3L)`
repulsive cost. All Coulomb and derivative-square integrals are finite before
passing to real values. Relabeling makes all signed terms have identical energy;
the normalized separated wedge has that same energy.
-/

public section
open MeasureTheory Set Function
open scoped ENNReal NNReal SchwartzMap
namespace LiebThirring

theorem escape_schwartz_fderiv_lintegral_toReal
    {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (h : 𝓢(V, H)) (v : V) :
    (∫⁻ p : V, (‖fderiv ℝ (fun z => h z) p v‖₊ : ℝ≥0∞) ^ 2).toReal =
      ∫ p : V, ‖fderiv ℝ (fun z => h z) p v‖ ^ 2 := by
  have he := Fourier.lintegral_norm_sq_eq_ofReal_integral (LineDeriv.lineDerivOp v h)
  simp only [SchwartzMap.lineDerivOp_apply_eq_fderiv] at he
  rw [he, ENNReal.toReal_ofReal (integral_nonneg (fun p => sq_nonneg _))]

/-- The real value of the orbital Dirichlet sum is the sum of its real integrals. -/
theorem escape_schwartz_gradient_lintegral_toReal {q : ℕ}
    (h : 𝓢(Position, EuclideanSpace ℂ (Fin q))) :
    (∑ a : Fin 3, ∫⁻ p : Position,
      (‖fderiv ℝ (fun z => h z) p (PiLp.single 2 a (1 : ℝ))‖₊ : ℝ≥0∞) ^ 2).toReal =
      ∑ a : Fin 3, ∫ p : Position, ‖fderiv ℝ (fun z => h z) p
        (PiLp.single 2 a (1 : ℝ))‖ ^ 2 := by
  rw [ENNReal.toReal_sum (fun a _ => (schwartz_lintegral_fderiv_lt_top h _).ne)]
  simp only [escape_schwartz_fderiv_lintegral_toReal]

/-- Every signed tensor summand has exactly the selected-zero summand energy. -/
theorem escapeAtomicSchwartzEnergy_term_eq_zero {N q : ℕ} (Z : ℝ≥0)
    (f : 𝓢(Configuration N, SpinAmplitudes N q))
    (h : 𝓢(Position, EuclideanSpace ℂ (Fin q)))
    (hf : HasCompactSupport (fun x => f x)) (hh : HasCompactSupport (fun x => h x))
    (i : Fin (N + 1)) :
    escapeAtomicSchwartzEnergy Z (escapeWedgeTermSchwartz f h hf hh i) =
      escapeAtomicSchwartzEnergy Z (escapeWedgeTermSchwartz f h hf hh 0) := by
  unfold escapeAtomicSchwartzEnergy
  rw [escapeWedgeTerm_kineticEnergy_eq_zero]
  change _ + (∫⁻ x, electronRepulsion x *
    (‖escapeWedgeTermAmplitudes (fun y => f y) (fun p => h p) i x‖₊ : ℝ≥0∞) ^ 2).toReal -
    (∫⁻ x, attraction (fun _ : Fin 1 => Z) (fun _ => 0) x *
    (‖escapeWedgeTermAmplitudes (fun y => f y) (fun p => h p) i x‖₊ : ℝ≥0∞) ^ 2).toReal = _
  rw [escapeWedgeTerm_lintegral_electronRepulsion_eq,
    escapeWedgeTerm_lintegral_attraction_eq]
  rfl

/-- The normalized selected-zero tensor costs only its orbital kinetic energy and `N / (3L)`. -/
theorem escapeAtomicSchwartzEnergy_term_zero_le {N q : ℕ} (Z : ℝ≥0)
    (f : 𝓢(Configuration N, SpinAmplitudes N q))
    (h : 𝓢(Position, EuclideanSpace ℂ (Fin q)))
    (hf : HasCompactSupport (fun x => f x)) (hh : HasCompactSupport (fun x => h x))
    (hnf : ‖f.toLp 2 (volume : Measure (Configuration N))‖ = 1)
    (hnh : ‖h.toLp 2 (volume : Measure Position)‖ = 1)
    {R L : ℝ} (hR : 0 ≤ R) (hL : 0 < L)
    (hRf : ∀ x ∈ tsupport (fun y => f y), ∀ j, ‖particlePosition x j‖ ≤ R)
    (hLh : ∀ y ∈ tsupport (fun p => h p), ‖y - escapeCenter R L‖ ≤ L) :
    escapeAtomicSchwartzEnergy Z (escapeWedgeTermSchwartz f h hf hh 0) ≤
      escapeAtomicSchwartzEnergy Z f +
        (∑ a : Fin 3, ∫ p, ‖fderiv ℝ (fun z => h z) p (PiLp.single 2 a (1 : ℝ))‖ ^ 2) +
        (N : ℝ) / (3 * L) := by
  let g := escapeWedgeTermSchwartz f h hf hh 0
  have hrep := escapeWedgeTerm_zero_lintegral_electronRepulsion_le_of_norm f h
    hR hL hRf hLh hnf hnh
  have hrepReal := ENNReal.toReal_mono
    (ENNReal.add_ne_top.mpr ⟨(escape_schwartz_repulsion_lt_top f).ne, ENNReal.ofReal_ne_top⟩) hrep
  rw [ENNReal.toReal_add (escape_schwartz_repulsion_lt_top f).ne ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal (div_nonneg (Nat.cast_nonneg N) (mul_pos (by norm_num) hL).le)] at hrepReal
  have hattr := escapeWedgeTerm_zero_lintegral_attraction_ge_of_norm Z f h hnh
  have hattrReal := ENNReal.toReal_mono (escape_schwartz_attraction_lt_top Z g).ne hattr
  change _ ≤ (∫⁻ x : Configuration (N + 1),
    attraction (fun _ : Fin 1 => Z) (fun _ => 0) x *
      (‖escapeWedgeTermAmplitudes (fun y => f y) (fun p => h p) 0 x‖₊ : ℝ≥0∞) ^ 2).toReal at hattrReal
  have hk : (kineticEnergy (g.toLp 2 (volume : Measure (Configuration (N + 1))))).toReal =
      (kineticEnergy (f.toLp 2 (volume : Measure (Configuration N)))).toReal +
        ∑ a : Fin 3, ∫ p, ‖fderiv ℝ (fun z => h z) p (PiLp.single 2 a (1 : ℝ))‖ ^ 2 := by
    rw [escapeWedgeTerm_zero_kineticEnergy,
      escape_schwartz_lintegral_mass_one h hnh, escape_schwartz_lintegral_mass_one f hnf,
      mul_one, one_mul, ENNReal.toReal_add (kineticEnergy_schwartz_lt_top f).ne
        (ENNReal.sum_lt_top.mpr (fun a _ => schwartz_lintegral_fderiv_lt_top h _)).ne,
      escape_schwartz_gradient_lintegral_toReal]
  unfold escapeAtomicSchwartzEnergy
  rw [show (escapeWedgeTermSchwartz f h hf hh 0) = g from rfl, hk]
  change _ + (∫⁻ x, electronRepulsion x *
    (‖escapeWedgeTermAmplitudes (fun y => f y) (fun p => h p) 0 x‖₊ : ℝ≥0∞) ^ 2).toReal -
    (∫⁻ x, attraction (fun _ : Fin 1 => Z) (fun _ => 0) x *
    (‖escapeWedgeTermAmplitudes (fun y => f y) (fun p => h p) 0 x‖₊ : ℝ≥0∞) ^ 2).toReal ≤ _
  linarith only [hrepReal, hattrReal]

/-- The normalized separated wedge has exactly its selected-zero summand energy. -/
theorem escapeAtomicSchwartzEnergy_wedge_eq_term_zero {N q : ℕ} (Z : ℝ≥0)
    (f : 𝓢(Configuration N, SpinAmplitudes N q))
    (h : 𝓢(Position, EuclideanSpace ℂ (Fin q)))
    (hf : HasCompactSupport (fun x => f x)) (hh : HasCompactSupport (fun x => h x))
    {R L : ℝ} (hR : 0 ≤ R) (hL : 0 < L)
    (hRf : ∀ x ∈ tsupport (fun y => f y), ∀ j, ‖particlePosition x j‖ ≤ R)
    (hLh : ∀ y ∈ tsupport (fun p => h p), ‖y - escapeCenter R L‖ ≤ L) :
    escapeAtomicSchwartzEnergy Z (escapeWedgeSchwartz f h hf hh) =
      escapeAtomicSchwartzEnergy Z (escapeWedgeTermSchwartz f h hf hh 0) := by
  rw [escapeAtomicSchwartzEnergy_wedge Z f h hf hh hR hL hRf hLh]
  simp only [escapeAtomicSchwartzEnergy_term_eq_zero Z f h hf hh,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    Nat.cast_add, Nat.cast_one]
  rw [← mul_assoc, inv_mul_cancel₀ (by positivity : (N : ℝ) + 1 ≠ 0), one_mul]

/-- The actual normalized remote-orbital wedge satisfies the complete escape energy bound. -/
theorem escapeAtomicSchwartzEnergy_wedge_le {N q : ℕ} (Z : ℝ≥0)
    (f : 𝓢(Configuration N, SpinAmplitudes N q))
    (h : 𝓢(Position, EuclideanSpace ℂ (Fin q)))
    (hf : HasCompactSupport (fun x => f x)) (hh : HasCompactSupport (fun x => h x))
    (hnf : ‖f.toLp 2 (volume : Measure (Configuration N))‖ = 1)
    (hnh : ‖h.toLp 2 (volume : Measure Position)‖ = 1)
    {R L : ℝ} (hR : 0 ≤ R) (hL : 0 < L)
    (hRf : ∀ x ∈ tsupport (fun y => f y), ∀ j, ‖particlePosition x j‖ ≤ R)
    (hLh : ∀ y ∈ tsupport (fun p => h p), ‖y - escapeCenter R L‖ ≤ L) :
    escapeAtomicSchwartzEnergy Z (escapeWedgeSchwartz f h hf hh) ≤
      escapeAtomicSchwartzEnergy Z f +
        (∑ a : Fin 3, ∫ p, ‖fderiv ℝ (fun z => h z) p (PiLp.single 2 a (1 : ℝ))‖ ^ 2) +
        (N : ℝ) / (3 * L) := by
  rw [escapeAtomicSchwartzEnergy_wedge_eq_term_zero Z f h hf hh hR hL hRf hLh]
  exact escapeAtomicSchwartzEnergy_term_zero_le Z f h hf hh hnf hnh hR hL hRf hLh

end LiebThirring
end
