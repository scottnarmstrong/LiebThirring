/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module
public import LiebThirring.Ionization.EscapeGeometry
public import LiebThirring.Ionization.EscapeOrbital
/-! # Spin-valued compact remote orbitals

Embedding a scalar orbital in a fixed unit spin basis vector preserves pointwise
mass and directional kinetic energy. The translated dilated family is normalized,
compactly supported in the prescribed remote ball, and has exact `L⁻²` kinetic scale.
-/

public section
open MeasureTheory Set Function
open scoped ENNReal NNReal ContDiff SchwartzMap
namespace LiebThirring
/-- Embed a scalar Schwartz orbital into the spin basis vector indexed by `t`. -/
@[expose] noncomputable def escapeSpinOrbital {q : ℕ} (h : 𝓢(Position, ℂ)) (t : Fin q) :
    𝓢(Position, EuclideanSpace ℂ (Fin q)) :=
  h.postcompCLM (ContinuousLinearMap.toSpanSingleton ℂ ((PiLp.single 2 t (1 : ℂ) : EuclideanSpace ℂ (Fin q))))

/-- The spin embedding is multiplication by a fixed unit basis vector. -/
@[simp] theorem escapeSpinOrbital_apply {q : ℕ} (h : 𝓢(Position, ℂ)) (t : Fin q) (x : Position) :
    escapeSpinOrbital h t x = h x • (PiLp.single 2 t (1 : ℂ) : EuclideanSpace ℂ (Fin q)) := rfl

/-- The spin embedding preserves pointwise norm. -/
@[simp] theorem norm_escapeSpinOrbital {q : ℕ} (h : 𝓢(Position, ℂ)) (t : Fin q) (x : Position) :
    ‖escapeSpinOrbital h t x‖ = ‖h x‖ := by
  rw [escapeSpinOrbital_apply, norm_smul, PiLp.norm_single, norm_one, mul_one]

/-- The spin embedding preserves the L² norm. -/
theorem norm_toLp_escapeSpinOrbital {q : ℕ} (h : 𝓢(Position, ℂ)) (t : Fin q) :
    ‖(escapeSpinOrbital h t).toLp 2 (volume : Measure Position)‖ =
      ‖h.toLp 2 (volume : Measure Position)‖ := by
  rw [SchwartzMap.norm_toLp' (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      (by norm_num : (2 : ℝ≥0∞) ≠ ⊤),
    SchwartzMap.norm_toLp' (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)]
  simp only [norm_escapeSpinOrbital]

/-- The spin embedding has closed support contained in the scalar support. -/
theorem tsupport_escapeSpinOrbital_subset {q : ℕ} (h : 𝓢(Position, ℂ)) (t : Fin q) :
    tsupport (fun x => escapeSpinOrbital h t x) ⊆ tsupport (fun x => h x) :=
  tsupport_smul_subset_left (fun x => h x) (fun _ => (PiLp.single 2 t (1 : ℂ) : EuclideanSpace ℂ (Fin q)))

/-- Compact scalar orbitals give compact spin-valued orbitals. -/
theorem hasCompactSupport_escapeSpinOrbital {q : ℕ} (h : 𝓢(Position, ℂ))
    (hh : HasCompactSupport (fun x => h x)) (t : Fin q) :
    HasCompactSupport (fun x => escapeSpinOrbital h t x) := hh.smul_right

/-- Differentiation commutes with the fixed spin embedding. -/
theorem fderiv_escapeSpinOrbital {q : ℕ} (h : 𝓢(Position, ℂ)) (t : Fin q) (x v : Position) :
    fderiv ℝ (fun y => escapeSpinOrbital h t y) x v =
      fderiv ℝ (fun y => h y) x v • (PiLp.single 2 t (1 : ℂ) : EuclideanSpace ℂ (Fin q)) := by
  change fderiv ℝ (fun y => h y • (PiLp.single 2 t (1 : ℂ) : EuclideanSpace ℂ (Fin q))) x v = _
  rw [fderiv_smul_const ((h.smooth ⊤).differentiable (by simp)).differentiableAt]
  rfl

/-- The spin embedding preserves the norm of every directional derivative. -/
@[simp] theorem norm_fderiv_escapeSpinOrbital {q : ℕ}
    (h : 𝓢(Position, ℂ)) (t : Fin q) (x v : Position) :
    ‖fderiv ℝ (fun y => escapeSpinOrbital h t y) x v‖ =
      ‖fderiv ℝ (fun y => h y) x v‖ := by
  rw [fderiv_escapeSpinOrbital, norm_smul, PiLp.norm_single, norm_one, mul_one]

/-- The spin embedding preserves every directional kinetic quadratic energy. -/
theorem integral_norm_sq_fderiv_escapeSpinOrbital {q : ℕ}
    (h : 𝓢(Position, ℂ)) (t : Fin q) (v : Position) :
    (∫ x, ‖fderiv ℝ (fun y => escapeSpinOrbital h t y) x v‖ ^ 2) =
      ∫ x, ‖fderiv ℝ (fun y => h y) x v‖ ^ 2 := by
  simp only [norm_fderiv_escapeSpinOrbital]

/-- The normalized remote spin orbital with center prescribed by the escape geometry. -/
@[expose] noncomputable def escapeRemoteSpinOrbital {q : ℕ} (h : 𝓢(Position, ℂ))
    (hh : ∀ x, 1 < ‖x‖ → h x = 0) (t : Fin q) (R L : ℝ) (hL : 0 < L) :
    𝓢(Position, EuclideanSpace ℂ (Fin q)) :=
  escapeSpinOrbital (escapeOrbitalSchwartz h hh L hL (escapeCenter R L)) t

/-- A normalized scalar base orbital gives a normalized remote spin state. -/
theorem norm_toLp_escapeRemoteSpinOrbital {q : ℕ} (h : 𝓢(Position, ℂ))
    (hh : ∀ x, 1 < ‖x‖ → h x = 0) (hn : (∫ x, ‖h x‖ ^ 2) = 1)
    (t : Fin q) (R L : ℝ) (hL : 0 < L) :
    ‖(escapeRemoteSpinOrbital h hh t R L hL).toLp 2 (volume : Measure Position)‖ = 1 := by
  unfold escapeRemoteSpinOrbital
  rw [norm_toLp_escapeSpinOrbital]
  exact norm_toLp_escapeOrbitalSchwartz h hh hn L hL (escapeCenter R L)

/-- The remote spin orbital is supported in the prescribed remote ball. -/
theorem tsupport_escapeRemoteSpinOrbital_subset {q : ℕ} (h : 𝓢(Position, ℂ))
    (hh : ∀ x, 1 < ‖x‖ → h x = 0) (t : Fin q) (R L : ℝ) (hL : 0 < L) :
    tsupport (fun x => escapeRemoteSpinOrbital h hh t R L hL x) ⊆
      Metric.closedBall (escapeCenter R L) L :=
  (tsupport_escapeSpinOrbital_subset _ t).trans
    (tsupport_escapeOrbital_subset (fun x => h x) hh L hL (escapeCenter R L))

/-- The remote spin orbital has compact closed support. -/
theorem hasCompactSupport_escapeRemoteSpinOrbital {q : ℕ} (h : 𝓢(Position, ℂ))
    (hh : ∀ x, 1 < ‖x‖ → h x = 0) (t : Fin q) (R L : ℝ) (hL : 0 < L) :
    HasCompactSupport (fun x => escapeRemoteSpinOrbital h hh t R L hL x) :=
  hasCompactSupport_escapeSpinOrbital (escapeOrbitalSchwartz h hh L hL (escapeCenter R L))
    (hasCompactSupport_escapeOrbital (fun x => h x) hh L hL (escapeCenter R L)) t

/-- The remote spin directional kinetic energy has exact `L⁻²` scaling. -/
theorem integral_norm_sq_fderiv_escapeRemoteSpinOrbital {q : ℕ} (h : 𝓢(Position, ℂ))
    (hh : ∀ x, 1 < ‖x‖ → h x = 0) (t : Fin q) (R L : ℝ) (hL : 0 < L) (v : Position) :
    (∫ x, ‖fderiv ℝ (fun y => escapeRemoteSpinOrbital h hh t R L hL y) x v‖ ^ 2) =
      L⁻¹ ^ 2 * ∫ x, ‖fderiv ℝ (fun y => h y) x v‖ ^ 2 := by
  unfold escapeRemoteSpinOrbital
  rw [integral_norm_sq_fderiv_escapeSpinOrbital]
  exact integral_norm_sq_fderiv_escapeOrbital (fun x => h x) (h.smooth ⊤) L hL
    (escapeCenter R L) v

/-- The remote spin gradient quadratic energy has exact `L⁻²` scaling. -/
theorem sum_integral_norm_sq_fderiv_escapeRemoteSpinOrbital {q : ℕ} (h : 𝓢(Position, ℂ))
    (hh : ∀ x, 1 < ‖x‖ → h x = 0) (t : Fin q) (R L : ℝ) (hL : 0 < L) :
    (∑ j : Fin 3, ∫ x, ‖fderiv ℝ (fun y => escapeRemoteSpinOrbital h hh t R L hL y) x
      (PiLp.single 2 j (1 : ℝ))‖ ^ 2) =
      L⁻¹ ^ 2 * ∑ j : Fin 3, ∫ x, ‖fderiv ℝ (fun y => h y) x
        (PiLp.single 2 j (1 : ℝ))‖ ^ 2 := by
  simp only [integral_norm_sq_fderiv_escapeRemoteSpinOrbital]
  exact (Finset.mul_sum _ _ _).symm

/-- A compact normalized remote spin-orbital family exists with a uniform kinetic constant. -/
theorem exists_remote_spin_orbitals (q : ℕ) (hq : 1 ≤ q) (R : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (L : ℝ), 0 < L →
      ∃ g : 𝓢(Position, EuclideanSpace ℂ (Fin q)),
        ‖g.toLp 2 (volume : Measure Position)‖ = 1 ∧
        HasCompactSupport (fun x => g x) ∧
        tsupport (fun x => g x) ⊆ Metric.closedBall (escapeCenter R L) L ∧
        (∑ j : Fin 3, ∫ x, ‖fderiv ℝ (fun y => g y) x
          (PiLp.single 2 j (1 : ℝ))‖ ^ 2) = L⁻¹ ^ 2 * K := by
  obtain ⟨h, _, hh, hn⟩ := exists_normalized_compact_schwartz_orbital
  let t : Fin q := ⟨0, lt_of_lt_of_le Nat.zero_lt_one hq⟩
  let K : ℝ := ∑ j : Fin 3, ∫ x, ‖fderiv ℝ (fun y => h y) x
    (PiLp.single 2 j (1 : ℝ))‖ ^ 2
  refine ⟨K, ?_, ?_⟩
  · exact Finset.sum_nonneg (fun j _ => integral_nonneg (fun x => sq_nonneg _))
  · intro L hL
    exact ⟨escapeRemoteSpinOrbital h hh t R L hL,
      norm_toLp_escapeRemoteSpinOrbital h hh hn t R L hL,
      hasCompactSupport_escapeRemoteSpinOrbital h hh t R L hL,
      tsupport_escapeRemoteSpinOrbital_subset h hh t R L hL,
      sum_integral_norm_sq_fderiv_escapeRemoteSpinOrbital h hh t R L hL⟩

end LiebThirring
end
