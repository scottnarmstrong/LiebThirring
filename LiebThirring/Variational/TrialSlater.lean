/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Variational.TrialOrbitals

/-! # Compact smooth Slater amplitudes -/

public section

open MeasureTheory WithLp Set Function
open scoped ENNReal NNReal ContDiff SchwartzMap

namespace LiebThirring

/-- Regroup configuration coordinates into particle positions. -/
@[expose] noncomputable def trialConfigurationHomeomorph (N : ℕ) :
    Configuration N ≃ₜ (Fin N → Position) :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin N × Fin 3 => ℝ)).toHomeomorph |>.trans
    (Homeomorph.piCurry.trans (Homeomorph.piCongrRight fun _ : Fin N =>
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.toHomeomorph))

/-- Coordinate evaluation is smooth. -/
theorem contDiff_particlePosition {N : ℕ} (i : Fin N) :
    ContDiff ℝ ∞ (fun x : Configuration N => particlePosition x i) := by
  apply (contDiff_piLp 2).mpr
  intro a
  exact ((contDiff_apply ℝ ℝ (i, a)).comp
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin N × Fin 3 => ℝ)).contDiff)

/-- The spatial determinant of one-particle orbitals. -/
@[expose] noncomputable def trialSlaterSpatial {N : ℕ}
    (b : Fin N → Position → ℝ) (x : Configuration N) : ℝ :=
  Matrix.det (fun i j : Fin N => b j (particlePosition x i))

/-- Permuting particles multiplies the spatial determinant by the fermionic sign. -/
theorem trialSlaterSpatial_permute {N : ℕ} (b : Fin N → Position → ℝ)
    (σ : Equiv.Perm (Fin N)) (x : Configuration N) :
    trialSlaterSpatial b (permutePositions σ x) =
      (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : ℝ) * trialSlaterSpatial b x := by
  exact Matrix.det_permute σ (fun i j : Fin N => b j (particlePosition x i))

/-- The determinant is smooth when the orbitals are smooth. -/
theorem contDiff_trialSlaterSpatial {N : ℕ} (b : Fin N → Position → ℝ)
    (hb : ∀ i, ContDiff ℝ ∞ (b i)) : ContDiff ℝ ∞ (trialSlaterSpatial b) := by
  classical
  have hdet : trialSlaterSpatial b = fun x : Configuration N =>
      ∑ σ : Equiv.Perm (Fin N), (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : ℝ) *
        ∏ i : Fin N, b i (particlePosition x (σ i)) :=
    funext fun x => Matrix.det_apply' (fun i j : Fin N => b j (particlePosition x i))
  rw [hdet]
  apply ContDiff.sum
  intro σ _
  apply contDiff_const.mul
  apply contDiff_prod
  intro i _
  exact (hb i).comp (contDiff_particlePosition (σ i))

/-- Compact orbitals give a compactly supported many-particle determinant. -/
theorem hasCompactSupport_trialSlaterSpatial {N : ℕ} (b : Fin N → Position → ℝ)
    (hb : ∀ i, HasCompactSupport (b i)) : HasCompactSupport (trialSlaterSpatial b) := by
  classical
  let K : Set Position := ⋃ j : Fin N, tsupport (b j)
  have hK : IsCompact K := isCompact_iUnion hb
  have hprod : IsCompact (Set.pi Set.univ (fun _ : Fin N => K)) :=
    isCompact_univ_pi (fun _ => hK)
  apply HasCompactSupport.of_support_subset_isCompact
    ((trialConfigurationHomeomorph N).isCompact_preimage.mpr hprod)
  intro x hx
  change ∀ i ∈ (Set.univ : Set (Fin N)), particlePosition x i ∈ K
  intro i _
  by_contra hi
  have hrow (j : Fin N) : b j (particlePosition x i) = 0 := by
    apply image_eq_zero_of_notMem_tsupport
    intro hj
    exact hi (mem_iUnion_of_mem j hj)
  exact hx (Matrix.det_eq_zero_of_row_eq_zero i hrow)

/-- All particles have the chosen spin label, giving a unit spin basis vector. -/
@[expose] noncomputable def trialSpinVector (N q : ℕ) (t : Fin q) : SpinAmplitudes N q :=
  toLp 2 (fun s : SpinLabels N q => if s = (fun _ => t) then 1 else 0)

/-- Simultaneous spin permutations fix a constant spin label. -/
theorem trialSpinVector_permute {N q : ℕ} (t : Fin q)
    (σ : Equiv.Perm (Fin N)) (s : SpinLabels N q) :
    trialSpinVector N q t (permuteSpins σ s) = trialSpinVector N q t s := by
  have heq : permuteSpins σ s = (fun _ => t) ↔ s = (fun _ => t) := by
    constructor
    · intro h
      funext i
      have hi := congrFun h (σ.symm i)
      simpa only [permuteSpins, σ.apply_symm_apply] using hi
    · intro h
      subst s
      rfl
  change (if permuteSpins σ s = (fun _ => t) then (1 : ℂ) else 0) =
    (if s = (fun _ => t) then (1 : ℂ) else 0)
  simp only [heq]

/-- Slater amplitudes with every particle in one spin state. -/
@[expose] noncomputable def trialSlater {N q : ℕ}
    (b : Fin N → Position → ℝ) (t : Fin q) (x : Configuration N) : SpinAmplitudes N q :=
  trialSlaterSpatial b x • trialSpinVector N q t

/-- Smoothness of the Slater amplitudes. -/
theorem contDiff_trialSlater {N q : ℕ} (b : Fin N → Position → ℝ)
    (hb : ∀ i, ContDiff ℝ ∞ (b i)) (t : Fin q) : ContDiff ℝ ∞ (trialSlater b t) :=
  (contDiff_trialSlaterSpatial b hb).smul contDiff_const

/-- Compact support of the Slater amplitudes. -/
theorem hasCompactSupport_trialSlater {N q : ℕ} (b : Fin N → Position → ℝ)
    (hb : ∀ i, HasCompactSupport (b i)) (t : Fin q) : HasCompactSupport (trialSlater b t) :=
  (hasCompactSupport_trialSlaterSpatial b hb).smul_right

/-- Pointwise antisymmetry of the spatial and spin Slater amplitudes. -/
theorem trialSlater_permute {N q : ℕ} (b : Fin N → Position → ℝ) (t : Fin q)
    (σ : Equiv.Perm (Fin N)) (x : Configuration N) (s : SpinLabels N q) :
    trialSlater b t (permutePositions σ x) (permuteSpins σ s) =
      (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : ℂ) * trialSlater b t x s := by
  change (trialSlaterSpatial b (permutePositions σ x) : ℂ) *
      trialSpinVector N q t (permuteSpins σ s) = _
  rw [trialSlaterSpatial_permute, trialSpinVector_permute]
  simp only [Complex.ofReal_mul, Complex.ofReal_intCast, trialSlater,
    PiLp.smul_apply, Complex.real_smul]
  ring

end LiebThirring

end
