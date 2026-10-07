/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFCoulomb.CubeKernel
import LiebThirring.Electrostatics.ShellAssemblyEnergy

/-! # Coulomb pair counting in occupation sectors

Lieb–Simon (1977) III.12 (60b): regroup the actual particle pairs by their cube
labels, retaining the diagonal and subtracting exactly the excluded self pairs.
-/

public section

open MeasureTheory
open scoped ENNReal

namespace LiebThirring.TFCoulomb

/-- Number of particles assigned to a cube. -/
@[expose] noncomputable def sectorCount {N : ℕ} (b : Fin N → LatticeIndex)
    (β : LatticeIndex) : ℕ := (Finset.univ.filter (fun i => b i = β)).card

/-- Finitely many cube labels occupied by an assignment. -/
@[expose] noncomputable def occupiedCubes {N : ℕ} (b : Fin N → LatticeIndex) :
    Finset LatticeIndex := Finset.univ.image b

/-- All cube pairs, including equal labels. -/
@[expose] noncomputable def sectorDirectEnergy {N : ℕ} (ℓ : ℝ)
    (b : Fin N → LatticeIndex) : ℝ :=
  (∑ β ∈ occupiedCubes b, ∑ γ ∈ occupiedCubes b,
    cubeWeight ℓ β γ * (sectorCount b β : ℝ) * (sectorCount b γ : ℝ)) / 2

theorem sum_sectorCount {N : ℕ} (b : Fin N → LatticeIndex) :
    ∑ β ∈ occupiedCubes b, sectorCount b β = N := by
  classical
  simpa only [occupiedCubes, sectorCount, nsmul_eq_mul, mul_one, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, smul_eq_mul] using
    (Finset.sum_comp (s := Finset.univ) (fun _ : LatticeIndex => (1 : ℕ)) b).symm

theorem sum_cubeWeight_labels {N : ℕ} (ℓ : ℝ) (b : Fin N → LatticeIndex) :
    (∑ i : Fin N, ∑ j : Fin N, cubeWeight ℓ (b i) (b j)) =
      2 * sectorDirectEnergy ℓ b := by
  classical
  have hinner (β : LatticeIndex) :
      (∑ j : Fin N, cubeWeight ℓ β (b j)) =
        ∑ γ ∈ occupiedCubes b, (sectorCount b γ : ℝ) * cubeWeight ℓ β γ := by
    simpa only [occupiedCubes, sectorCount, nsmul_eq_mul] using
      Finset.sum_comp (s := Finset.univ) (cubeWeight ℓ β) b
  rw [Finset.sum_comp (fun β => ∑ j : Fin N, cubeWeight ℓ β (b j)) b]
  simp only [hinner, nsmul_eq_mul]
  unfold sectorDirectEnergy occupiedCubes
  rw [show (2 : ℝ) * ((∑ β ∈ Finset.univ.image b, ∑ γ ∈ Finset.univ.image b,
      cubeWeight ℓ β γ * (sectorCount b β : ℝ) * (sectorCount b γ : ℝ)) / 2) =
      ∑ β ∈ Finset.univ.image b, ∑ γ ∈ Finset.univ.image b,
      cubeWeight ℓ β γ * (sectorCount b β : ℝ) * (sectorCount b γ : ℝ) by ring]
  apply Finset.sum_congr rfl
  intro β _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro γ _
  unfold sectorCount
  ring

/-- The double sum contains precisely N spurious particle self pairs. -/
theorem sectorDirectEnergy_eq_pair_sum_add {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    (b : Fin N → LatticeIndex) :
    sectorDirectEnergy ℓ b =
      (∑ i : Fin N, ∑ j ∈ Finset.univ.filter (fun j => i < j),
        cubeWeight ℓ (b i) (b j)) + (N : ℝ) / (2 * Real.sqrt 3 * ℓ) := by
  classical
  have hw : ∀ i j : Fin N, 0 ≤ cubeWeight ℓ (b i) (b j) :=
    fun i j => (cubeWeight_pos hℓ _ _).le
  have he := symmetric_sum_eq_diagonal_add
    (fun i j : Fin N => ENNReal.ofReal (cubeWeight ℓ (b i) (b j)))
    (fun i j => congrArg ENNReal.ofReal (cubeWeight_comm ℓ _ _))
  have hreal : (∑ i : Fin N, ∑ j : Fin N, cubeWeight ℓ (b i) (b j)) =
      (∑ i : Fin N, cubeWeight ℓ (b i) (b i)) +
        2 * ∑ i : Fin N, ∑ j ∈ Finset.univ.filter (fun j => i < j),
          cubeWeight ℓ (b i) (b j) := by
    have hsum := congrArg ENNReal.toReal he
    have hdiag : (∑ i : Fin N, ENNReal.ofReal (cubeWeight ℓ (b i) (b i))) ≠ ⊤ :=
      ENNReal.sum_ne_top.mpr (fun _ _ => ENNReal.ofReal_ne_top)
    have hpair : (∑ i : Fin N, ∑ j ∈ Finset.univ.filter (fun j => i < j),
        ENNReal.ofReal (cubeWeight ℓ (b i) (b j))) ≠ ⊤ :=
      ENNReal.sum_ne_top.mpr (fun _ _ =>
        ENNReal.sum_ne_top.mpr (fun _ _ => ENNReal.ofReal_ne_top))
    rw [ENNReal.toReal_add hdiag (ENNReal.mul_ne_top (by norm_num) hpair),
      ENNReal.toReal_mul] at hsum
    simpa [ENNReal.toReal_sum, ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal, hw] using hsum
  simp only [cubeWeight_self hℓ.le, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul] at hreal
  rw [sum_cubeWeight_labels ℓ b] at hreal
  have hs : (N : ℝ) / (2 * Real.sqrt 3 * ℓ) =
      (N : ℝ) * (1 / (Real.sqrt 3 * ℓ)) / 2 := by ring
  rw [hs]
  linarith only [hreal]

/-- The pointwise sector lower bound is valid even at electron collisions.
The additive extended form avoids infinity-minus-infinity conventions. -/
theorem ofReal_sectorDirectEnergy_le_repulsion_add {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    (x : Configuration N) (b : Fin N → LatticeIndex)
    (hx : ∀ i, particlePosition x i ∈ latticeClosedCell ℓ (b i)) :
    ENNReal.ofReal (sectorDirectEnergy ℓ b) ≤
      electronRepulsion x + ENNReal.ofReal ((N : ℝ) / (2 * Real.sqrt 3 * ℓ)) := by
  classical
  rw [sectorDirectEnergy_eq_pair_sum_add hℓ b, ENNReal.ofReal_add]
  · apply add_le_add_left
    rw [ENNReal.ofReal_sum_of_nonneg]
    · unfold electronRepulsion
      apply Finset.sum_le_sum
      intro i _
      rw [ENNReal.ofReal_sum_of_nonneg (fun j _ => (cubeWeight_pos hℓ _ _).le)]
      apply Finset.sum_le_sum
      intro j _
      exact ofReal_cubeWeight_le_coulombKernel hℓ (hx i) (hx j)
    · intro i _
      exact Finset.sum_nonneg (fun j _ => (cubeWeight_pos hℓ _ _).le)
  · exact Finset.sum_nonneg fun i _ =>
      Finset.sum_nonneg fun j _ => (cubeWeight_pos hℓ _ _).le
  · exact div_nonneg (Nat.cast_nonneg N)
      (mul_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg 3)) hℓ.le)

/-- Positivity of the direct occupation energy. -/
theorem sectorDirectEnergy_nonneg {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    (b : Fin N → LatticeIndex) : 0 ≤ sectorDirectEnergy ℓ b := by
  unfold sectorDirectEnergy
  apply div_nonneg _ (by norm_num)
  apply Finset.sum_nonneg
  intro β _
  apply Finset.sum_nonneg
  intro γ _
  exact mul_nonneg (mul_nonneg (cubeWeight_pos hℓ β γ).le (Nat.cast_nonneg _))
    (Nat.cast_nonneg _)

/-- Boxwise Coulomb comparison in a normalized occupation sector. The probability measure and its
support are the Neumann sector estimate restriction data. -/
theorem sectorDirectEnergy_le_repulsion_integral_add {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    (b : Fin N → LatticeIndex) (σ : MeasureTheory.Measure (Configuration N))
    [MeasureTheory.IsProbabilityMeasure σ]
    (hsupport : ∀ᵐ x ∂σ, ∀ i, particlePosition x i ∈ latticeClosedCell ℓ (b i))
    (hfinite : (∫⁻ x, electronRepulsion x ∂σ) ≠ ⊤) :
    sectorDirectEnergy ℓ b ≤ (∫⁻ x, electronRepulsion x ∂σ).toReal +
      (N : ℝ) / (2 * Real.sqrt 3 * ℓ) := by
  have h : ENNReal.ofReal (sectorDirectEnergy ℓ b) ≤
      (∫⁻ x, electronRepulsion x ∂σ) +
        ENNReal.ofReal ((N : ℝ) / (2 * Real.sqrt 3 * ℓ)) := by
    calc
      _ = ∫⁻ _x : Configuration N, ENNReal.ofReal (sectorDirectEnergy ℓ b) ∂σ := by
        rw [lintegral_const, measure_univ, mul_one]
      _ ≤ ∫⁻ x, electronRepulsion x +
          ENNReal.ofReal ((N : ℝ) / (2 * Real.sqrt 3 * ℓ)) ∂σ := by
        apply lintegral_mono_ae
        filter_upwards [hsupport] with x hx
        exact ofReal_sectorDirectEnergy_le_repulsion_add hℓ x b hx
      _ = _ := by rw [lintegral_add_right electronRepulsion (measurable_const : Measurable (fun _x : Configuration N =>
        ENNReal.ofReal ((N : ℝ) / (2 * Real.sqrt 3 * ℓ)))), lintegral_const,
        measure_univ, mul_one]
  have hn : 0 ≤ (N : ℝ) / (2 * Real.sqrt 3 * ℓ) := by positivity
  have hr := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr
    ⟨hfinite, ENNReal.ofReal_ne_top⟩) h
  rw [ENNReal.toReal_ofReal (sectorDirectEnergy_nonneg hℓ b),
    ENNReal.toReal_add hfinite ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hn] at hr
  exact hr

end LiebThirring.TFCoulomb

end
