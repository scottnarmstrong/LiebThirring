/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFCubes.CubeHilbertBases
public import LiebThirring.TFCubes.CubeBasisMixedIndices

/-! # Complete mixed sine/cosine bases for cube derivatives -/

@[expose] public section

open MeasureTheory Set
open scoped BigOperators

namespace LiebThirring.TFCubes

/-- Three possibly different interval bases on the translated physical cube. -/
noncomputable def cubeScalarHetProductBasis {ι₀ ι₁ ι₂ : Type*}
    (b : Position) (ℓ : {ℓ : ℝ // 0 < ℓ})
    (B₀ : HilbertBasis ι₀ ℂ (Lp ℂ 2 (volume.restrict (Ioo 0 ℓ.val))))
    (B₁ : HilbertBasis ι₁ ℂ (Lp ℂ 2 (volume.restrict (Ioo 0 ℓ.val))))
    (B₂ : HilbertBasis ι₂ ℂ (Lp ℂ 2 (volume.restrict (Ioo 0 ℓ.val)))) :
    HilbertBasis ((ι₀ × ι₁) × ι₂) ℂ (RegionState Position ℂ (cubeInterior b ℓ)) :=
  mapHilbertBasis (cubeCoordinateL2Equiv b ℓ) (hilbertBasisPiThreeProductHet B₀ B₁ B₂)

theorem cubeScalarHetProductBasis_ae {ι₀ ι₁ ι₂ : Type*}
    (b : Position) (ℓ : {ℓ : ℝ // 0 < ℓ})
    (B₀ : HilbertBasis ι₀ ℂ (Lp ℂ 2 (volume.restrict (Ioo 0 ℓ.val))))
    (B₁ : HilbertBasis ι₁ ℂ (Lp ℂ 2 (volume.restrict (Ioo 0 ℓ.val))))
    (B₂ : HilbertBasis ι₂ ℂ (Lp ℂ 2 (volume.restrict (Ioo 0 ℓ.val))))
    (φ₀ : ι₀ → ℝ → ℂ) (φ₁ : ι₁ → ℝ → ℂ) (φ₂ : ι₂ → ℝ → ℂ)
    (h₀ : ∀ i, B₀ i =ᵐ[volume.restrict (Ioo 0 ℓ.val)] φ₀ i)
    (h₁ : ∀ i, B₁ i =ᵐ[volume.restrict (Ioo 0 ℓ.val)] φ₁ i)
    (h₂ : ∀ i, B₂ i =ᵐ[volume.restrict (Ioo 0 ℓ.val)] φ₂ i)
    (k : ((ι₀ × ι₁) × ι₂)) :
    cubeScalarHetProductBasis b ℓ B₀ B₁ B₂ k =ᵐ[volume.restrict (cubeInterior b ℓ)]
      fun x => (φ₀ k.1.1 (x 0 - b 0) * φ₁ k.1.2 (x 1 - b 1)) *
        φ₂ k.2 (x 2 - b 2) := by
  have hproduct : hilbertBasisPiThreeProductHet B₀ B₁ B₂ k =ᵐ[cubeCoordinateMeasure ℓ]
      fun x => (φ₀ k.1.1 (x 0) * φ₁ k.1.2 (x 1)) * φ₂ k.2 (x 2) := by
    have hf (a : Fin 3) := Measure.quasiMeasurePreserving_eval
      (fun _ : Fin 3 => volume.restrict (Ioo 0 ℓ.val)) a
    filter_upwards [hilbertBasisPiThreeProductHet_ae B₀ B₁ B₂ k,
      (hf 0).ae (h₀ k.1.1), (hf 1).ae (h₁ k.1.2), (hf 2).ae (h₂ k.2)]
      with x hx h0 h1 h2
    rw [hx, h0, h1, h2]
  rw [cubeScalarHetProductBasis, mapHilbertBasis_apply]
  exact (cubeCoordinateL2LI_ae b ℓ _).trans
    ((measurePreserving_cubeCoordinates_restrict b ℓ).quasiMeasurePreserving.ae hproduct)

/-- Complete active-cosine and spectator-sine scalar basis. -/
noncomputable def dirichletMixedCubeScalarBasis (ℓ : {ℓ : ℝ // 0 < ℓ})
    (b : Position) (a : Fin 3) :
    HilbertBasis (DirichletMixedFrequencyIndex a) ℂ
      (RegionState Position ℂ (cubeInterior b ℓ)) := by
  refine Fin.cases ?_ (fun a => ?_) a
  · exact reindexHilbertBasis (cubeScalarHetProductBasis b ℓ (neumannIntervalBasis ℓ) (dirichletIntervalBasis ℓ) (dirichletIntervalBasis ℓ))
        dirichletMixedFrequencyEquivZero.symm
  · refine Fin.cases ?_ (fun a => ?_) a
    · exact reindexHilbertBasis (cubeScalarHetProductBasis b ℓ (dirichletIntervalBasis ℓ) (neumannIntervalBasis ℓ) (dirichletIntervalBasis ℓ))
        dirichletMixedFrequencyEquivOne.symm
    · have ha : a = 0 := Subsingleton.elim _ _
      subst a
      exact reindexHilbertBasis (cubeScalarHetProductBasis b ℓ (dirichletIntervalBasis ℓ) (dirichletIntervalBasis ℓ) (neumannIntervalBasis ℓ))
        dirichletMixedFrequencyEquivTwo.symm

/-- Complete active-sine and spectator-cosine scalar basis. -/
noncomputable def neumannMixedCubeScalarBasis (ℓ : {ℓ : ℝ // 0 < ℓ})
    (b : Position) (a : Fin 3) :
    HilbertBasis (NeumannMixedFrequencyIndex a) ℂ
      (RegionState Position ℂ (cubeInterior b ℓ)) := by
  refine Fin.cases ?_ (fun a => ?_) a
  · exact reindexHilbertBasis (cubeScalarHetProductBasis b ℓ (dirichletIntervalBasis ℓ) (neumannIntervalBasis ℓ) (neumannIntervalBasis ℓ))
        neumannMixedFrequencyEquivZero.symm
  · refine Fin.cases ?_ (fun a => ?_) a
    · exact reindexHilbertBasis (cubeScalarHetProductBasis b ℓ (neumannIntervalBasis ℓ) (dirichletIntervalBasis ℓ) (neumannIntervalBasis ℓ))
        neumannMixedFrequencyEquivOne.symm
    · have ha : a = 0 := Subsingleton.elim _ _
      subst a
      exact reindexHilbertBasis (cubeScalarHetProductBasis b ℓ (neumannIntervalBasis ℓ) (neumannIntervalBasis ℓ) (dirichletIntervalBasis ℓ))
        neumannMixedFrequencyEquivTwo.symm

@[simp] theorem neumannMixedCubeScalarBasis_zero
    (ℓ : {ℓ : ℝ // 0 < ℓ}) (b : Position) :
    neumannMixedCubeScalarBasis ℓ b 0 =
      reindexHilbertBasis (cubeScalarHetProductBasis b ℓ (dirichletIntervalBasis ℓ) (neumannIntervalBasis ℓ) (neumannIntervalBasis ℓ))
        neumannMixedFrequencyEquivZero.symm := by rfl

@[simp] theorem neumannMixedCubeScalarBasis_one
    (ℓ : {ℓ : ℝ // 0 < ℓ}) (b : Position) :
    neumannMixedCubeScalarBasis ℓ b 1 =
      reindexHilbertBasis (cubeScalarHetProductBasis b ℓ (neumannIntervalBasis ℓ) (dirichletIntervalBasis ℓ) (neumannIntervalBasis ℓ))
        neumannMixedFrequencyEquivOne.symm := by rfl

@[simp] theorem neumannMixedCubeScalarBasis_two
    (ℓ : {ℓ : ℝ // 0 < ℓ}) (b : Position) :
    neumannMixedCubeScalarBasis ℓ b 2 =
      reindexHilbertBasis (cubeScalarHetProductBasis b ℓ (neumannIntervalBasis ℓ) (neumannIntervalBasis ℓ) (dirichletIntervalBasis ℓ))
        neumannMixedFrequencyEquivTwo.symm := by rfl

theorem neumannMixedCubeScalarBasis_ae {q : ℕ} (ℓ : {ℓ : ℝ // 0 < ℓ})
    (b : Position) (a : Fin 3) (p : NeumannMixedCubeModeIndex q a) :
    neumannMixedCubeScalarBasis ℓ b a p.1 =ᵐ[volume.restrict (cubeInterior b ℓ)]
      neumannMixedCubeSpatialMode ℓ b a p := by
  fin_cases a
  · change neumannMixedCubeScalarBasis ℓ b (0 : Fin 3) p.1
        =ᵐ[volume.restrict (cubeInterior b ℓ)] neumannMixedCubeSpatialMode ℓ b 0 p
    rw [neumannMixedCubeScalarBasis_zero, reindexHilbertBasis_apply]
    have h := cubeScalarHetProductBasis_ae b ℓ
      (dirichletIntervalBasis ℓ) (neumannIntervalBasis ℓ) (neumannIntervalBasis ℓ)
      (fun n x => (dirichletIntervalMode ℓ n x : ℂ)) (fun n x => (neumannIntervalMode ℓ n x : ℂ)) (fun n x => (neumannIntervalMode ℓ n x : ℂ))
      (fun n => (dirichletIntervalBasis_apply ℓ n) ▸ dirichletIntervalModeL2_ae ℓ n)
      (fun n => (neumannIntervalBasis_apply ℓ n) ▸ neumannIntervalModeL2_ae ℓ n)
      (fun n => (neumannIntervalBasis_apply ℓ n) ▸ neumannIntervalModeL2_ae ℓ n)
      (neumannMixedFrequencyEquivZero p.1)
    filter_upwards [h] with x hx
    simpa [neumannMixedFrequencyEquivZero, neumannMixedCubeSpatialMode,
      neumannCubeMixedTestLimit, Fin.prod_univ_three, mul_assoc] using hx
  · change neumannMixedCubeScalarBasis ℓ b (1 : Fin 3) p.1
        =ᵐ[volume.restrict (cubeInterior b ℓ)] neumannMixedCubeSpatialMode ℓ b 1 p
    rw [neumannMixedCubeScalarBasis_one, reindexHilbertBasis_apply]
    have h := cubeScalarHetProductBasis_ae b ℓ
      (neumannIntervalBasis ℓ) (dirichletIntervalBasis ℓ) (neumannIntervalBasis ℓ)
      (fun n x => (neumannIntervalMode ℓ n x : ℂ)) (fun n x => (dirichletIntervalMode ℓ n x : ℂ)) (fun n x => (neumannIntervalMode ℓ n x : ℂ))
      (fun n => (neumannIntervalBasis_apply ℓ n) ▸ neumannIntervalModeL2_ae ℓ n)
      (fun n => (dirichletIntervalBasis_apply ℓ n) ▸ dirichletIntervalModeL2_ae ℓ n)
      (fun n => (neumannIntervalBasis_apply ℓ n) ▸ neumannIntervalModeL2_ae ℓ n)
      (neumannMixedFrequencyEquivOne p.1)
    filter_upwards [h] with x hx
    simpa [neumannMixedFrequencyEquivOne, neumannMixedCubeSpatialMode,
      neumannCubeMixedTestLimit, Fin.prod_univ_three, mul_assoc] using hx
  · change neumannMixedCubeScalarBasis ℓ b (2 : Fin 3) p.1
        =ᵐ[volume.restrict (cubeInterior b ℓ)] neumannMixedCubeSpatialMode ℓ b 2 p
    rw [neumannMixedCubeScalarBasis_two, reindexHilbertBasis_apply]
    have h := cubeScalarHetProductBasis_ae b ℓ
      (neumannIntervalBasis ℓ) (neumannIntervalBasis ℓ) (dirichletIntervalBasis ℓ)
      (fun n x => (neumannIntervalMode ℓ n x : ℂ)) (fun n x => (neumannIntervalMode ℓ n x : ℂ)) (fun n x => (dirichletIntervalMode ℓ n x : ℂ))
      (fun n => (neumannIntervalBasis_apply ℓ n) ▸ neumannIntervalModeL2_ae ℓ n)
      (fun n => (neumannIntervalBasis_apply ℓ n) ▸ neumannIntervalModeL2_ae ℓ n)
      (fun n => (dirichletIntervalBasis_apply ℓ n) ▸ dirichletIntervalModeL2_ae ℓ n)
      (neumannMixedFrequencyEquivTwo p.1)
    filter_upwards [h] with x hx
    simpa [neumannMixedFrequencyEquivTwo, neumannMixedCubeSpatialMode,
      neumannCubeMixedTestLimit, Fin.prod_univ_three, mul_assoc] using hx

end LiebThirring.TFCubes

end
