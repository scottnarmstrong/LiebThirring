/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFCubes.CubeProductTestL2
public import LiebThirring.TFCubes.CubeTestLimits
public import LiebThirring.TFCubes.CubeHilbertBases

/-! # Physical weak coefficient identities on cubes -/

@[expose] public section

open MeasureTheory
open scoped InnerProductSpace

namespace LiebThirring.TFCubes

theorem neumannCubeMixedDerivativeLimit_eq_frequency_mul
    (ℓ : {ℓ : ℝ // 0 < ℓ}) (b : Position) (k : Fin 3 → ℕ)
    (a : Fin 3) (n : ℕ+) (x : Position) :
    neumannCubeMixedDerivativeLimit ℓ b k a n x =
      (intervalFrequency ℓ n : ℂ) *
        neumannCubeSpatialMode ℓ b (Function.update k a (n : ℕ)) x := by
  unfold neumannCubeMixedDerivativeLimit neumannCubeSpatialMode
  rw [fderiv_dirichletIntervalMode_ofReal]
  have hprod := Finset.prod_erase_mul (s := Finset.univ)
    (f := fun i : Fin 3 =>
      (neumannIntervalMode ℓ (Function.update k a (n : ℕ) i) (x i - b i) : ℂ))
    (Finset.mem_univ a)
  simp only [Function.update_self] at hprod
  have hoff : (∏ i ∈ Finset.univ.erase a,
      (neumannIntervalMode ℓ (Function.update k a (n : ℕ) i) (x i - b i) : ℂ)) =
      ∏ i ∈ Finset.univ.erase a,
        (neumannIntervalMode ℓ (k i) (x i - b i) : ℂ) := by
    apply Finset.prod_congr rfl
    intro i hi
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]
  rw [← hprod]
  rw [hoff]
  ring

theorem neumannCubeMixedDerivativeLimitL2_eq_smul_basis
    (ℓ : {ℓ : ℝ // 0 < ℓ}) (b : Position) (k : Fin 3 → ℕ)
    (a : Fin 3) (n : ℕ+) :
    neumannCubeMixedDerivativeLimitL2 ℓ b k a n =
      (intervalFrequency ℓ n : ℂ) •
        neumannCubeScalarBasis ℓ b (Function.update k a (n : ℕ)) := by
  apply Lp.ext
  filter_upwards [(neumannCubeMixedDerivativeLimit_memLp ℓ b k a n).coeFn_toLp,
    Lp.coeFn_smul (intervalFrequency ℓ n : ℂ)
      (neumannCubeScalarBasis ℓ b (Function.update k a (n : ℕ))),
    neumannCubeScalarBasis_ae ℓ b (Function.update k a (n : ℕ))] with x hx hs hbasis
  rw [neumannCubeMixedDerivativeLimitL2, hx, hs]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [hbasis]
  exact neumannCubeMixedDerivativeLimit_eq_frequency_mul ℓ b k a n x

/-- Testing a genuine local weak derivative against the compact cube product jets
gives the physical mixed-mode coefficient identity. -/
theorem HasWeakDerivativeOn.neumannCube_mixed_coeff
    (ℓ : {ℓ : ℝ // 0 < ℓ}) (b : Position) (k : Fin 3 → ℕ)
    (a : Fin 3) (n : ℕ+)
    {u g : RegionState Position ℂ (cubeInterior b ℓ)}
    (h : HasWeakDerivativeOn (cubeInterior b ℓ)
      (EuclideanSpace.basisFun (Fin 3) ℝ a) u g) :
    ⟪neumannCubeMixedTestLimitL2 ℓ b k a n, g⟫_ℂ =
      -(intervalFrequency ℓ n : ℂ) *
        ⟪neumannCubeScalarBasis ℓ b (Function.update k a (n : ℕ)), u⟫_ℂ := by
  have hw := h.test_limit (fun j => neumannCubeProductTest ℓ b k a n j)
    (hasCompactSupport_neumannCubeProductTest ℓ b k a n)
    (contDiff_neumannCubeProductTest ℓ b k a n)
    (tsupport_neumannCubeProductTest_subset_cubeInterior ℓ b k a n)
    (tendsto_localL2_neumannCubeProductTest ℓ b k a n)
    (tendsto_localL2_fderiv_neumannCubeProductTest ℓ b k a n)
  rw [neumannCubeMixedDerivativeLimitL2_eq_smul_basis, inner_smul_left,
    Complex.conj_ofReal] at hw
  simpa only [neg_mul] using hw

end LiebThirring.TFCubes

end
