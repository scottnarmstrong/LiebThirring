/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.ThermoClusters.StateMotion
public import LiebThirring.Thermodynamic.QuantumRepulsionEnergy
public import LiebThirring.Thermodynamic.QuantumAttractionEnergy

/-!
# Coulomb invariance of joint rigid transport

All interparticle distances are unchanged by the simultaneous motion. The exact
nonnegative repulsive and attractive expectations are therefore unchanged
by inverse pullback, without any finite-energy assumption.

-/

public section
open MeasureTheory WithLp
open scoped ENNReal NNReal
namespace LiebThirring

/-- The inverse rigid motion preserves the Coulomb kernel as well. -/
theorem coulombKernel_rigid_inverse (Q : Position ≃ₗᵢ[ℝ] Position) (c x y : Position) :
    coulombKernel (Q.symm (x-c)) (Q.symm (y-c)) = coulombKernel x y := by
  rw [coulombKernel, ← Q.symm.map_sub, Q.symm.norm_map, sub_sub_sub_cancel_right]
  rfl

theorem electronRepulsion_quantumRigidMotion_symm {N M : ℕ}
    (Q : Position ≃ₗᵢ[ℝ] Position) (c : Position) (X : QuantumConfiguration N M) :
    electronRepulsion ((quantumRigidMotion Q c).symm X).fst = electronRepulsion X.fst := by
  have hf (i : Fin N) : particlePosition ((quantumRigidMotion Q c).symm X).fst i =
      Q.symm (particlePosition X.fst i - c) := rfl
  simp only [electronRepulsion, hf, coulombKernel_rigid_inverse]

theorem nuclearRepulsion_quantumRigidMotion_symm {N M : ℕ}
    (Q : Position ≃ₗᵢ[ℝ] Position) (c : Position) (z : Fin M → ℝ≥0)
    (X : QuantumConfiguration N M) :
    nuclearRepulsion z (fun k => particlePosition ((quantumRigidMotion Q c).symm X).snd k) =
      nuclearRepulsion z (fun k => particlePosition X.snd k) := by
  have hs (k : Fin M) : particlePosition ((quantumRigidMotion Q c).symm X).snd k =
      Q.symm (particlePosition X.snd k - c) := rfl
  simp only [nuclearRepulsion, hs, coulombKernel_rigid_inverse]

theorem attraction_quantumRigidMotion_symm {N M : ℕ}
    (Q : Position ≃ₗᵢ[ℝ] Position) (c : Position) (z : Fin M → ℝ≥0)
    (X : QuantumConfiguration N M) :
    attraction z (fun k => particlePosition ((quantumRigidMotion Q c).symm X).snd k)
      ((quantumRigidMotion Q c).symm X).fst =
      attraction z (fun k => particlePosition X.snd k) X.fst := by
  have hf (i : Fin N) : particlePosition ((quantumRigidMotion Q c).symm X).fst i =
      Q.symm (particlePosition X.fst i - c) := rfl
  have hs (k : Fin M) : particlePosition ((quantumRigidMotion Q c).symm X).snd k =
      Q.symm (particlePosition X.snd k - c) := rfl
  simp only [attraction, hf, hs, coulombKernel_rigid_inverse]

/-- The exact joint repulsion expectation is invariant under state transport. -/
@[simp] theorem quantumRepulsionEnergy_quantumStateMotion {N M q : ℕ}
    (Q : Position ≃ₗᵢ[ℝ] Position) (c : Position) (z : ℕ) (ψ : QuantumState N M q) :
    quantumRepulsionEnergy z (quantumStateMotion Q c ψ) = quantumRepulsionEnergy z ψ := by
  unfold quantumRepulsionEnergy
  calc
    _ = ∫⁻ X : QuantumConfiguration N M,
        (electronRepulsion ((quantumRigidMotion Q c).symm X).fst +
          nuclearRepulsion (fun _ : Fin M => (z : ℝ≥0))
            (fun k => particlePosition ((quantumRigidMotion Q c).symm X).snd k)) *
          (‖ψ ((quantumRigidMotion Q c).symm X)‖₊ : ℝ≥0∞) ^ 2 := by
      apply lintegral_congr_ae
      filter_upwards [coeFn_quantumStateMotion Q c ψ] with X hX
      rw [hX, electronRepulsion_quantumRigidMotion_symm, nuclearRepulsion_quantumRigidMotion_symm]
      rfl
    _ = _ := (measurePreserving_quantumRigidMotion_symm (N := N) (M := M) Q c).lintegral_comp_emb
      (quantumRigidMotionMeasurableEquiv Q c).symm.measurableEmbedding
      (fun X : QuantumConfiguration N M =>
        (electronRepulsion X.fst + nuclearRepulsion (fun _ : Fin M => (z : ℝ≥0))
          (fun k => particlePosition X.snd k)) * (‖ψ X‖₊ : ℝ≥0∞) ^ 2)

/-- The exact joint attraction expectation is invariant under state transport. -/
@[simp] theorem quantumAttractionEnergy_quantumStateMotion {N M q : ℕ}
    (Q : Position ≃ₗᵢ[ℝ] Position) (c : Position) (z : ℕ) (ψ : QuantumState N M q) :
    quantumAttractionEnergy z (quantumStateMotion Q c ψ) = quantumAttractionEnergy z ψ := by
  unfold quantumAttractionEnergy
  calc
    _ = ∫⁻ X : QuantumConfiguration N M,
        attraction (fun _ : Fin M => (z : ℝ≥0))
          (fun k => particlePosition ((quantumRigidMotion Q c).symm X).snd k)
          ((quantumRigidMotion Q c).symm X).fst *
          (‖ψ ((quantumRigidMotion Q c).symm X)‖₊ : ℝ≥0∞) ^ 2 := by
      apply lintegral_congr_ae
      filter_upwards [coeFn_quantumStateMotion Q c ψ] with X hX
      rw [hX, attraction_quantumRigidMotion_symm]
      rfl
    _ = _ := (measurePreserving_quantumRigidMotion_symm (N := N) (M := M) Q c).lintegral_comp_emb
      (quantumRigidMotionMeasurableEquiv Q c).symm.measurableEmbedding
      (fun X : QuantumConfiguration N M =>
        attraction (fun _ : Fin M => (z : ℝ≥0))
          (fun k => particlePosition X.snd k) X.fst * (‖ψ X‖₊ : ℝ≥0∞) ^ 2)

end LiebThirring
end
