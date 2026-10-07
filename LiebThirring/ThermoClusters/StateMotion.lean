/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.ThermoClusters.Rigid
public import LiebThirring.Thermodynamic.QuantumAntisymmetric
public import LiebThirring.Thermodynamic.NuclearSymmetric
import LiebThirring.ThermoForm.SmoothCore

/-!
# Rigid transport of joint quantum states

The inverse coordinate pullback is a complex linear L² isometry. It acts trivially
on electron spin labels and preserves both statistics predicates.

-/

public section
open MeasureTheory WithLp
namespace LiebThirring

/-- Pull back a joint quantum state by the inverse simultaneous spatial motion. -/
@[expose] noncomputable def quantumStateMotion {N M q : ℕ}
    (Q : Position ≃ₗᵢ[ℝ] Position) (c : Position) :
    QuantumState N M q →ₗᵢ[ℂ] QuantumState N M q :=
  Lp.compMeasurePreservingₗᵢ ℂ (quantumRigidMotion Q c).symm
    (measurePreserving_quantumRigidMotion_symm Q c)

/-- The actual representative of the transported L² state agrees almost everywhere with pullback. -/
theorem coeFn_quantumStateMotion {N M q : ℕ}
    (Q : Position ≃ₗᵢ[ℝ] Position) (c : Position) (ψ : QuantumState N M q) :
    quantumStateMotion Q c ψ =ᵐ[volume] ψ ∘ (quantumRigidMotion Q c).symm :=
  Lp.coeFn_compMeasurePreserving ψ (measurePreserving_quantumRigidMotion_symm Q c)

@[simp] theorem norm_quantumStateMotion {N M q : ℕ}
    (Q : Position ≃ₗᵢ[ℝ] Position) (c : Position) (ψ : QuantumState N M q) :
    ‖quantumStateMotion Q c ψ‖ = ‖ψ‖ := (quantumStateMotion Q c).norm_map ψ

/-- The inverse state action pulls back by the forward coordinate motion. -/
@[expose] noncomputable def quantumStateMotionInverse {N M q : ℕ}
    (Q : Position ≃ₗᵢ[ℝ] Position) (c : Position) :
    QuantumState N M q →ₗᵢ[ℂ] QuantumState N M q :=
  Lp.compMeasurePreservingₗᵢ ℂ (quantumRigidMotion Q c)
    (measurePreserving_quantumRigidMotion Q c)

theorem coeFn_quantumStateMotionInverse {N M q : ℕ}
    (Q : Position ≃ₗᵢ[ℝ] Position) (c : Position) (ψ : QuantumState N M q) :
    quantumStateMotionInverse Q c ψ =ᵐ[volume] ψ ∘ quantumRigidMotion Q c :=
  Lp.coeFn_compMeasurePreserving ψ (measurePreserving_quantumRigidMotion Q c)

@[simp] theorem quantumStateMotionInverse_quantumStateMotion {N M q : ℕ}
    (Q : Position ≃ₗᵢ[ℝ] Position) (c : Position) (ψ : QuantumState N M q) :
    quantumStateMotionInverse Q c (quantumStateMotion Q c ψ) = ψ := by
  apply Lp.ext
  have hi := (measurePreserving_quantumRigidMotion Q c).quasiMeasurePreserving.ae
    (coeFn_quantumStateMotion Q c ψ)
  filter_upwards [coeFn_quantumStateMotionInverse Q c (quantumStateMotion Q c ψ), hi]
    with X hX hinner
  rw [hX]
  simp only [Function.comp_apply]
  rw [hinner]
  simp only [Function.comp_apply, AffineIsometryEquiv.symm_apply_apply]

@[simp] theorem quantumStateMotion_quantumStateMotionInverse {N M q : ℕ}
    (Q : Position ≃ₗᵢ[ℝ] Position) (c : Position) (ψ : QuantumState N M q) :
    quantumStateMotion Q c (quantumStateMotionInverse Q c ψ) = ψ := by
  apply Lp.ext
  have hi := (measurePreserving_quantumRigidMotion_symm Q c).quasiMeasurePreserving.ae
    (coeFn_quantumStateMotionInverse Q c ψ)
  filter_upwards [coeFn_quantumStateMotion Q c (quantumStateMotionInverse Q c ψ), hi]
    with X hX hinner
  rw [hX]
  simp only [Function.comp_apply]
  rw [hinner]
  simp only [Function.comp_apply, AffineIsometryEquiv.apply_symm_apply]

/-- Rigid pullback preserves fermionic electron statistics, including the spin permutation. -/
theorem quantum_antisymmetric_quantumStateMotion {N M q : ℕ}
    (Q : Position ≃ₗᵢ[ℝ] Position) (c : Position) (ψ : QuantumState N M q)
    (hψ : quantum_antisymmetric ψ) : quantum_antisymmetric (quantumStateMotion Q c ψ) := by
  intro σ
  have hcoeff := coeFn_quantumStateMotion Q c ψ
  have hperm := (measurePreserving_quantum_electron_permutation (M := M) σ).quasiMeasurePreserving.ae hcoeff
  have hstat := (measurePreserving_quantumRigidMotion_symm Q c).quasiMeasurePreserving.ae (hψ σ)
  filter_upwards [hcoeff, hperm, hstat] with X hX hσ hsymm
  intro s
  rw [hσ, hX]
  change ψ ((quantumRigidMotion Q c).symm (toLp 2 (permutePositions σ X.fst, X.snd)))
    (permuteSpins σ s) = (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : ℂ) *
      ψ ((quantumRigidMotion Q c).symm X) s
  rw [quantumRigidMotion_symm_electron_permutation]
  exact hsymm s

/-- Rigid pullback preserves bosonic spinless nucleus statistics. -/
theorem nuclear_symmetric_quantumStateMotion {N M q : ℕ}
    (Q : Position ≃ₗᵢ[ℝ] Position) (c : Position) (ψ : QuantumState N M q)
    (hψ : nuclear_symmetric ψ) : nuclear_symmetric (quantumStateMotion Q c ψ) := by
  intro τ
  have hcoeff := coeFn_quantumStateMotion Q c ψ
  have hperm := (measurePreserving_quantum_nuclear_permutation (N := N) τ).quasiMeasurePreserving.ae hcoeff
  have hstat := (measurePreserving_quantumRigidMotion_symm Q c).quasiMeasurePreserving.ae (hψ τ)
  filter_upwards [hcoeff, hperm, hstat] with X hX hτ hsymm
  intro s
  rw [hτ, hX]
  change ψ ((quantumRigidMotion Q c).symm (toLp 2 (X.fst, permutePositions τ X.snd))) s =
    ψ ((quantumRigidMotion Q c).symm X) s
  rw [quantumRigidMotion_symm_nuclear_permutation]
  exact hsymm s

/-- Forward-coordinate pullback also preserves fermionic electron statistics. -/
theorem quantum_antisymmetric_quantumStateMotionInverse {N M q : ℕ}
    (Q : Position ≃ₗᵢ[ℝ] Position) (c : Position) (ψ : QuantumState N M q)
    (hψ : quantum_antisymmetric ψ) : quantum_antisymmetric (quantumStateMotionInverse Q c ψ) := by
  intro σ
  have hcoeff := coeFn_quantumStateMotionInverse Q c ψ
  have hperm := (measurePreserving_quantum_electron_permutation (M := M) σ).quasiMeasurePreserving.ae hcoeff
  have hstat := (measurePreserving_quantumRigidMotion Q c).quasiMeasurePreserving.ae (hψ σ)
  filter_upwards [hcoeff, hperm, hstat] with X hX hσ hsymm
  intro s
  rw [hσ, hX]
  change ψ (quantumRigidMotion Q c (toLp 2 (permutePositions σ X.fst, X.snd)))
    (permuteSpins σ s) = (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : ℂ) * ψ (quantumRigidMotion Q c X) s
  rw [quantumRigidMotion_electron_permutation]
  exact hsymm s

/-- Forward-coordinate pullback also preserves bosonic nucleus statistics. -/
theorem nuclear_symmetric_quantumStateMotionInverse {N M q : ℕ}
    (Q : Position ≃ₗᵢ[ℝ] Position) (c : Position) (ψ : QuantumState N M q)
    (hψ : nuclear_symmetric ψ) : nuclear_symmetric (quantumStateMotionInverse Q c ψ) := by
  intro τ
  have hcoeff := coeFn_quantumStateMotionInverse Q c ψ
  have hperm := (measurePreserving_quantum_nuclear_permutation (N := N) τ).quasiMeasurePreserving.ae hcoeff
  have hstat := (measurePreserving_quantumRigidMotion Q c).quasiMeasurePreserving.ae (hψ τ)
  filter_upwards [hcoeff, hperm, hstat] with X hX hτ hsymm
  intro s
  rw [hτ, hX]
  change ψ (quantumRigidMotion Q c (toLp 2 (X.fst, permutePositions τ X.snd))) s =
    ψ (quantumRigidMotion Q c X) s
  rw [quantumRigidMotion_nuclear_permutation]
  exact hsymm s

end LiebThirring
end
