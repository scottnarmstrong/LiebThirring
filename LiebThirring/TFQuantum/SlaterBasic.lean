/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Kinetic.Permutation

/-! # Slater determinants of general spatial-spin orbitals

The orbitals are genuine one-particle states, so their value depends on
both position and spin. No common-spin or disjoint-support restriction is made.
-/

public section
open MeasureTheory WithLp
open scoped ENNReal NNReal
namespace LiebThirring

/-- Embed one physical position as a one-particle configuration. -/
@[expose] def oneParticleConfiguration (x : Position) : Configuration 1 :=
  toLp 2 (fun ia => x ia.2)

@[simp] theorem particlePosition_oneParticleConfiguration (x : Position) (i : Fin 1) :
    particlePosition (oneParticleConfiguration x) i = x := by
  apply WithLp.ofLp_injective
  funext a
  exact congrArg (fun j : Fin 1 => (oneParticleConfiguration x) (j, a)) (Subsingleton.elim i 0)

/-- Embed one spin label as a one-electron spin configuration. -/
@[expose] def oneParticleSpinLabel {q : ℕ} (t : Fin q) : SpinLabels 1 q := fun _ => t

/-- Pointwise value of a one-particle spatial-spin orbital. -/
@[expose] noncomputable def orbitalValue {q : ℕ} (u : State 1 q) (x : Position) (t : Fin q) : ℂ :=
  u (oneParticleConfiguration x) (oneParticleSpinLabel t)

/-- The unnormalized determinant of general complex spatial-spin orbitals. -/
@[expose] noncomputable def slaterDeterminant {N q : ℕ} (u : Fin N → State 1 q)
    (x : Configuration N) (s : SpinLabels N q) : ℂ :=
  Matrix.det (fun i j : Fin N => orbitalValue (u j) (particlePosition x i) (s i))

/-- The conventional `1 / sqrt(N!)` Slater amplitude. -/
@[expose] noncomputable def slaterAmplitude {N q : ℕ} (u : Fin N → State 1 q)
    (x : Configuration N) : SpinAmplitudes N q :=
  toLp 2 (fun s => (Real.sqrt N.factorial)⁻¹ * slaterDeterminant u x s)

/-- Simultaneously permuting position and spin rows gives the fermionic sign. -/
theorem slaterDeterminant_permute {N q : ℕ} (u : Fin N → State 1 q)
    (σ : Equiv.Perm (Fin N)) (x : Configuration N) (s : SpinLabels N q) :
    slaterDeterminant u (permutePositions σ x) (permuteSpins σ s) =
      (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : ℂ) * slaterDeterminant u x s := by
  unfold slaterDeterminant orbitalValue
  exact Matrix.det_permute σ
    (fun i j : Fin N => u j (oneParticleConfiguration (particlePosition x i))
      (oneParticleSpinLabel (s i)))

/-- Pointwise antisymmetry of the normalized Slater amplitude. -/
theorem slaterAmplitude_permute {N q : ℕ} (u : Fin N → State 1 q)
    (σ : Equiv.Perm (Fin N)) (x : Configuration N) (s : SpinLabels N q) :
    slaterAmplitude u (permutePositions σ x) (permuteSpins σ s) =
      (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : ℂ) * slaterAmplitude u x s := by
  simp only [slaterAmplitude, PiLp.toLp_apply, slaterDeterminant_permute]
  ring

end LiebThirring
end
