/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring
import all LiebThirring.Electrostatics.Basic
public import LiebThirring.Ionization.BindingBound
public import LiebThirring.Ionization.WeakGroundStateBound
public import LiebThirring.Thermodynamic.ThermodynamicLimit
public import LiebThirring.ThomasFermi.MolecularLimit
public import LiebThirring.ThomasFermi.TotalLimit
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.Analysis.Fourier.LpSpace
public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Topology.Instances.EReal.Lemmas
public import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

/-!
# Stability of non-relativistic Coulomb matter

The kinetic Lieb–Thirring inequality and Baxter's electrostatic inequality give
an energy lower bound linear in the number of electrons and nuclei. The kinetic
coefficient is one: units are ℏ²/(2m) = 1 and the Coulomb coupling is one.
Mathlib's Fourier convention uses exp(-2π i x·ξ), hence the factor (2π)².
Spin has q labels; the wavefunction is normalized in L² and changes sign under
simultaneous permutations of positions and spin labels.

All positive energy terms and lower integrals take values in [0,∞]. The Coulomb
kernel is infinite at collisions. An infimum over no nuclei is ∞, with inverse
zero; sums over no particles are zero. The real energy statement explicitly
requires finite kinetic energy and distinct nuclear positions.

Sources: Lieb and Thirring, *Bound for the kinetic energy of fermions which
proves the stability of matter* (1975); Lundholm, *Methods of Modern Mathematical
Physics: Uncertainty and Exclusion Principles in Quantum Mechanics* (2019),
Theorem 6.1 (pp. 89–90), Corollary 6.8 (p. 93), Theorem 7.2 (pp. 102–106),
and Theorem 7.6 (pp. 106–107); Frank, *The Lieb–Thirring inequalities: Recent
results and open problems* (2020), Corollary 6 (pp. 7–9) and Theorem 7 (pp. 9–11).
The coefficient below is Rumin's explicit lower bound, rather than the optimal
Lieb–Thirring constant; see Lundholm's (4.21) and Theorem 6.1.
-/

public section

open MeasureTheory WithLp
open scoped ENNReal NNReal SchwartzMap

namespace LiebThirringAudit

/-! ## Configuration spaces and fermionic states -/

/-- Euclidean three-dimensional position space, with Lebesgue measure. -/
@[expose] def Position  : Type :=
  EuclideanSpace ℝ (Fin 3)

attribute [reducible] Position

/-- Euclidean space of N electron positions, with its product Lebesgue measure. -/
@[expose] def Configuration (N : ℕ) : Type :=
  EuclideanSpace ℝ (Fin N × Fin 3)

attribute [reducible] Configuration

/-- One of q spin labels for each of N electrons. -/
@[expose] def SpinLabels (N q : ℕ) : Type :=
  Fin N → Fin q

attribute [reducible] SpinLabels

/-- Complex spin amplitudes with the Euclidean norm (sum over spin). -/
@[expose] def SpinAmplitudes (N q : ℕ) : Type :=
  EuclideanSpace ℂ (SpinLabels N q)

attribute [reducible] SpinAmplitudes

/-- Square-integrable spin-valued wavefunctions modulo almost-everywhere equality. -/
@[expose] def State (N q : ℕ) : Type :=
  Lp (SpinAmplitudes N q) 2 (volume : Measure (Configuration N))

attribute [reducible] State

/-- Position of electron i in a configuration. -/
@[expose] def particlePosition {N : ℕ} (x : Configuration N) (i : Fin N) : Position :=
  toLp 2 (fun a => x (i, a))

/-- Permutation of electron positions. -/
@[expose] def permutePositions {N : ℕ} (σ : Equiv.Perm (Fin N))
    (x : Configuration N) : Configuration N :=
  toLp 2 (fun ia => x (σ ia.1, ia.2))

/-- The same permutation acting on spin labels. -/
@[expose] def permuteSpins {N q : ℕ} (σ : Equiv.Perm (Fin N))
    (s : SpinLabels N q) : SpinLabels N q :=
  fun i => s (σ i)

/-- The configuration of all electrons except electron i. -/
@[expose] def OtherConfiguration {N : ℕ} (i : Fin N) : Type :=
  EuclideanSpace ℝ ({j : Fin N // j ≠ i} × Fin 3)

attribute [reducible] OtherConfiguration

/-- Insert position x for electron i into the remaining configuration. -/
@[expose] def insertParticle {N : ℕ} (i : Fin N) (x : Position)
    (y : OtherConfiguration i) : Configuration N :=
  toLp 2 (fun ja => if h : ja.1 = i then x ja.2 else y (⟨ja.1, h⟩, ja.2))

/-- Fermionic sign rule almost everywhere, for every permutation and spin label. -/
@[expose] def antisymmetric {N q : ℕ} (ψ : State N q) : Prop :=
  ∀ σ : Equiv.Perm (Fin N), ∀ᵐ x ∂(volume : Measure (Configuration N)),
    ∀ s : SpinLabels N q,
      ψ (permutePositions σ x) (permuteSpins σ s) =
        (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : ℂ) * ψ x s

/-! ## Kinetic energy and density (Lundholm, Theorem 6.1 and Corollary 6.8) -/

/-- Extended kinetic energy, the Fourier integral of (2π)²|ξ|²|ψ̂(ξ)|². -/
@[expose] noncomputable def kineticEnergy {N q : ℕ} (ψ : State N q) : ℝ≥0∞ :=
  ∫⁻ ξ : Configuration N,
    ENNReal.ofReal ((2 * Real.pi) ^ 2) * (‖ξ‖₊ : ℝ≥0∞) ^ 2 *
      (‖(Lp.fourierTransformₗᵢ (Configuration N) (SpinAmplitudes N q) ψ) ξ‖₊ : ℝ≥0∞) ^ 2

/-- One-particle density: sum of all spatial marginals, including all spin amplitudes. -/
@[expose] noncomputable def density {N q : ℕ} (ψ : State N q) (x : Position) : ℝ≥0∞ :=
  ∑ i : Fin N, ∫⁻ y : OtherConfiguration i,
    (‖ψ (insertParticle i x y)‖₊ : ℝ≥0∞) ^ 2

/-- Explicit three-dimensional Rumin coefficient (9/35)(6π²)^(2/3). -/
@[expose] noncomputable def ruminConstant : ℝ≥0 :=
  Real.toNNReal ((9 / 35 : ℝ) * (6 * Real.pi ^ 2) ^ ((2 : ℝ) / 3))

/-! ## Coulomb interactions and screening (Lundholm, Theorem 7.2) -/

/-- Coulomb kernel 1/|x-y| in [0,∞], with value ∞ at x = y. -/
@[expose] noncomputable def coulombKernel (x y : Position) : ℝ≥0∞ :=
  (ENNReal.ofReal ‖x - y‖)⁻¹

/-- Electron repulsion, with each unordered pair counted once. -/
@[expose] noncomputable def electronRepulsion {N : ℕ} (x : Configuration N) : ℝ≥0∞ :=
  ∑ i : Fin N, ∑ j ∈ Finset.univ.filter (fun j : Fin N => i < j),
    coulombKernel (particlePosition x i) (particlePosition x j)

/-- Positive magnitude of electron–nucleus attraction for charges z. -/
@[expose] noncomputable def attraction {N M : ℕ} (z : Fin M → ℝ≥0)
    (R : Fin M → Position) (x : Configuration N) : ℝ≥0∞ :=
  ∑ i : Fin N, ∑ k : Fin M,
    (z k : ℝ≥0∞) * coulombKernel (particlePosition x i) (R k)

/-- Nuclear repulsion, with each unordered pair counted once. -/
@[expose] noncomputable def nuclearRepulsion {M : ℕ} (z : Fin M → ℝ≥0)
    (R : Fin M → Position) : ℝ≥0∞ :=
  ∑ k : Fin M, ∑ l ∈ Finset.univ.filter (fun l : Fin M => k < l),
    ((z k : ℝ≥0∞) * (z l : ℝ≥0∞)) * coulombKernel (R k) (R l)

/-- Distance to the nearest nucleus; ∞ when there are no nuclei. -/
@[expose] noncomputable def nearestNucleusDistance {M : ℕ}
    (R : Fin M → Position) (x : Position) : ℝ≥0∞ :=
  ⨅ k : Fin M, ENNReal.ofReal ‖x - R k‖

/-- Distance from nucleus k to its nearest other nucleus; ∞ for a single nucleus. -/
@[expose] noncomputable def nearestOtherNucleusDistance {M : ℕ}
    (R : Fin M → Position) (k : Fin M) : ℝ≥0∞ :=
  ⨅ l : {l : Fin M // l ≠ k}, ENNReal.ofReal ‖R k - R l‖

/-- Baxter screening term (2Z+1) times the sum of inverse nearest-nucleus distances. -/
@[expose] noncomputable def nearestNucleusControl {N M : ℕ} (Z : ℝ≥0)
    (R : Fin M → Position) (x : Configuration N) : ℝ≥0∞ :=
  (2 * (Z : ℝ≥0∞) + 1) *
    ∑ i : Fin N, (nearestNucleusDistance R (particlePosition x i))⁻¹

/-- Positive nuclear correction (Z²/4) times the sum of inverse nearest-neighbor distances. -/
@[expose] noncomputable def baxterCorrection {M : ℕ} (Z : ℝ≥0)
    (R : Fin M → Position) : ℝ≥0∞ :=
  (Z : ℝ≥0∞) ^ 2 / 4 * ∑ k : Fin M, (nearestOtherNucleusDistance R k)⁻¹

/-! ## Main results -/

/-- Kinetic Lieb–Thirring with spin degeneracy q and Rumin's explicit coefficient.
Lundholm, Theorem 6.1 and Corollary 6.8; Frank, Corollary 6. -/
theorem kinetic_lieb_thirring (q : ℕ) (hq : 1 ≤ q) (N : ℕ) (ψ : State N q)
    (hanti : antisymmetric ψ) (hnorm : ‖ψ‖ = 1) :
    (ruminConstant : ℝ≥0∞) * (q : ℝ≥0∞) ^ (-(2 : ℝ) / 3) *
      (∫⁻ x : Position, density ψ x ^ ((5 : ℝ) / 3)) ≤ kineticEnergy ψ := by
  exact LiebThirring.kinetic_lieb_thirring q hq N ψ hanti hnorm

/-- Baxter's electrostatic inequality for equal nuclear charge Z, including the nuclear correction.
Lundholm, Theorem 7.2. -/
theorem baxter (N M : ℕ) (Z : ℝ≥0) (R : Fin M → Position) (x : Configuration N) :
    attraction (fun _ => Z) R x + baxterCorrection Z R ≤
      electronRepulsion x + nuclearRepulsion (fun _ => Z) R +
        nearestNucleusControl Z R x := by
  exact LiebThirring.baxter N M Z R x

/-- Stability in additive extended form: C depends only on q and the nuclear charge bound Z.
Lundholm, Theorem 7.6; Frank, Theorem 7. -/
theorem stability_of_matter (q : ℕ) (hq : 1 ≤ q) (Z : ℝ≥0) :
    ∃ C : ℝ≥0, 0 < C ∧
      ∀ (N M : ℕ) (z : Fin M → ℝ≥0) (R : Fin M → Position) (ψ : State N q),
        (∀ k, z k ≤ Z) → antisymmetric ψ → ‖ψ‖ = 1 →
          (∫⁻ x : Configuration N, attraction z R x * (‖ψ x‖₊ : ℝ≥0∞) ^ 2) ≤
            kineticEnergy ψ +
              (∫⁻ x : Configuration N, electronRepulsion x * (‖ψ x‖₊ : ℝ≥0∞) ^ 2) +
              nuclearRepulsion z R + (C : ℝ≥0∞) * (N + M : ℕ) := by
  exact LiebThirring.stability_of_matter q hq Z

/-- Stability on the finite kinetic form domain, including finiteness of all Coulomb terms.
Lundholm, Theorem 7.6; Frank, Theorem 7. -/
theorem stability_of_matter_real (q : ℕ) (hq : 1 ≤ q) (Z : ℝ≥0) :
    ∃ C : ℝ≥0, 0 < C ∧
      ∀ (N M : ℕ) (z : Fin M → ℝ≥0) (R : Fin M → Position) (ψ : State N q),
        (∀ k, z k ≤ Z) → Function.Injective R →
          antisymmetric ψ → ‖ψ‖ = 1 → kineticEnergy ψ < ⊤ →
            (∫⁻ x : Configuration N,
              attraction z R x * (‖ψ x‖₊ : ℝ≥0∞) ^ 2) < ⊤ ∧
            (∫⁻ x : Configuration N,
              electronRepulsion x * (‖ψ x‖₊ : ℝ≥0∞) ^ 2) < ⊤ ∧
            nuclearRepulsion z R < ⊤ ∧
            -(C : ℝ) * ((N + M : ℕ) : ℝ) ≤
              (kineticEnergy ψ).toReal +
                (∫⁻ x : Configuration N,
                  electronRepulsion x * (‖ψ x‖₊ : ℝ≥0∞) ^ 2).toReal +
                (nuclearRepulsion z R).toReal -
                (∫⁻ x : Configuration N,
                  attraction z R x * (‖ψ x‖₊ : ℝ≥0∞) ^ 2).toReal := by
  exact LiebThirring.stability_of_matter_real q hq Z


/-! ## Atomic binding and weak ground states (Lieb, 1984) -/

/-- Unnormalized antisymmetric states with finite Fourier kinetic energy. -/
@[expose] def FormDomain (N q : ℕ) : Type :=
  {ψ : State N q // antisymmetric ψ ∧ kineticEnergy ψ < ⊤}

attribute [reducible] FormDomain

/-- The real quadratic energy for distinct fixed nuclei, without normalization. -/
@[expose] noncomputable def realEnergy {N q M : ℕ} (z : Fin M → ℝ≥0)
    (R : Fin M → Position) (_hR : Function.Injective R) (ψ : FormDomain N q) : ℝ :=
  (kineticEnergy (ψ : State N q)).toReal +
    (∫⁻ x : Configuration N,
      electronRepulsion x * (‖(ψ : State N q) x‖₊ : ℝ≥0∞) ^ 2).toReal +
    (nuclearRepulsion z R).toReal * ‖(ψ : State N q)‖ ^ 2 -
    (∫⁻ x : Configuration N,
      attraction z R x * (‖(ψ : State N q) x‖₊ : ℝ≥0∞) ^ 2).toReal

/-- The literal Coulomb form, conjugate-linear in the first state. -/
@[expose] noncomputable def energyForm {N q M : ℕ} (z : Fin M → ℝ≥0)
    (R : Fin M → Position) (_hR : Function.Injective R)
    (φ ψ : FormDomain N q) : ℂ :=
  (∫ ξ : Configuration N, (((2 * Real.pi) ^ 2 * ‖ξ‖ ^ 2 : ℝ) : ℂ) *
    inner ℂ
      ((Lp.fourierTransformₗᵢ (Configuration N) (SpinAmplitudes N q)
        (φ : State N q)) ξ)
      ((Lp.fourierTransformₗᵢ (Configuration N) (SpinAmplitudes N q)
        (ψ : State N q)) ξ)) +
    (∫ x : Configuration N,
      (((electronRepulsion x).toReal - (attraction z R x).toReal : ℝ) : ℂ) *
        inner ℂ ((φ : State N q) x) ((ψ : State N q) x)) +
    ((nuclearRepulsion z R).toReal : ℂ) *
      inner ℂ (φ : State N q) (ψ : State N q)

/-- Infimum over all normalized form-domain states; an empty set has value `⊤`. -/
@[expose] noncomputable def groundStateEnergy (N q M : ℕ) (z : Fin M → ℝ≥0)
    (R : Fin M → Position) (hR : Function.Injective R) : EReal :=
  ⨅ ψ : {ψ : FormDomain N q // ‖(ψ : State N q)‖ = 1},
    (realEnergy z R hR ψ.val : EReal)

/-- A nonzero form-domain state satisfying the weak equation at a real eigenvalue. -/
@[expose] def is_weak_eigenfunction {N q M : ℕ} (z : Fin M → ℝ≥0)
    (R : Fin M → Position) (hR : Function.Injective R)
    (E : ℝ) (ψ : FormDomain N q) : Prop :=
  (ψ : State N q) ≠ 0 ∧
    ∀ φ : FormDomain N q,
      energyForm z R hR φ ψ = (E : ℂ) * inner ℂ (φ : State N q) (ψ : State N q)

/-- A unit weak eigenfunction whose real eigenvalue equals the variational infimum. -/
@[expose] def is_weak_ground_state {N q M : ℕ} (z : Fin M → ℝ≥0)
    (R : Fin M → Position) (hR : Function.Injective R)
    (ψ : FormDomain N q) : Prop :=
  ‖(ψ : State N q)‖ = 1 ∧
    ∃ E : ℝ, groundStateEnergy N q M z R hR = (E : EReal) ∧
      is_weak_eigenfunction z R hR E ψ

/-- One nucleus of charge `Z` at the origin, in the `-Δ` convention. -/
@[expose] noncomputable def atomicGroundStateEnergy (N q : ℕ) (Z : ℝ≥0) : EReal :=
  groundStateEnergy N q 1 (fun _ => Z) (fun _ => 0)
    (fun _ _ _ => Subsingleton.elim _ _)

/-- Strict atomic binding implies N < 2Z + 1 (Lieb, 1984). -/
theorem electron_count_lt_of_atomic_binding (q : ℕ) (hq : 1 ≤ q)
    (N : ℕ) (Z : ℝ≥0) (hZ : 0 < Z)
    (hbind : atomicGroundStateEnergy N q Z < atomicGroundStateEnergy (N - 1) q Z) :
    (N : ℝ) < 2 * (Z : ℝ) + 1 := by
  exact LiebThirring.electron_count_lt_of_atomic_binding q hq N Z hZ hbind

/-- A normalized weak atomic ground state implies N < 2Z + 1 (Lieb, 1984). -/
theorem electron_count_lt_of_atomic_weak_ground_state (q : ℕ) (hq : 1 ≤ q)
    (N : ℕ) (Z : ℝ≥0) (hZ : 0 < Z) (ψ : FormDomain N q)
    (hψ : is_weak_ground_state (fun _ : Fin 1 => Z) (fun _ : Fin 1 => 0)
      (fun _ _ _ => Subsingleton.elim _ _) ψ) :
    (N : ℝ) < 2 * (Z : ℝ) + 1 := by
  exact LiebThirring.electron_count_lt_of_atomic_weak_ground_state q hq N Z hZ ψ hψ



/-! ## Canonical thermodynamic limit (Lieb–Lebowitz, 1972) -/

/-- The Euclidean product, with its L² spatial norm and Lebesgue volume. -/
@[expose] def QuantumConfiguration (N M : ℕ) : Type :=
  WithLp 2 (Configuration N × Configuration M)

attribute [reducible] QuantumConfiguration

/-- Spin labels belong only to the electrons; nuclei are spinless. -/
@[expose] def QuantumState (N M q : ℕ) : Type :=
  Lp (SpinAmplitudes N q) 2 (volume : Measure (QuantumConfiguration N M))

attribute [reducible] QuantumState

/-- Electron position and spin permutations act with the fermionic sign. -/
@[expose] def quantum_antisymmetric {N M q : ℕ} (ψ : QuantumState N M q) : Prop :=
  ∀ σ : Equiv.Perm (Fin N),
    ∀ᵐ X ∂(volume : Measure (QuantumConfiguration N M)),
      ∀ s : SpinLabels N q,
        ψ (toLp 2 (permutePositions σ X.fst, X.snd)) (permuteSpins σ s) =
          (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : ℂ) * ψ X s

/-- Nucleus permutations have positive sign and do not act on electron spins. -/
@[expose] def nuclear_symmetric {N M q : ℕ} (ψ : QuantumState N M q) : Prop :=
  ∀ τ : Equiv.Perm (Fin M),
    ∀ᵐ X ∂(volume : Measure (QuantumConfiguration N M)),
      ∀ s : SpinLabels N q,
        ψ (toLp 2 (X.fst, permutePositions τ X.snd)) s = ψ X s

/-- Nuclear mass measured in electron masses; electron kinetic coefficient is one. -/
@[expose] noncomputable def nuclearKineticCoefficient
    (m : {m : ℝ≥0 // 0 < m}) : ℝ≥0 :=
  m.val⁻¹

/-- The gradient-square normalization uses the Fourier multiplier (2π)². -/
@[expose] noncomputable def quantumElectronKineticEnergy {N M q : ℕ}
    (ψ : QuantumState N M q) : ℝ≥0∞ :=
  ∫⁻ ξ : QuantumConfiguration N M,
    ENNReal.ofReal ((2 * Real.pi) ^ 2) * (‖ξ.fst‖₊ : ℝ≥0∞) ^ 2 *
      (‖(Lp.fourierTransformₗᵢ (QuantumConfiguration N M)
        (SpinAmplitudes N q) ψ) ξ‖₊ : ℝ≥0∞) ^ 2

/-- The gradient-square normalization uses the Fourier multiplier (2π)². -/
@[expose] noncomputable def quantumNuclearKineticEnergy {N M q : ℕ}
    (ψ : QuantumState N M q) : ℝ≥0∞ :=
  ∫⁻ ξ : QuantumConfiguration N M,
    ENNReal.ofReal ((2 * Real.pi) ^ 2) * (‖ξ.snd‖₊ : ℝ≥0∞) ^ 2 *
      (‖(Lp.fourierTransformₗᵢ (QuantumConfiguration N M)
        (SpinAmplitudes N q) ψ) ξ‖₊ : ℝ≥0∞) ^ 2

/-- Unnormalized joint H¹ states with the two species statistics. -/
@[expose] def QuantumFormDomain (N M q : ℕ) : Type :=
  {ψ : QuantumState N M q //
    quantum_antisymmetric ψ ∧ nuclear_symmetric ψ ∧
      quantumElectronKineticEnergy ψ < ⊤ ∧ quantumNuclearKineticEnergy ψ < ⊤}

attribute [reducible] QuantumFormDomain

/-- Electron and nuclear repulsions, including the nuclear probability density. -/
@[expose] noncomputable def quantumRepulsionEnergy {N M q : ℕ}
    (z : ℕ) (ψ : QuantumState N M q) : ℝ≥0∞ :=
  ∫⁻ X : QuantumConfiguration N M,
    (electronRepulsion X.fst +
      nuclearRepulsion (fun _ : Fin M => (z : ℝ≥0))
        (fun k => particlePosition X.snd k)) * (‖ψ X‖₊ : ℝ≥0∞) ^ 2

/-- Electron-nucleus attraction with constant integer nuclear charge. -/
@[expose] noncomputable def quantumAttractionEnergy {N M q : ℕ}
    (z : ℕ) (ψ : QuantumState N M q) : ℝ≥0∞ :=
  ∫⁻ X : QuantumConfiguration N M,
    attraction (fun _ : Fin M => (z : ℝ≥0))
      (fun k => particlePosition X.snd k) X.fst * (‖ψ X‖₊ : ℝ≥0∞) ^ 2

/-- Both expectations are finite on this finite-kinetic carrier by pair Hardy bounds. -/
@[expose] noncomputable def quantumCoulombEnergy {N M q : ℕ}
    (z : ℕ) (ψ : QuantumFormDomain N M q) : ℝ :=
  (quantumRepulsionEnergy z ψ.val).toReal -
    (quantumAttractionEnergy z ψ.val).toReal

/-- Full joint energy; no fixed-nucleus minimization occurs. -/
@[expose] noncomputable def quantumEnergy {N M q : ℕ}
    (z : ℕ) (m : {m : ℝ≥0 // 0 < m}) (ψ : QuantumFormDomain N M q) : ℝ :=
  (quantumElectronKineticEnergy ψ.val).toReal +
    (nuclearKineticCoefficient m : ℝ) * (quantumNuclearKineticEnergy ψ.val).toReal +
    quantumCoulombEnergy z ψ

/-- Approximation by symmetric compact smooth states in the full kinetic form norm. -/
@[expose] def is_dirichlet_ball {N M q : ℕ}
    (m : {m : ℝ≥0 // 0 < m}) (L : {L : ℝ // 0 < L})
    (ψ : QuantumState N M q) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ f : 𝓢(QuantumConfiguration N M, SpinAmplitudes N q),
      let φ : QuantumState N M q :=
        f.toLp 2 (volume : Measure (QuantumConfiguration N M))
      IsCompact (tsupport f) ∧
      tsupport f ⊆ {X | (∀ i : Fin N, particlePosition X.fst i ∈
        Metric.ball (0 : Position) L.val) ∧
        (∀ k : Fin M, particlePosition X.snd k ∈ Metric.ball (0 : Position) L.val)} ∧
      quantum_antisymmetric φ ∧ nuclear_symmetric φ ∧
      ENNReal.ofReal (‖ψ - φ‖ ^ 2) +
        quantumElectronKineticEnergy (ψ - φ) +
        (nuclearKineticCoefficient m : ℝ≥0∞) *
          quantumNuclearKineticEnergy (ψ - φ) < ENNReal.ofReal ε

/-- The unnormalized Dirichlet form domain in a positive-radius ball. -/
@[expose] def DirichletBallFormDomain (N M q : ℕ)
    (m : {m : ℝ≥0 // 0 < m}) (L : {L : ℝ // 0 < L}) : Type :=
  {ψ : QuantumFormDomain N M q // is_dirichlet_ball m L ψ.val}

attribute [reducible] DirichletBallFormDomain

/-- Honest complete-order infimum: empty sectors give top, unbounded ones bottom. -/
@[expose] noncomputable def confinedGroundStateEnergy (N M q z : ℕ)
    (m : {m : ℝ≥0 // 0 < m}) (L : {L : ℝ // 0 < L}) : EReal :=
  ⨅ ψ : {ψ : DirichletBallFormDomain N M q m L // ‖ψ.val.val‖ = 1},
    (quantumEnergy z m ψ.val.val : EReal)

/-- The literal Euclidean ball volume formula, on positive radii. -/
@[expose] noncomputable def ballVolume (L : {L : ℝ // 0 < L}) : ℝ :=
  (4 * Real.pi / 3) * L.val ^ 3

/-- Unique continuous convex neutral energy density along every density sequence (Lieb–Lebowitz, 1972). -/
theorem exists_unique_thermodynamic_energy_density
    (q : ℕ) (hq : 1 ≤ q) (z : ℕ) (hz : 1 ≤ z)
    (m : {m : ℝ≥0 // 0 < m}) :
    ∃! e : ℝ≥0 → ℝ,
      e 0 = 0 ∧ Continuous e ∧
      (∀ (ρ₁ ρ₂ : ℝ≥0) (t : ℝ≥0), t ≤ 1 →
        e (t * ρ₁ + (1 - t) * ρ₂) ≤
          (t : ℝ) * e ρ₁ + (1 - (t : ℝ)) * e ρ₂) ∧
      ∀ (ρ : ℝ≥0) (L : ℕ → {L : ℝ // 0 < L}) (M : ℕ → ℕ),
        Filter.Tendsto (fun j => (L j).val) Filter.atTop Filter.atTop →
        Filter.Tendsto (fun j => (M j : ℝ) / ballVolume (L j))
          Filter.atTop (nhds (ρ : ℝ)) →
        Filter.Tendsto
          (fun j => confinedGroundStateEnergy (z * M j) (M j) q z m (L j) /
            (ballVolume (L j) : EReal))
          Filter.atTop (nhds (e ρ : EReal)) := by
  exact LiebThirring.exists_unique_thermodynamic_energy_density q hq z hz m



/-! ## Molecular Thomas–Fermi limits (Lieb–Simon, 1977; Lieb, 1981) -/

/-- The Coulomb potential `Φ_α(x) = ∫ |x - y|⁻¹ dα(y)` of a positive measure, in `ℝ≥0∞`. -/
@[expose] noncomputable def coulombPotential (α : Measure Position) (x : Position) : ℝ≥0∞ :=
  ∫⁻ y, coulombKernel x y ∂α

/-- The mutual Coulomb energy `I(α, β) = ∬ |x - y|⁻¹ dα(x) dβ(y)` of positive measures,
in `ℝ≥0∞` (no factor `1/2`). -/
@[expose] noncomputable def coulombEnergy (α β : Measure Position) : ℝ≥0∞ :=
  ∫⁻ x, coulombPotential β x ∂α

/-- Nonnegative a.e. classes in L¹ ∩ L^{5/3}, with no quantum representability restriction. -/
@[expose] def TFDensity : Type :=
  {ρ : Lp ℝ ((5 : ℝ≥0∞) / 3) (volume : Measure Position) //
    (∀ᵐ x ∂(volume : Measure Position), 0 ≤ ρ x) ∧
      Integrable (fun x : Position => ρ x) volume}

/-- The Lebesgue mass of a Thomas–Fermi density. -/
@[expose] noncomputable def tfMass (ρ : TFDensity) : ℝ :=
  ∫ x : Position, ρ.val x

/-- The absolutely continuous positive measure ρ dx. -/
@[expose] noncomputable def tfDensityMeasure (ρ : TFDensity) : Measure Position :=
  volume.withDensity (fun x : Position => ENNReal.ofReal (ρ.val x))

/-- The mutual Coulomb form, including the factor one half. -/
@[expose] noncomputable def tfCoulombEnergy (ρ σ : TFDensity) : ℝ :=
  (coulombEnergy (tfDensityMeasure ρ) (tfDensityMeasure σ)).toReal / 2

/-- Positive nuclear potential; the value at each pole is immaterial to Lebesgue integrals. -/
@[expose] noncomputable def tfNuclearPotential {M : ℕ}
    (z : Fin M → ℝ≥0) (R : Fin M → Position) (x : Position) : ℝ :=
  ∑ k : Fin M, (z k : ℝ) / ‖x - R k‖

/-- The sharp −Δ semiclassical coefficient for a fixed positive spin multiplicity. -/
@[expose] noncomputable def tfKineticConstant (q : {q : ℕ // 1 ≤ q}) : {a : ℝ // 0 < a} :=
  ⟨(3 / 5 : ℝ) * (6 * Real.pi ^ 2 / (q.val : ℝ)) ^ ((2 : ℝ) / 3), by
    have hq : (0 : ℝ) < (q.val : ℝ) := by
      have : 0 < q.val := q.property
      exact_mod_cast this
    positivity⟩

/-- The electronic TF functional; a is the entire positive kinetic coefficient. -/
@[expose] noncomputable def tfFunctional {M : ℕ} (a : {a : ℝ // 0 < a})
    (z : Fin M → ℝ≥0) (R : Fin M → Position) (ρ : TFDensity) : ℝ :=
  a.val * (∫ x : Position, (ρ.val x) ^ ((5 : ℝ) / 3)) -
    (∫ x : Position, tfNuclearPotential z R x * ρ.val x) +
    tfCoulombEnergy ρ ρ

/-- The honest extended-real infimum at exact mass ν. -/
@[expose] noncomputable def tfEnergy {M : ℕ} (a : {a : ℝ // 0 < a})
    (ν : ℝ≥0) (z : Fin M → ℝ≥0) (R : Fin M → Position) : EReal :=
  ⨅ ρ : {ρ : TFDensity // tfMass ρ = (ν : ℝ)},
    (tfFunctional a z R ρ.val : EReal)

/-- Electronic energy T+B−A, omitting the nuclear constant, on the finite kinetic form domain. -/
@[expose] noncomputable def electronicGroundStateEnergy (N q M : ℕ)
    (z : Fin M → ℝ≥0) (R : Fin M → Position) : EReal :=
  ⨅ ψ : {ψ : FormDomain N q // ‖(ψ : State N q)‖ = 1},
    (((kineticEnergy (ψ.val : State N q)).toReal +
      (∫⁻ x : Configuration N,
        electronRepulsion x * (‖(ψ.val : State N q) x‖₊ : ℝ≥0∞) ^ 2).toReal -
      (∫⁻ x : Configuration N,
        attraction z R x * (‖(ψ.val : State N q) x‖₊ : ℝ≥0∞) ^ 2).toReal : ℝ) : EReal)

/-- Electronic energy converges under the molecular large-charge scaling (Lieb–Simon, 1977). -/
theorem tendsto_electronicGroundStateEnergy_tf (q : {q : ℕ // 1 ≤ q})
    (M : ℕ) (hM : 1 ≤ M) (ν : ℝ≥0) (hν : 0 < ν)
    (z : Fin M → ℝ≥0) (hz : ∀ k, 0 < z k)
    (R : Fin M → Position) (hR : Function.Injective R)
    (N : ℕ → ℕ) (hN : Filter.Tendsto N Filter.atTop Filter.atTop) :
    Filter.Tendsto
      (fun j =>
        let α : ℝ≥0 := (N j : ℝ≥0) / ν
        (((α : ℝ) ^ (-(7 : ℝ) / 3) : ℝ) : EReal) *
          electronicGroundStateEnergy (N j) q.val M
            (fun k => α * z k)
            (fun k => ((α : ℝ) ^ (-(1 : ℝ) / 3)) • R k))
      Filter.atTop (nhds (tfEnergy (tfKineticConstant q) ν z R)) := by
  exact LiebThirring.tendsto_electronicGroundStateEnergy_tf q M hM ν hν z hz R hR N hN

/-- Total energy converges with the nuclear repulsion included (Lieb–Simon, 1977). -/
theorem tendsto_groundStateEnergy_tf (q : {q : ℕ // 1 ≤ q})
    (M : ℕ) (hM : 1 ≤ M) (ν : ℝ≥0) (hν : 0 < ν)
    (z : Fin M → ℝ≥0) (hz : ∀ k, 0 < z k)
    (R : Fin M → Position) (hR : Function.Injective R)
    (N : ℕ → ℕ) (hN : Filter.Tendsto N Filter.atTop Filter.atTop)
    (hRN : ∀ j, Function.Injective
      (fun k => ((((N j : ℝ≥0) / ν : ℝ≥0) : ℝ) ^ (-(1 : ℝ) / 3)) • R k)) :
    Filter.Tendsto
      (fun j =>
        let α : ℝ≥0 := (N j : ℝ≥0) / ν
        (((α : ℝ) ^ (-(7 : ℝ) / 3) : ℝ) : EReal) *
          groundStateEnergy (N j) q.val M
            (fun k => α * z k)
            (fun k => ((α : ℝ) ^ (-(1 : ℝ) / 3)) • R k) (hRN j))
      Filter.atTop
      (nhds (tfEnergy (tfKineticConstant q) ν z R +
        ((nuclearRepulsion z R).toReal : EReal))) := by
  exact LiebThirring.tendsto_groundStateEnergy_tf q M hM ν hν z hz R hR N hN hRN

end LiebThirringAudit

end
