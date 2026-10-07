/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFCoulomb.RegularPotential
public import LiebThirring.TFCoulomb.BoxEnergy
public import LiebThirring.ThomasFermi.Functional
public import LiebThirring.Variational.FormDomain

/-! # Regular box potentials and their discrete Thomas--Fermi functional -/

@[expose] public section

open MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace LiebThirring.TFCoulomb

noncomputable def cappedAttractionExpectation {N q M : ℕ} (δ : ℝ)
    (z : Fin M → ℝ≥0) (R : Fin M → Position) (ψ : FormDomain N q) : ℝ :=
  (∫⁻ x : Configuration N,
    ENNReal.ofReal (∑ i : Fin N,
      tfCappedNuclearPotential δ z R (particlePosition x i)) *
      (‖(ψ : State N q) x‖₊ : ℝ≥0∞) ^ 2).toReal

noncomputable def repulsionExpectation {N q : ℕ} (ψ : FormDomain N q) : ℝ :=
  (∫⁻ x : Configuration N,
    electronRepulsion x * (‖(ψ : State N q) x‖₊ : ℝ≥0∞) ^ 2).toReal

noncomputable def regularScaledQuantumEnergy {N q M : ℕ} (α δ t : ℝ)
    (z : Fin M → ℝ≥0) (R : Fin M → Position) (ψ : FormDomain N q) : ℝ :=
  α ^ (-(5 : ℝ) / 3) * t * (kineticEnergy (ψ : State N q)).toReal +
    α⁻¹ ^ 2 * repulsionExpectation ψ -
    α⁻¹ * cappedAttractionExpectation δ z R ψ

def cubeCappedPotentialValues {M : ℕ} (δ ℓ : ℝ) (z : Fin M → ℝ≥0)
    (R : Fin M → Position) (β : LatticeIndex) : Set ℝ :=
  {v | ∃ x ∈ latticeClosedCell ℓ β, v = tfCappedNuclearPotential δ z R x}

noncomputable def cubeSupCappedPotential {M : ℕ} (δ ℓ : ℝ)
    (z : Fin M → ℝ≥0) (R : Fin M → Position) (β : LatticeIndex) : ℝ :=
  sSup (cubeCappedPotentialValues δ ℓ z R β)

noncomputable def boxCappedPotential {M : ℕ} (δ ℓ : ℝ)
    (z : Fin M → ℝ≥0) (R : Fin M → Position) (x : Position) : ℝ :=
  cubeSupCappedPotential δ ℓ z R (latticeLabel ℓ x)

theorem cubeCappedPotentialValues_nonempty {M : ℕ} {ℓ : ℝ} (hℓ : 0 ≤ ℓ)
    (δ : ℝ) (z : Fin M → ℝ≥0) (R : Fin M → Position) (β : LatticeIndex) :
    (cubeCappedPotentialValues δ ℓ z R β).Nonempty :=
  ⟨tfCappedNuclearPotential δ z R (latticeCorner ℓ β), latticeCorner ℓ β,
    latticeCorner_mem_closedCell hℓ β, rfl⟩

theorem cubeCappedPotentialValues_bddAbove {M : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (ℓ : ℝ) (z : Fin M → ℝ≥0) (R : Fin M → Position) (β : LatticeIndex) :
    BddAbove (cubeCappedPotentialValues δ ℓ z R β) := by
  refine ⟨(∑ k : Fin M, (z k : ℝ)) / δ, ?_⟩
  rintro v ⟨x, _hx, rfl⟩
  exact tfCappedNuclearPotential_le hδ z R x

theorem cubeSupCappedPotential_le {M : ℕ} {δ : ℝ} (hδ : 0 < δ)
    {ℓ : ℝ} (hℓ : 0 ≤ ℓ) (z : Fin M → ℝ≥0) (R : Fin M → Position)
    (β : LatticeIndex) :
    cubeSupCappedPotential δ ℓ z R β ≤ (∑ k : Fin M, (z k : ℝ)) / δ := by
  apply csSup_le (cubeCappedPotentialValues_nonempty hℓ δ z R β)
  rintro v ⟨x, _hx, rfl⟩
  exact tfCappedNuclearPotential_le hδ z R x

theorem tfCappedNuclearPotential_le_boxCappedPotential {M : ℕ} {δ ℓ : ℝ}
    (hδ : 0 < δ) (hℓ : 0 < ℓ) (z : Fin M → ℝ≥0) (R : Fin M → Position)
    (x : Position) :
    tfCappedNuclearPotential δ z R x ≤ boxCappedPotential δ ℓ z R x := by
  apply le_csSup (cubeCappedPotentialValues_bddAbove hδ ℓ z R (latticeLabel ℓ x))
  exact ⟨x, latticeCell_subset_closedCell ℓ _ (mem_latticeCell_label hℓ x), rfl⟩

theorem boxCappedPotential_nonneg {M : ℕ} {δ ℓ : ℝ}
    (hδ : 0 < δ) (hℓ : 0 < ℓ) (z : Fin M → ℝ≥0) (R : Fin M → Position)
    (x : Position) : 0 ≤ boxCappedPotential δ ℓ z R x :=
  (tfCappedNuclearPotential_nonneg hδ z R x).trans
    (tfCappedNuclearPotential_le_boxCappedPotential hδ hℓ z R x)

theorem boxCappedPotential_le {M : ℕ} {δ ℓ : ℝ}
    (hδ : 0 < δ) (hℓ : 0 < ℓ) (z : Fin M → ℝ≥0) (R : Fin M → Position)
    (x : Position) :
    boxCappedPotential δ ℓ z R x ≤ (∑ k : Fin M, (z k : ℝ)) / δ :=
  cubeSupCappedPotential_le hδ hℓ.le z R (latticeLabel ℓ x)

noncomputable def regularDiscreteTFFunctional {M : ℕ} (a δ ℓ : ℝ)
    (z : Fin M → ℝ≥0) (R : Fin M → Position) (ρ : TFDensity) : ℝ :=
  a * (∫ x : Position, (ρ.val x) ^ ((5 : ℝ) / 3)) -
    (∫ x : Position, boxCappedPotential δ ℓ z R x * ρ.val x) +
    tfBoxCoulombEnergy ℓ ρ

def regularDiscreteTFValues {M : ℕ} (a ν δ ℓ : ℝ)
    (z : Fin M → ℝ≥0) (R : Fin M → Position) : Set ℝ :=
  {E | ∃ ρ : TFDensity, tfMass ρ = ν ∧ E = regularDiscreteTFFunctional a δ ℓ z R ρ}

noncomputable def regularDiscreteTFInfimum {M : ℕ} (a ν δ ℓ : ℝ)
    (z : Fin M → ℝ≥0) (R : Fin M → Position) : ℝ :=
  sInf (regularDiscreteTFValues a ν δ ℓ z R)

end LiebThirring.TFCoulomb

end
