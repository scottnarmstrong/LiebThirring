/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Defs.Configuration

/-!
# Coulomb interactions

Electron and nuclear interactions, nearest-nucleus distances, and the electrostatic correction
in Baxter’s inequality.
-/

public section

open MeasureTheory WithLp
open scoped ENNReal NNReal

namespace LiebThirring

@[expose] noncomputable def coulombKernel (x y : Position) : ℝ≥0∞ :=
  (ENNReal.ofReal ‖x - y‖)⁻¹

@[expose] noncomputable def electronRepulsion {N : ℕ} (x : Configuration N) : ℝ≥0∞ :=
  ∑ i : Fin N, ∑ j ∈ Finset.univ.filter (fun j : Fin N => i < j),
    coulombKernel (particlePosition x i) (particlePosition x j)

@[expose] noncomputable def attraction {N M : ℕ} (z : Fin M → ℝ≥0)
    (R : Fin M → Position) (x : Configuration N) : ℝ≥0∞ :=
  ∑ i : Fin N, ∑ k : Fin M,
    (z k : ℝ≥0∞) * coulombKernel (particlePosition x i) (R k)

@[expose] noncomputable def nuclearRepulsion {M : ℕ} (z : Fin M → ℝ≥0)
    (R : Fin M → Position) : ℝ≥0∞ :=
  ∑ k : Fin M, ∑ l ∈ Finset.univ.filter (fun l : Fin M => k < l),
    ((z k : ℝ≥0∞) * (z l : ℝ≥0∞)) * coulombKernel (R k) (R l)

@[expose] noncomputable def nearestNucleusDistance {M : ℕ}
    (R : Fin M → Position) (x : Position) : ℝ≥0∞ :=
  ⨅ k : Fin M, ENNReal.ofReal ‖x - R k‖

@[expose] noncomputable def nearestOtherNucleusDistance {M : ℕ}
    (R : Fin M → Position) (k : Fin M) : ℝ≥0∞ :=
  ⨅ l : {l : Fin M // l ≠ k}, ENNReal.ofReal ‖R k - R l‖

@[expose] noncomputable def nearestNucleusControl {N M : ℕ} (Z : ℝ≥0)
    (R : Fin M → Position) (x : Configuration N) : ℝ≥0∞ :=
  (2 * (Z : ℝ≥0∞) + 1) *
    ∑ i : Fin N, (nearestNucleusDistance R (particlePosition x i))⁻¹

@[expose] noncomputable def baxterCorrection {M : ℕ} (Z : ℝ≥0)
    (R : Fin M → Position) : ℝ≥0∞ :=
  (Z : ℝ≥0∞) ^ 2 / 4 * ∑ k : Fin M, (nearestOtherNucleusDistance R k)⁻¹

end LiebThirring

end
