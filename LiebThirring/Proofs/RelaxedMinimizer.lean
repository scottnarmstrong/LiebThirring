/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.ThomasFermi.RelaxedEnergy
import LiebThirring.TFMinimizer.Attainment

/-!
# Unique relaxed Thomas–Fermi minimizer

Quantitative convexity makes minimizing sequences Cauchy in L⁵ᐟ³.
Mass closure and Coulomb continuity yield existence, and strict convexity yields uniqueness.
Source: Lieb–Simon (1977), Theorem II.14; Lieb (1981), Theorem 2.4.
-/

public section

open MeasureTheory
open scoped ENNReal NNReal

namespace LiebThirring.Proofs

theorem exists_unique_tfRelaxedMinimizer {M : ℕ} (a : {a : ℝ // 0 < a})
    (ν : ℝ≥0) (z : Fin M → ℝ≥0) (R : Fin M → Position) :
    ∃! ρ : TFDensity, tfMass ρ ≤ (ν : ℝ) ∧
      (tfFunctional a z R ρ : EReal) = tfRelaxedEnergy a ν z R :=
  LiebThirring.TFMinimizer.exists_unique_tfRelaxedMinimizer a ν z R

end LiebThirring.Proofs

end
