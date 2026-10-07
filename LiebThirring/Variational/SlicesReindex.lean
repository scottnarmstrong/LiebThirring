/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Sobolev.Regrouping
public import LiebThirring.Kinetic.CurryingState

/-!
# Reindexing residual particle states

Residual configurations are transported to literal `State k q` carriers only through an
explicit ordering equivalence. This avoids treating `OtherConfiguration i` as definitionally equal
to `Configuration (N - 1)`.
-/

@[expose] public section

open MeasureTheory WithLp
open scoped ENNReal

namespace LiebThirring.Variational

local instance : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨ENNReal.ofNat_ne_top⟩

/-- Reindex residual spin labels through an ordering of the residual particles. -/
def residualSpinLabelEquiv {N k q : ℕ} (i : Fin N)
    (e : Fin k ≃ {j : Fin N // j ≠ i}) : OtherSpinLabels i q ≃ SpinLabels k q where
  toFun s j := s (e j)
  invFun s j := s (e.symm j)
  left_inv s := by funext j; simp
  right_inv s := by funext j; simp

/-- Reindex the residual spin amplitude through an explicit ordering of the remaining particles. -/
noncomputable def residualSpinReindex {N k q : ℕ} (i : Fin N)
    (e : Fin k ≃ {j : Fin N // j ≠ i}) :
    EuclideanSpace ℂ (OtherSpinLabels i q) ≃ₗᵢ[ℂ] SpinAmplitudes k q :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (residualSpinLabelEquiv i e)

/-- Reindex a residual L² state through an explicit ordering of the remaining particles. -/
noncomputable def residualStateReindex {N k q : ℕ} (i : Fin N)
    (e : Fin k ≃ {j : Fin N // j ≠ i}) : RestState i q ≃ₗᵢ[ℂ] State k q :=
  (l2PullbackEquiv (E := EuclideanSpace ℂ (OtherSpinLabels i q))
    (Sobolev.configurationReindexMeasurableEquiv e)
    (Sobolev.measurePreserving_configurationReindex e)).trans
  (l2TargetEquiv (volume : Measure (Configuration k)) (residualSpinReindex i e))

/-- Representative formula for residual-state reindexing. -/
theorem residualStateReindex_ae {N k q : ℕ} (i : Fin N)
    (e : Fin k ≃ {j : Fin N // j ≠ i}) (u : RestState i q) :
    ∀ᵐ x : Configuration k, ∀ s : SpinLabels k q,
      residualStateReindex i e u x s = u (Sobolev.configurationReindexMeasurableEquiv e x)
        (fun j => s (e.symm j)) := by
  filter_upwards [l2TargetEquiv_ae (volume : Measure (Configuration k))
      (residualSpinReindex i e)
      (l2PullbackEquiv (E := EuclideanSpace ℂ (OtherSpinLabels i q))
        (Sobolev.configurationReindexMeasurableEquiv e)
        (Sobolev.measurePreserving_configurationReindex e) u),
    l2PullbackEquiv_ae (E := EuclideanSpace ℂ (OtherSpinLabels i q))
      (Sobolev.configurationReindexMeasurableEquiv e)
      (Sobolev.measurePreserving_configurationReindex e) u] with x ht hx
  intro s
  change ((l2TargetEquiv (volume : Measure (Configuration k)) (residualSpinReindex i e))
      ((l2PullbackEquiv (E := EuclideanSpace ℂ (OtherSpinLabels i q))
        (Sobolev.configurationReindexMeasurableEquiv e)
        (Sobolev.measurePreserving_configurationReindex e)) u) x) s = _
  rw [ht, hx]
  simp [residualSpinReindex, residualSpinLabelEquiv]

end LiebThirring.Variational

end
