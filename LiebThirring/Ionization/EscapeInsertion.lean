/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Ionization.EscapeWedge

/-! # Inserting a particle before the successor coordinates -/

public section

open MeasureTheory WithLp

namespace LiebThirring

/-- Put the selected particle at zero and the old particles at successors. -/
@[expose] def escapeInsertPositions {N : ℕ} (p : Position) (y : Configuration N) :
    Configuration (N + 1) :=
  toLp 2 (fun ja => Fin.cases (p ja.2) (fun j => y (j, ja.2)) ja.1)

/-- Coordinate partition underlying the selected-zero insertion. -/
@[expose] def escapeInsertionIndexEquiv (N : ℕ) :
    (Fin (N + 1) × Fin 3) ≃ (Fin 3 ⊕ (Fin N × Fin 3)) where
  toFun ja := Fin.cases (Sum.inl ja.2) (fun j => Sum.inr (j, ja.2)) ja.1
  invFun := Sum.elim (fun a => (0, a)) (fun ja => (ja.1.succ, ja.2))
  left_inv := by
    rintro ⟨j, a⟩
    exact Fin.cases rfl (fun _ => rfl) j
  right_inv := by
    intro ja
    cases ja with
    | inl a => rfl
    | inr ja => rfl

/-- Selected-zero insertion as a measurable equivalence of actual configurations. -/
@[expose] noncomputable def escapeInsertionMeasurableEquiv (N : ℕ) :
    (Position × Configuration N) ≃ᵐ Configuration (N + 1) :=
  ((MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).symm.prodCongr
    (MeasurableEquiv.toLp 2 ((Fin N × Fin 3) → ℝ)).symm).trans
  ((MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin 3 ⊕ (Fin N × Fin 3) => ℝ)).symm.trans
    ((MeasurableEquiv.piCongrLeft (fun _ : Fin (N + 1) × Fin 3 => ℝ)
      (escapeInsertionIndexEquiv N).symm).trans (MeasurableEquiv.toLp 2 _)))

theorem escapeInsertionMeasurableEquiv_apply {N : ℕ} (z : Position × Configuration N) :
    escapeInsertionMeasurableEquiv N z = escapeInsertPositions z.1 z.2 := by
  ext ja
  rcases ja with ⟨j, a⟩
  exact Fin.cases rfl (fun _ => rfl) j

theorem measurePreserving_escapeInsertion (N : ℕ) :
    MeasurePreserving (escapeInsertionMeasurableEquiv N) volume volume := by
  exact ((PiLp.volume_preserving_ofLp (Fin 3)).prod
    (PiLp.volume_preserving_ofLp (Fin N × Fin 3))).trans
    ((volume_measurePreserving_sumPiEquivProdPi_symm _).trans
      ((volume_measurePreserving_piCongrLeft _ (escapeInsertionIndexEquiv N).symm).trans
        (PiLp.volume_preserving_toLp (Fin (N + 1) × Fin 3))))

@[simp] theorem particlePosition_escapeInsertPositions_zero {N : ℕ}
    (p : Position) (y : Configuration N) : particlePosition (escapeInsertPositions p y) 0 = p := by
  ext a
  rfl

@[simp] theorem particlePosition_escapeInsertPositions_succ {N : ℕ}
    (p : Position) (y : Configuration N) (j : Fin N) :
    particlePosition (escapeInsertPositions p y) j.succ = particlePosition y j := by
  ext a
  rfl

@[simp] theorem escapeOmitPositions_escapeInsertPositions {N : ℕ}
    (p : Position) (y : Configuration N) : escapeOmitPositions 0 (escapeInsertPositions p y) = y := by
  ext ja
  simp only [escapeOmitPositions, Equiv.swap_self, Equiv.refl_apply,
    escapeInsertPositions, PiLp.toLp_apply, Fin.cases_succ]

theorem escapeInsertPositions_particlePosition_omit {N : ℕ} (x : Configuration (N + 1)) :
    escapeInsertPositions (particlePosition x 0) (escapeOmitPositions 0 x) = x := by
  ext ja
  rcases ja with ⟨j, a⟩
  refine Fin.cases ?_ (fun k => ?_) j
  · rfl
  · simp only [escapeInsertPositions, PiLp.toLp_apply, Fin.cases_succ,
      escapeOmitPositions, Equiv.swap_self, Equiv.refl_apply]

/-- Spin counterpart of selected-zero spatial insertion. -/
@[expose] def escapeInsertSpins {N q : ℕ} (t : Fin q) (s : SpinLabels N q) :
    SpinLabels (N + 1) q := Fin.cases t s

/-- A spin configuration is exactly its zero spin and successor spins. -/
@[expose] def escapeInsertionSpinEquiv (N q : ℕ) :
    (Fin q × SpinLabels N q) ≃ SpinLabels (N + 1) q where
  toFun z := escapeInsertSpins z.1 z.2
  invFun s := (s 0, escapeOmitSpins 0 s)
  left_inv := by
    rintro ⟨t, s⟩
    apply Prod.ext
    · rfl
    · funext j
      simp only [escapeOmitSpins, escapeInsertSpins, Equiv.swap_self,
        Equiv.refl_apply, Fin.cases_succ]
  right_inv := by
    intro s
    funext j
    refine Fin.cases ?_ (fun k => ?_) j
    · rfl
    · simp only [escapeOmitSpins, escapeInsertSpins, Equiv.swap_self,
        Equiv.refl_apply, Fin.cases_succ]

@[simp] theorem escapeOmitSpins_escapeInsertSpins {N q : ℕ} (t : Fin q)
    (s : SpinLabels N q) : escapeOmitSpins 0 (escapeInsertSpins t s) = s := by
  funext j
  simp only [escapeOmitSpins, Equiv.swap_self, Equiv.refl_apply, escapeInsertSpins, Fin.cases_succ]

end LiebThirring

end
