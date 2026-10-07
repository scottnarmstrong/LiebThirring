/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFCubes.IntervalModeDerivatives
public import LiebThirring.TFCubes.IntervalBasis
public import Mathlib.Analysis.Distribution.TestFunction
public import Mathlib.Analysis.Calculus.FDeriv.Star
public import Mathlib.Tactic
public import LiebThirring.TFCubes.CubeCoordinates
public import LiebThirring.TFCubes.CubeMixedModes

/-! # Explicit index equivalences for mixed cube modes -/

@[expose] public section

namespace LiebThirring.TFCubes

abbrev DirichletMixedFrequencyIndex (a : Fin 3) :=
  {k : Fin 3 → ℕ // ∀ i, i ≠ a → 0 < k i}

abbrev NeumannMixedFrequencyIndex (a : Fin 3) :=
  {k : Fin 3 → ℕ // 0 < k a}

def dirichletMixedFrequencyEquivZero :
    DirichletMixedFrequencyIndex 0 ≃ ((ℕ × ℕ+) × ℕ+) where
  toFun k := ((k.1 0, ⟨k.1 1, k.2 1 (by decide)⟩), ⟨k.1 2, k.2 2 (by decide)⟩)
  invFun p := ⟨![p.1.1, p.1.2.1, p.2.1], by
    intro i hi
    fin_cases i
    · exact (hi rfl).elim
    · exact p.1.2.2
    · exact p.2.2⟩
  left_inv k := by apply Subtype.ext; funext i; fin_cases i <;> rfl
  right_inv p := by rcases p with ⟨⟨n, m⟩, r⟩; rfl

def dirichletMixedFrequencyEquivOne :
    DirichletMixedFrequencyIndex 1 ≃ ((ℕ+ × ℕ) × ℕ+) where
  toFun k := ((⟨k.1 0, k.2 0 (by decide)⟩, k.1 1), ⟨k.1 2, k.2 2 (by decide)⟩)
  invFun p := ⟨![p.1.1.1, p.1.2, p.2.1], by
    intro i hi
    fin_cases i
    · exact p.1.1.2
    · exact (hi rfl).elim
    · exact p.2.2⟩
  left_inv k := by apply Subtype.ext; funext i; fin_cases i <;> rfl
  right_inv p := by rcases p with ⟨⟨n, m⟩, r⟩; rfl

def dirichletMixedFrequencyEquivTwo :
    DirichletMixedFrequencyIndex 2 ≃ ((ℕ+ × ℕ+) × ℕ) where
  toFun k := ((⟨k.1 0, k.2 0 (by decide)⟩, ⟨k.1 1, k.2 1 (by decide)⟩), k.1 2)
  invFun p := ⟨![p.1.1.1, p.1.2.1, p.2], by
    intro i hi
    fin_cases i
    · exact p.1.1.2
    · exact p.1.2.2
    · exact (hi rfl).elim⟩
  left_inv k := by apply Subtype.ext; funext i; fin_cases i <;> rfl
  right_inv p := by rcases p with ⟨⟨n, m⟩, r⟩; rfl

def neumannMixedFrequencyEquivZero :
    NeumannMixedFrequencyIndex 0 ≃ ((ℕ+ × ℕ) × ℕ) where
  toFun k := ((⟨k.1 0, k.2⟩, k.1 1), k.1 2)
  invFun p := ⟨![p.1.1.1, p.1.2, p.2], p.1.1.2⟩
  left_inv k := by apply Subtype.ext; funext i; fin_cases i <;> rfl
  right_inv p := by rcases p with ⟨⟨n, m⟩, r⟩; rfl

def neumannMixedFrequencyEquivOne :
    NeumannMixedFrequencyIndex 1 ≃ ((ℕ × ℕ+) × ℕ) where
  toFun k := ((k.1 0, ⟨k.1 1, k.2⟩), k.1 2)
  invFun p := ⟨![p.1.1, p.1.2.1, p.2], p.1.2.2⟩
  left_inv k := by apply Subtype.ext; funext i; fin_cases i <;> rfl
  right_inv p := by rcases p with ⟨⟨n, m⟩, r⟩; rfl

def neumannMixedFrequencyEquivTwo :
    NeumannMixedFrequencyIndex 2 ≃ ((ℕ × ℕ) × ℕ+) where
  toFun k := ((k.1 0, k.1 1), ⟨k.1 2, k.2⟩)
  invFun p := ⟨![p.1.1, p.1.2, p.2.1], p.2.2⟩
  left_inv k := by apply Subtype.ext; funext i; fin_cases i <;> rfl
  right_inv p := by rcases p with ⟨⟨n, m⟩, r⟩; rfl

end LiebThirring.TFCubes

end
