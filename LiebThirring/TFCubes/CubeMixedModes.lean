/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFCubes.CubeProductTests

/-! # Mixed sine/cosine modes for the Neumann cube gradient

Differentiating a cosine state changes exactly one coordinate to a positive
sine frequency. The two spectator coordinates retain their cosine factors.
-/

@[expose] public section

namespace LiebThirring.TFCubes

/-- Positive active frequency, arbitrary nonnegative spectator frequencies, and spin. -/
abbrev NeumannMixedCubeModeIndex (q : ℕ) (a : Fin 3) :=
  {k : Fin 3 → ℕ // 0 < k a} × Fin q

/-- The literal positive sine in the active coordinate and cosines in the spectators. -/
noncomputable def neumannMixedCubeSpatialMode {q : ℕ} (ℓ : {ℓ : ℝ // 0 < ℓ})
    (b : Position) (a : Fin 3) (p : NeumannMixedCubeModeIndex q a) : Position → ℂ :=
  neumannCubeMixedTestLimit ℓ b p.1.val a ⟨p.1.val a, p.1.property⟩

end LiebThirring.TFCubes

end
