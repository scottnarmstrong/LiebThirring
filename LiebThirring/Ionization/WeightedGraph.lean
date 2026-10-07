/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Sobolev.LipschitzProductRule

/-! # Graph continuity of the weighted kinetic cross term -/

public section

open MeasureTheory Filter
open scoped Topology NNReal

namespace LiebThirring
open Sobolev

/-- A fixed bounded Lipschitz multiplier preserves convergence of each product derivative. -/
theorem tendsto_lipschitzProductDerivative {N q : ℕ}
    (b : Configuration N → ℝ) (B : ℝ) (hB : ∀ x, ‖b x‖ ≤ B)
    (C : ℝ≥0) (hb : LipschitzWith C b) (a : Fin N × Fin 3)
    {u g : State N q} {uSeq gSeq : ℕ → State N q}
    (hu : Tendsto uSeq atTop (𝓝 u)) (hg : Tendsto gSeq atTop (𝓝 g)) :
    Tendsto (fun n => lipschitzProductDerivative b B hB C hb a (uSeq n) (gSeq n))
      atTop (𝓝 (lipschitzProductDerivative b B hB C hb a u g)) := by
  have h₁ (v : State N q) : lipschitzBoundedSMul b B hB hb v =
      boundedSMul (fun x => (b x : ℂ)) v B (fun x => by simpa using hB x)
        (Complex.measurable_ofReal.comp hb.continuous.measurable).aestronglyMeasurable := by
    apply Lp.ext
    exact (lipschitzBoundedSMul_coeFn b B hB hb v).trans
      (boundedSMul_coeFn _ _ _ _ _).symm
  have h₂ (v : State N q) : lipschitzDerivativeSMul b C hb a v =
      boundedSMul (fun x => (lipschitzDirectionalDerivative b a x : ℂ)) v C
        (fun x => by simpa using norm_lipschitzDirectionalDerivative_le b C hb a x)
        (Complex.measurable_ofReal.comp
          (lipschitzDirectionalDerivative_measurable b a)).aestronglyMeasurable := by
    apply Lp.ext
    exact (lipschitzDerivativeSMul_coeFn b C hb a v).trans
      (boundedSMul_coeFn _ _ _ _ _).symm
  simp only [lipschitzProductDerivative, h₁, h₂]
  exact (tendsto_boundedSMul _ _ _ _ hg).add (tendsto_boundedSMul _ _ _ _ hu)

/-- The selected kinetic pairing is continuous under simultaneous state and derivative limits. -/
theorem tendsto_selected_multiplier_cross {N q : ℕ}
    (i : Fin N) (b : Configuration N → ℝ) (B : ℝ) (hB : ∀ x, ‖b x‖ ≤ B)
    (C : ℝ≥0) (hb : LipschitzWith C b)
    {u : State N q} {g : (Fin N × Fin 3) → State N q}
    {uSeq : ℕ → State N q} {gSeq : ℕ → (Fin N × Fin 3) → State N q}
    (hu : Tendsto uSeq atTop (𝓝 u))
    (hg : ∀ a, Tendsto (fun n => gSeq n a) atTop (𝓝 (g a))) :
    Tendsto (fun n => (∑ a : Fin 3, inner ℂ
      (lipschitzProductDerivative b B hB C hb (i, a) (uSeq n) (gSeq n (i, a)))
      (gSeq n (i, a))).re) atTop
      (𝓝 ((∑ a : Fin 3, inner ℂ
        (lipschitzProductDerivative b B hB C hb (i, a) u (g (i, a)))
        (g (i, a))).re)) := by
  apply Complex.continuous_re.continuousAt.tendsto.comp
  exact tendsto_finsetSum _ (fun a _ =>
    (tendsto_lipschitzProductDerivative b B hB C hb (i, a) hu (hg (i, a))).inner (hg (i, a)))

end LiebThirring

end
