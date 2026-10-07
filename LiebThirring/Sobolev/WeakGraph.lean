/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Sobolev.WeakDerivative
import Mathlib.Analysis.Normed.Lp.SmoothApprox

/-!
# The closed graph of a weak coordinate derivative

Weak coordinate derivatives pass to simultaneous L² limits and are unique. Consequently their
graph is a closed complex linear subspace of the product of two copies of the state space, hence is
complete in the product Hilbert norm. This module does not identify that graph norm with the
Fourier kinetic energy.
-/

public section

open MeasureTheory
open scoped ContDiff

namespace LiebThirring.Sobolev

/-- A compact smooth test function, regarded as an L² state. -/
noncomputable def testFunctionL2 {N q : ℕ} (η : Configuration N → SpinAmplitudes N q)
    (hηc : HasCompactSupport η) (hηs : ContDiff ℝ ∞ η) : State N q :=
  (hηs.continuous.memLp_of_hasCompactSupport hηc).toLp η

theorem inner_testFunctionL2 {N q : ℕ} (η : Configuration N → SpinAmplitudes N q)
    (hηc : HasCompactSupport η) (hηs : ContDiff ℝ ∞ η) (u : State N q) :
    inner ℂ (testFunctionL2 η hηc hηs) u = ∫ x, inner ℂ (η x) (u x) := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(hηs.continuous.memLp_of_hasCompactSupport hηc).coeFn_toLp] with x hx
  change inner ℂ ((hηs.continuous.memLp_of_hasCompactSupport hηc).toLp η x) (u x) = _
  rw [hx]

/-- Reformulation of the weak derivative identity as an identity in the L² inner product. -/
theorem hasWeakDerivative_iff_inner {N q : ℕ} {a : Fin N × Fin 3} {u g : State N q} :
    HasWeakDerivative a u g ↔ ∀ η : Configuration N → SpinAmplitudes N q,
      ∀ hηc : HasCompactSupport η, ∀ hηs : ContDiff ℝ ∞ η,
        inner ℂ (testFunctionL2 η hηc hηs) g =
          -inner ℂ (testFunctionL2 (fun x ↦ fderiv ℝ η x (coordinateVector a))
            (HasCompactSupport.fderiv_apply ℝ hηc (coordinateVector a))
            ((hηs.fderiv_right (by simp)).clm_apply contDiff_const)) u := by
  constructor
  · intro h η hηc hηs
    rw [inner_testFunctionL2, inner_testFunctionL2]
    exact h η hηc hηs
  · intro h η hηc hηs
    simpa only [inner_testFunctionL2] using h η hηc hηs

/-- Weak coordinate derivatives are preserved by simultaneous L² limits. -/
theorem HasWeakDerivative.closed_of_tendsto {N q : ℕ} {a : Fin N × Fin 3}
    {u g : State N q} {uSeq gSeq : ℕ → State N q}
    (hderiv : ∀ n, HasWeakDerivative a (uSeq n) (gSeq n))
    (hu : Filter.Tendsto uSeq Filter.atTop (nhds u))
    (hg : Filter.Tendsto gSeq Filter.atTop (nhds g)) : HasWeakDerivative a u g := by
  rw [hasWeakDerivative_iff_inner]
  intro η hηc hηs
  let dη := testFunctionL2 (fun x ↦ fderiv ℝ η x (coordinateVector a))
    (HasCompactSupport.fderiv_apply ℝ hηc (coordinateVector a))
    ((hηs.fderiv_right (by simp)).clm_apply contDiff_const)
  have heq : ∀ n, inner ℂ (testFunctionL2 η hηc hηs) (gSeq n) =
      -inner ℂ dη (uSeq n) := by
    intro n
    exact hasWeakDerivative_iff_inner.mp (hderiv n) η hηc hηs
  exact tendsto_nhds_unique
    ((tendsto_const_nhds.inner hg).congr' (Filter.Eventually.of_forall heq))
    ((tendsto_const_nhds.inner hu).neg)

/-- An L² weak coordinate derivative is unique. -/
theorem HasWeakDerivative.unique {N q : ℕ} {a : Fin N × Fin 3} {u g h : State N q}
    (hg : HasWeakDerivative a u g) (hh : HasWeakDerivative a u h) : g = h := by
  apply (Lp.dense_hasCompactSupport_contDiff (E := Configuration N)
    (F := SpinAmplitudes N q) (μ := volume) (p := 2) (by simp)).eq_of_inner_right ℂ
  intro φ hφ
  obtain ⟨η, hφη, hηc, hηs⟩ := hφ
  rw [show inner ℂ φ g = inner ℂ (testFunctionL2 η hηc hηs) g by
    apply congrArg (fun z ↦ inner ℂ z g)
    apply Lp.ext
    filter_upwards [hφη, (hηs.continuous.memLp_of_hasCompactSupport hηc).coeFn_toLp] with x h1 h2
    exact h1.trans h2.symm]
  rw [show inner ℂ φ h = inner ℂ (testFunctionL2 η hηc hηs) h by
    apply congrArg (fun z ↦ inner ℂ z h)
    apply Lp.ext
    filter_upwards [hφη, (hηs.continuous.memLp_of_hasCompactSupport hηc).coeFn_toLp] with x h1 h2
    exact h1.trans h2.symm]
  rw [hasWeakDerivative_iff_inner.mp hg η hηc hηs,
    hasWeakDerivative_iff_inner.mp hh η hηc hηs]

/-- The set of pairs related by a weak coordinate derivative is closed. -/
theorem isClosed_weakDerivativeGraph {N q : ℕ} (a : Fin N × Fin 3) :
    IsClosed {p : State N q × State N q | HasWeakDerivative a p.1 p.2} := by
  apply IsSeqClosed.isClosed
  intro p x hp hx
  exact HasWeakDerivative.closed_of_tendsto (fun n ↦ hp n)
    ((continuous_fst.tendsto x).comp hx) ((continuous_snd.tendsto x).comp hx)

/-- The complex linear graph of the weak derivative in coordinate `a`. -/
@[expose] noncomputable def weakDerivativeGraph {N q : ℕ} (a : Fin N × Fin 3) :
    Submodule ℂ (State N q × State N q) where
  carrier := {p | HasWeakDerivative a p.1 p.2}
  zero_mem' := by
    change HasWeakDerivative a 0 0
    rw [hasWeakDerivative_iff_inner]
    simp
  add_mem' := by
    intro p r hp hr
    change HasWeakDerivative a p.1 p.2 at hp
    change HasWeakDerivative a r.1 r.2 at hr
    change HasWeakDerivative a (p + r).1 (p + r).2
    rw [hasWeakDerivative_iff_inner] at hp hr ⊢
    intro η hηc hηs
    rw [Prod.fst_add, Prod.snd_add, inner_add_right, inner_add_right, hp η hηc hηs,
      hr η hηc hηs, neg_add]
  smul_mem' := by
    intro c p hp
    change HasWeakDerivative a p.1 p.2 at hp
    change HasWeakDerivative a (c • p).1 (c • p).2
    rw [hasWeakDerivative_iff_inner] at hp ⊢
    intro η hηc hηs
    change inner ℂ (testFunctionL2 η hηc hηs) (c • p.2) =
      -inner ℂ (testFunctionL2 (fun x ↦ fderiv ℝ η x (coordinateVector a))
        (HasCompactSupport.fderiv_apply ℝ hηc (coordinateVector a))
        ((hηs.fderiv_right (by simp)).clm_apply contDiff_const)) (c • p.1)
    simpa only [inner_smul_right, map_neg, mul_neg] using congrArg (c * ·) (hp η hηc hηs)

theorem weakDerivativeGraph_isClosed {N q : ℕ} (a : Fin N × Fin 3) :
    IsClosed (weakDerivativeGraph (q := q) a : Set (State N q × State N q)) :=
  isClosed_weakDerivativeGraph a

end LiebThirring.Sobolev

end
