/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Sobolev.FormGraph

/-! # Closed weak graphs in almost-everywhere L² slices -/

public section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace LiebThirring.Variational

local instance : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨ENNReal.ofNat_ne_top⟩

/-- An L² limit of fields taking values in the weak Sobolev graph still takes values in that graph
almost everywhere.  The proof selects a single pointwise-a.e. convergent subsequence and uses the
closedness of the weak derivative graph. -/
theorem mem_formGraph_ae_of_tendsto_L2 {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [SFinite μ] {N q : ℕ}
    (v : ℕ → Lp (Sobolev.FormGraphAmbient N q) 2 μ)
    (u : Lp (Sobolev.FormGraphAmbient N q) 2 μ)
    (hv : ∀ n, ∀ᵐ x ∂μ, v n x ∈ Sobolev.formGraph N q)
    (hvu : Tendsto v atTop (𝓝 u)) :
    ∀ᵐ x ∂μ, u x ∈ Sobolev.formGraph N q := by
  obtain ⟨ns, -, hpoint⟩ :=
    (tendstoInMeasure_of_tendsto_Lp hvu).exists_seq_tendsto_ae
  have hall : ∀ᵐ x ∂μ, ∀ n, v n x ∈ Sobolev.formGraph N q :=
    ae_all_iff.mpr hv
  filter_upwards [hpoint, hall] with x hx hmem
  exact (Sobolev.formGraph_isClosed N q).mem_of_tendsto hx
    (Eventually.of_forall fun n => hmem (ns n))

end LiebThirring.Variational

end
