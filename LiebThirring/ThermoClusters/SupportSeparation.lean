/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.ThermoClusters.TensorExpectations
public import LiebThirring.Variational.TrialSlater

/-!
# Spatial separation of compact joint cluster trials

The finite union of all particle-coordinate images of a compact joint support
is compact. Supports confined to disjoint spatial regions therefore have a
positive uniform gap, even when the boundaries of those regions touch. The
actual one-body measures are concentrated on these coordinate images, giving
finite cross Coulomb expectations for all four species pairs.
compact-support separation argument.
-/

public section
open MeasureTheory WithLp Set
open scoped ENNReal NNReal SchwartzMap
namespace LiebThirring

/-- All spatial positions attained by any particle on the closed joint trial support. -/
@[expose] noncomputable def clusterSpatialSupport {N M q : ℕ}
    (f : 𝓢(QuantumConfiguration N M, SpinAmplitudes N q)) : Set Position :=
  (⋃ i : Fin N, (fun X : QuantumConfiguration N M => particlePosition X.fst i) '' tsupport f) ∪
    (⋃ k : Fin M, (fun X : QuantumConfiguration N M => particlePosition X.snd k) '' tsupport f)

/-- The collected coordinate images of a compact joint support are compact. -/
theorem isCompact_clusterSpatialSupport {N M q : ℕ}
    (f : 𝓢(QuantumConfiguration N M, SpinAmplitudes N q)) (hf : IsCompact (tsupport f)) :
    IsCompact (clusterSpatialSupport f) := by
  apply IsCompact.union
  · exact isCompact_iUnion (fun i => hf.image ((contDiff_particlePosition i).continuous.comp
      (WithLp.fstL 2 ℝ (Configuration N) (Configuration M)).continuous))
  · exact isCompact_iUnion (fun k => hf.image ((contDiff_particlePosition k).continuous.comp
      (WithLp.sndL 2 ℝ (Configuration N) (Configuration M)).continuous))

/-- Confinement of every particle confines the collected spatial support. -/
theorem clusterSpatialSupport_subset {N M q : ℕ}
    (f : 𝓢(QuantumConfiguration N M, SpinAmplitudes N q)) (Ω : Set Position)
    (hf : tsupport f ⊆ {X | (∀ i : Fin N, particlePosition X.fst i ∈ Ω) ∧
      (∀ k : Fin M, particlePosition X.snd k ∈ Ω)}) :
    clusterSpatialSupport f ⊆ Ω := by
  intro x hx
  rcases hx with hx | hx
  · obtain ⟨i, X, hX, rfl⟩ := mem_iUnion.mp hx
    exact (hf hX).1 i
  · obtain ⟨k, X, hX, rfl⟩ := mem_iUnion.mp hx
    exact (hf hX).2 k

/-- The actual joint probability vanishes off the closed support of its Schwartz representative. -/
theorem ae_quantumProbabilityMeasure_mem_tsupport {N M q : ℕ}
    (f : 𝓢(QuantumConfiguration N M, SpinAmplitudes N q)) :
    ∀ᵐ X ∂quantumProbabilityMeasure (f.toLp 2 volume), X ∈ tsupport f := by
  rw [quantumProbabilityMeasure_schwartz,
    ae_withDensity_iff (f.continuous.measurable.nnnorm.coe_nnreal_ennreal.pow_const 2)]
  apply Filter.Eventually.of_forall
  intro X hX
  apply subset_tsupport
  intro hf
  apply hX
  simp only [hf, nnnorm_zero, ENNReal.coe_zero, zero_pow (by decide : 2 ≠ 0)]

/-- The actual electronic one-body measure is concentrated on the collected spatial support. -/
theorem ae_quantumElectronMeasure_mem_clusterSpatialSupport {N M q : ℕ}
    (f : 𝓢(QuantumConfiguration N M, SpinAmplitudes N q)) (hf : IsCompact (tsupport f)) :
    ∀ᵐ x ∂quantumElectronMeasure (f.toLp 2 volume), x ∈ clusterSpatialSupport f := by
  classical
  unfold quantumElectronMeasure
  rw [ae_finsetSum_measure_iff]
  intro i _
  have hm := (contDiff_particlePosition i).continuous.measurable.comp
    (WithLp.fstL 2 ℝ (Configuration N) (Configuration M)).continuous.measurable
  apply (ae_map_iff hm.aemeasurable (isCompact_clusterSpatialSupport f hf).measurableSet).2
  filter_upwards [ae_quantumProbabilityMeasure_mem_tsupport f] with X hX
  exact Or.inl (mem_iUnion.mpr ⟨i, X, hX, rfl⟩)

/-- The actual nuclear one-body measure is concentrated on the collected spatial support. -/
theorem ae_quantumNuclearMeasure_mem_clusterSpatialSupport {N M q : ℕ}
    (f : 𝓢(QuantumConfiguration N M, SpinAmplitudes N q)) (hf : IsCompact (tsupport f)) :
    ∀ᵐ x ∂quantumNuclearMeasure (f.toLp 2 volume), x ∈ clusterSpatialSupport f := by
  classical
  unfold quantumNuclearMeasure
  rw [ae_finsetSum_measure_iff]
  intro k _
  have hm := (contDiff_particlePosition k).continuous.measurable.comp
    (WithLp.sndL 2 ℝ (Configuration N) (Configuration M)).continuous.measurable
  apply (ae_map_iff hm.aemeasurable (isCompact_clusterSpatialSupport f hf).measurableSet).2
  filter_upwards [ae_quantumProbabilityMeasure_mem_tsupport f] with X hX
  exact Or.inr (mem_iUnion.mpr ⟨k, X, hX, rfl⟩)

/-- Compact disjoint spatial sets have a positive uniform cross-distance, including empty sets. -/
theorem exists_pos_le_norm_sub_of_isCompact_disjoint {s t : Set Position}
    (hs : IsCompact s) (ht : IsCompact t) (hst : Disjoint s t) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ s, ∀ y ∈ t, ε ≤ ‖x-y‖ := by
  obtain ⟨r, hr, hsep⟩ := Metric.exists_pos_forall_lt_edist hs ht.isClosed hst
  refine ⟨r, hr, fun x hx y hy => ?_⟩
  have hxy : r < nndist x y := by
    simpa only [edist_nndist, ENNReal.coe_lt_coe] using hsep x hx y hy
  exact (show (r : ℝ) < dist x y from hxy).le

/-- Finite measures concentrated on compact disjoint sets have finite cross Coulomb interaction. -/
theorem clusterCoulombInteraction_lt_top_of_compact_disjoint
    (μ ν : Measure Position) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {s t : Set Position} (hs : IsCompact s) (ht : IsCompact t) (hst : Disjoint s t)
    (hμ : ∀ᵐ x ∂μ, x ∈ s) (hν : ∀ᵐ y ∂ν, y ∈ t) :
    clusterCoulombInteraction μ ν < ⊤ := by
  obtain ⟨ε, hε, hsep⟩ := exists_pos_le_norm_sub_of_isCompact_disjoint hs ht hst
  have hp : ∀ᵐ Z : Position × Position ∂μ.prod ν, ε ≤ ‖Z.1-Z.2‖ := by
    apply (Measure.ae_prod_iff_ae_ae
      (measurableSet_le measurable_const (continuous_fst.sub continuous_snd).norm.measurable)).2
    filter_upwards [hμ] with x hx
    filter_upwards [hν] with y hy
    exact hsep x hx y hy
  unfold clusterCoulombInteraction
  calc
    _ ≤ ∫⁻ _Z : Position × Position, (ENNReal.ofReal ε)⁻¹ ∂μ.prod ν := by
      apply lintegral_mono_ae
      filter_upwards [hp] with Z hZ
      exact ENNReal.inv_le_inv.mpr (ENNReal.ofReal_le_ofReal hZ)
    _ = (ENNReal.ofReal ε)⁻¹ * (μ.prod ν) univ := lintegral_const _
    _ < ⊤ := ENNReal.mul_lt_top (ENNReal.inv_lt_top.mpr (ENNReal.ofReal_pos.mpr hε))
      (measure_lt_top (μ.prod ν) univ)

/-- All four actual one-body cross interactions of separated compact clusters are finite. -/
theorem four_clusterCoulombInteractions_schwartz_lt_top {N₁ M₁ N₂ M₂ q : ℕ}
    (f : 𝓢(QuantumConfiguration N₁ M₁, SpinAmplitudes N₁ q))
    (g : 𝓢(QuantumConfiguration N₂ M₂, SpinAmplitudes N₂ q))
    (hf : IsCompact (tsupport f)) (hg : IsCompact (tsupport g))
    (Ω Ω' : Set Position) (hΩ : Disjoint Ω Ω')
    (hfs : tsupport f ⊆ {X | (∀ i, particlePosition X.fst i ∈ Ω) ∧
      (∀ k, particlePosition X.snd k ∈ Ω)})
    (hgs : tsupport g ⊆ {X | (∀ i, particlePosition X.fst i ∈ Ω') ∧
      (∀ k, particlePosition X.snd k ∈ Ω')}) :
    clusterCoulombInteraction (quantumElectronMeasure (f.toLp 2 volume))
      (quantumElectronMeasure (g.toLp 2 volume)) < ⊤ ∧
    clusterCoulombInteraction (quantumElectronMeasure (f.toLp 2 volume))
      (quantumNuclearMeasure (g.toLp 2 volume)) < ⊤ ∧
    clusterCoulombInteraction (quantumNuclearMeasure (f.toLp 2 volume))
      (quantumElectronMeasure (g.toLp 2 volume)) < ⊤ ∧
    clusterCoulombInteraction (quantumNuclearMeasure (f.toLp 2 volume))
      (quantumNuclearMeasure (g.toLp 2 volume)) < ⊤ := by
  have hdis := hΩ.mono (clusterSpatialSupport_subset f Ω hfs)
    (clusterSpatialSupport_subset g Ω' hgs)
  have hfc := isCompact_clusterSpatialSupport f hf
  have hgc := isCompact_clusterSpatialSupport g hg
  have hfe := ae_quantumElectronMeasure_mem_clusterSpatialSupport f hf
  have hfn := ae_quantumNuclearMeasure_mem_clusterSpatialSupport f hf
  have hge := ae_quantumElectronMeasure_mem_clusterSpatialSupport g hg
  have hgn := ae_quantumNuclearMeasure_mem_clusterSpatialSupport g hg
  exact ⟨clusterCoulombInteraction_lt_top_of_compact_disjoint _ _ hfc hgc hdis hfe hge,
    clusterCoulombInteraction_lt_top_of_compact_disjoint _ _ hfc hgc hdis hfe hgn,
    clusterCoulombInteraction_lt_top_of_compact_disjoint _ _ hfc hgc hdis hfn hge,
    clusterCoulombInteraction_lt_top_of_compact_disjoint _ _ hfc hgc hdis hfn hgn⟩

end LiebThirring
end
