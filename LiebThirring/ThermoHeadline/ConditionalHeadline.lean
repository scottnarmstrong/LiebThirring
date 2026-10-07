/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.ThermoHeadline.PhysicalLaws
public import LiebThirring.ThermoHeadline.VolumeBridge
public import LiebThirring.ThermoHeadline.AllRadii
public import LiebThirring.Thermodynamic.DensitySequenceExists

/-!
# Thermodynamic limit under neutral packing

The thermodynamic limit includes zero density, every radius/count sequence,
and extended-real division. Assuming integer neutral variational packing,
the proof combines quantum stability, domain inclusion, translation,
energy finiteness and convergence of normalized ball energies.
-/

public section

open Metric Set Filter Topology Finset
open scoped NNReal
open LiebThirring.ThermoBounds

namespace LiebThirring.ThermoHeadline

/-- Thermodynamic energy-density limit under integer neutral packing. -/
theorem exists_unique_thermodynamic_energy_density_of_neutral_packing
    (q : ℕ) (hq : 1 ≤ q) (z : ℕ) (hz : 1 ≤ z)
    (m : {m : ℝ≥0 // 0 < m})
    (hpacking : ∀ (ι : Type) (Ω : Set Position) (s : Finset ι)
      (c : ι → Position) (r : ι → ℝ) (n : ι → ℕ),
      IsOpen Ω → Ω.Nonempty → Bornology.IsBounded Ω →
      (∀ i ∈ s, 0 < r i) → (∀ i ∈ s, ball (c i) (r i) ⊆ Ω) →
      (s : Set ι).PairwiseDisjoint (fun i => ball (c i) (r i)) →
      physicalNeutralEnergy q z m Ω (∑ i ∈ s, n i) ≤
        ∑ i ∈ s, physicalNeutralEnergy q z m (ball (c i) (r i)) (n i)) :
    ∃! e : ℝ≥0 → ℝ,
      e 0 = 0 ∧ Continuous e ∧
      (∀ (ρ₁ ρ₂ : ℝ≥0) (t : ℝ≥0), t ≤ 1 →
        e (t * ρ₁ + (1 - t) * ρ₂) ≤
          (t : ℝ) * e ρ₁ + (1 - (t : ℝ)) * e ρ₂) ∧
      ∀ (ρ : ℝ≥0) (L : ℕ → {L : ℝ // 0 < L}) (M : ℕ → ℕ),
        Filter.Tendsto (fun j => (L j).val) Filter.atTop Filter.atTop →
        Filter.Tendsto (fun j => (M j : ℝ) / ballVolume (L j))
          Filter.atTop (nhds (ρ : ℝ)) →
        Filter.Tendsto
          (fun j => confinedGroundStateEnergy (z * M j) (M j) q z m (L j) /
            (ballVolume (L j) : EReal))
          Filter.atTop (nhds (e ρ : EReal)) := by
  obtain ⟨A, _, hlower⟩ := exists_physicalNeutralEnergy_ball_lower_bound q hq z hz m
  have hmono : ∀ Ω Ω', IsOpen Ω → Ω.Nonempty → Bornology.IsBounded Ω →
      IsOpen Ω' → Ω'.Nonempty → Bornology.IsBounded Ω' →
      Ω ⊆ Ω' → ∀ n, physicalNeutralEnergy q z m Ω' n ≤
        physicalNeutralEnergy q z m Ω n := by
    intro Ω Ω' hopen hne _ hopen' hne' _ hsub n
    exact physicalNeutralEnergy_antitone q hq z hz m hopen hne hopen' hne' hsub n
  have htranslation := physicalNeutralEnergy_ball_center q z m
  obtain ⟨e, he0, hec, heconv, helimits⟩ :=
    exists_all_ball_limits_of_integer_physics hlower hmono htranslation hpacking
  have he : e 0 = 0 ∧ Continuous e ∧
      (∀ (ρ₁ ρ₂ : ℝ≥0) (t : ℝ≥0), t ≤ 1 →
        e (t * ρ₁ + (1 - t) * ρ₂) ≤
          (t : ℝ) * e ρ₁ + (1 - (t : ℝ)) * e ρ₂) ∧
      ∀ (ρ : ℝ≥0) (L : ℕ → {L : ℝ // 0 < L}) (M : ℕ → ℕ),
        Tendsto (fun j => (L j).val) atTop atTop →
        Tendsto (fun j => (M j : ℝ) / ballVolume (L j)) atTop (𝓝 (ρ : ℝ)) →
        Tendsto
          (fun j => confinedGroundStateEnergy (z * M j) (M j) q z m (L j) /
            (ballVolume (L j) : EReal)) atTop (𝓝 (e ρ : EReal)) := by
    refine ⟨he0, hec, heconv, ?_⟩
    intro ρ L M hL hM
    have hs : Tendsto (fun j => (M j : ℝ) / neutralBallVolume (L j).val)
        atTop (𝓝 (ρ : ℝ)) := by
      simpa only [neutralBallVolume_eq_ballVolume] using hM
    have ht := EReal.tendsto_coe.mpr
      (helimits ρ (fun j => (L j).val) M (fun j => (L j).property) hL hs)
    simpa only [confined_normalized_eq_coe_neutralBallDensity q hq z hz m] using ht
  refine ⟨e, he, ?_⟩
  intro e' he'
  funext ρ
  obtain ⟨L, M, hL, hM⟩ := exists_neutral_density_sequence ρ
  have hsame : (e' ρ : EReal) = (e ρ : EReal) :=
    tendsto_nhds_unique (he'.2.2.2 ρ L M hL hM) (he.2.2.2 ρ L M hL hM)
  exact EReal.coe_injective hsame

end LiebThirring.ThermoHeadline

end
