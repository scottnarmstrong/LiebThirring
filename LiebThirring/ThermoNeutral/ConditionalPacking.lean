/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.ThermoNeutral.MeanSelection
public import LiebThirring.ThermoNeutral.ChargeBridge
public import LiebThirring.ThermoNeutral.TrialSupport
public import LiebThirring.ThermoNeutral.TrialApproximation
public import LiebThirring.ThermoClusters.MotionMarginals
public import LiebThirring.ThermoClusters.ContainedAssembly
public import LiebThirring.Packing.SwissCheeseStage

/-! # Neutral packing

The finite-family full-energy identity, rotation selection, and variational
approximation combine to give the physical packing inequality.
-/

public section

open MeasureTheory Metric Set Finset Function
open scoped NNReal ENNReal

namespace LiebThirring.ThermoNeutral

open ThermoHeadline

private theorem physicalNeutralEnergy_le_smoothRegionTrial
    (q : ℕ) (hq : 1 ≤ q) (z : ℕ) (hz : 1 ≤ z)
    (mass : {m : ℝ≥0 // 0 < m}) (Ω : Set Position)
    (hopen : IsOpen Ω) (hne : Ω.Nonempty) (N n : ℕ)
    (hN : N = z * n) (f : SmoothRegionTrial N n q Ω) :
    physicalNeutralEnergy q z mass Ω n ≤ quantumEnergy z mass f.formDomain := by
  subst N
  have hdir : dirichletRegionGroundStateEnergy (z * n) n q z mass Ω ≤
      (quantumEnergy z mass f.formDomain : EReal) := by
    unfold dirichletRegionGroundStateEnergy
    let ψ : DirichletRegionFormDomain (z * n) n q mass Ω := f.dirichletFormDomain mass
    let u : {ψ : DirichletRegionFormDomain (z * n) n q mass Ω // ‖ψ.val.val‖ = 1} :=
      ⟨ψ, f.norm_formDomain⟩
    exact iInf_le
      (fun v : {ψ : DirichletRegionFormDomain (z * n) n q mass Ω // ‖ψ.val.val‖ = 1} =>
        (quantumEnergy z mass v.val.val : EReal)) u
  have hphys := coe_physicalNeutralEnergy q hq z hz mass Ω n hopen hne
  exact EReal.coe_le_coe_iff.mp (hphys.symm ▸ hdir)

/-- Neutral ball packing inside any nonempty open ambient region. -/
theorem physicalNeutralEnergy_packing_fin_in_region
    (k : ℕ)
    (q : ℕ) (hq : 1 ≤ q) (z : ℕ) (hz : 1 ≤ z)
    (mass : {m : ℝ≥0 // 0 < m})
    (Ω : Set Position) (c : Fin k → Position) (R : Fin k → ℝ) (n : Fin k → ℕ)
    (hopen : IsOpen Ω) (hne : Ω.Nonempty) (hR : ∀ i, 0 < R i)
    (hsub : ∀ i, ball (c i) (R i) ⊆ Ω)
    (hdisj : Pairwise fun i j => Disjoint (ball (c i) (R i)) (ball (c j) (R j))) :
    physicalNeutralEnergy q z mass Ω (∑ i, n i) ≤
      ∑ i, physicalNeutralEnergy q z mass (ball (c i) (R i)) (n i) := by
  apply le_of_forall_pos_le_add
  intro ε hε
  let η := ε / (k + 1 : ℕ)
  have hη : 0 < η := div_pos hε (by positivity)
  choose g hg using fun i =>
    exists_smoothRegionTrial_energy_lt_physical_add q hq z hz mass (c i) (hR i) (n i) hη
  choose r hr0 hrR hμe hμn using fun i =>
    exists_inner_radius_of_smoothRegionTrial_ball (g i) (hR i)
  let μe : Fin k → Measure Position := fun i => quantumElectronMeasure (g i).formDomain.val
  let μn : Fin k → Measure Position := fun i => quantumNuclearMeasure (g i).formDomain.val
  have hneutral : ∀ i, (z : ℝ≥0∞) * μn i univ = μe i univ := by
    intro i
    rw [show μn i univ = (n i : ℝ≥0∞) from
      quantumNuclearMeasure_mass_of_normalized _ (g i).norm_formDomain,
      show μe i univ = (z * n i : ℕ) from
        quantumElectronMeasure_mass_of_normalized _ (g i).norm_formDomain]
    norm_num
  obtain ⟨Q, hQ⟩ := exists_nonpos_totalRotatedChargeInteraction z c r R μe μn
    hr0 hrR hdisj hμe hμn hneutral
  let rotIso : Fin k → Position ≃ₗᵢ[ℝ] Position := fun i => spatialRotationIsometry (Q i)
  let shift : Fin k → Position := fun i => c i - rotIso i (c i)
  have happly (i : Fin k) (x : Position) : spatialRigidMotion (rotIso i) (shift i) x =
      rotIso i x + shift i := rfl
  have hrot (i : Fin k) : spatialRigidMotion (rotIso i) (shift i) '' ball (c i) (R i) ⊆
      ball (c i) (R i) := by
    rintro y ⟨x, hx, rfl⟩
    have heq : spatialRigidMotion (rotIso i) (shift i) x = rotateAbout (Q i) (c i) x := by
      simp only [happly, shift, rotIso, rotateAbout, map_sub]
      abel_nf
    rw [heq, mem_ball, dist_eq_norm, norm_rotateAbout_sub]
    simpa only [mem_ball, dist_eq_norm] using hx
  let f : ∀ i : Fin k, SmoothRegionTrial (z * n i) (n i) q (ball (c i) (R i)) :=
    fun i => ((g i).motion (rotIso i) (shift i)).enlarge (hrot i)
  have henergy (i : Fin k) : quantumEnergy z mass (f i).formDomain =
      quantumEnergy z mass (g i).formDomain := by
    change quantumEnergy z mass ((g i).motion (rotIso i) (shift i)).formDomain = _
    exact SmoothRegionTrial.energy_motion _ _ _ _ _
  have hmap_e (i : Fin k) : quantumElectronMeasure (f i).formDomain.val =
      (μe i).map (rotateAbout (Q i) (c i)) := by
    change quantumElectronMeasure ((g i).motion (rotIso i) (shift i)).formDomain.val = _
    rw [SmoothRegionTrial.formDomain_motion]
    change quantumElectronMeasure
      (quantumStateMotion (rotIso i) (shift i) (g i).formDomain.val) = _
    rw [quantumElectronMeasure_quantumStateMotion]
    congr 1
    funext x
    simp only [happly, shift, rotIso, rotateAbout, map_sub]
    abel_nf
  have hmap_n (i : Fin k) : quantumNuclearMeasure (f i).formDomain.val =
      (μn i).map (rotateAbout (Q i) (c i)) := by
    change quantumNuclearMeasure ((g i).motion (rotIso i) (shift i)).formDomain.val = _
    rw [SmoothRegionTrial.formDomain_motion]
    change quantumNuclearMeasure
      (quantumStateMotion (rotIso i) (shift i) (g i).formDomain.val) = _
    rw [quantumNuclearMeasure_quantumStateMotion]
    congr 1
    funext x
    simp only [happly, shift, rotIso, rotateAbout, map_sub]
    abel_nf
  obtain ⟨F, _, _, _, _, hF⟩ := exists_smoothRegionTrial_finite_assembly_in_region
    k q z mass (fun i => z * n i) n (fun i => ball (c i) (R i)) Ω f hdisj hsub
  have htrial : physicalNeutralEnergy q z mass Ω (∑ i, n i) ≤
      quantumEnergy z mass F.formDomain := by
    have hcounts : ∑ i, z * n i = z * ∑ i, n i := by
      rw [mul_sum]
    exact physicalNeutralEnergy_le_smoothRegionTrial q hq z hz mass Ω hopen hne
      (∑ i, z * n i) (∑ i, n i) hcounts F
  calc
    physicalNeutralEnergy q z mass Ω (∑ i, n i)
        ≤ quantumEnergy z mass F.formDomain := htrial
    _ = ∑ i, quantumEnergy z mass (g i).formDomain +
        totalRotatedChargeInteraction z c μe μn Q := by
      rw [hF, totalRotatedChargeInteraction_eq_sum_clusterChargeInteraction
        z c μe μn Q (fun i j hij =>
          inner_radii_lt_center_distance_of_disjoint_balls
            ((hr0 i).trans (hrR i)) ((hr0 j).trans (hrR j))
            (hrR i) (hrR j) (hdisj hij)) hμe hμn]
      simp_rw [henergy, hmap_e, hmap_n]
    _ ≤ ∑ i, quantumEnergy z mass (g i).formDomain := by linarith
    _ ≤ ∑ i, physicalNeutralEnergy q z mass (ball (c i) (R i)) (n i) + ε := by
      have hs : ∑ i, quantumEnergy z mass (g i).formDomain ≤
          ∑ i, (physicalNeutralEnergy q z mass (ball (c i) (R i)) (n i) + η) :=
        sum_le_sum fun i _ => (hg i).le
      have hcard : ∑ _i : Fin k, η < ε := by
        simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, η]
        have hc : (k : ℝ) < ((k + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.lt_succ_self k
        calc
          (k : ℝ) * (ε / (k + 1 : ℕ))
              = ε * ((k : ℝ) / (k + 1 : ℕ)) := by ring
          _ < ε * 1 := (mul_lt_mul_of_pos_left ((div_lt_one (by positivity)).2 hc) hε)
          _ = ε := mul_one ε
      rw [sum_add_distrib] at hs
      linarith

/-- The exact all-ball neutral integer packing hypothesis consumed by the
thermodynamic limit, for arbitrary finite labels and ambient regions. -/
theorem physicalNeutralEnergy_neutral_packing
    (q : ℕ) (hq : 1 ≤ q) (z : ℕ) (hz : 1 ≤ z)
    (m : {m : ℝ≥0 // 0 < m}) :
    ∀ (ι : Type) (Ω : Set Position) (s : Finset ι)
      (c : ι → Position) (r : ι → ℝ) (n : ι → ℕ),
      IsOpen Ω → Ω.Nonempty → Bornology.IsBounded Ω →
      (∀ i ∈ s, 0 < r i) → (∀ i ∈ s, ball (c i) (r i) ⊆ Ω) →
      (s : Set ι).PairwiseDisjoint (fun i => ball (c i) (r i)) →
      physicalNeutralEnergy q z m Ω (∑ i ∈ s, n i) ≤
        ∑ i ∈ s, physicalNeutralEnergy q z m (ball (c i) (r i)) (n i) := by
  intro ι Ω s c r n hopen hne _hbounded hr hsub hdisj
  let e : Fin s.card ≃ s :=
    (Fintype.equivFinOfCardEq (α := s) (by simp : Fintype.card s = s.card)).symm
  have hsum (a : ι → ℝ) : ∑ i : Fin s.card, a (e i) = ∑ i ∈ s, a i := by
    calc
      _ = ∑ i : s, a i := Equiv.sum_comp e (fun i : s => a i)
      _ = _ := Finset.sum_attach s a
  have hsum_nat : ∑ i : Fin s.card, n (e i) = ∑ i ∈ s, n i := by
    calc
      _ = ∑ i : s, n i := Equiv.sum_comp e (fun i : s => n i)
      _ = _ := Finset.sum_attach s n
  have hp := physicalNeutralEnergy_packing_fin_in_region s.card q hq z hz m Ω
    (fun i => c (e i)) (fun i => r (e i)) (fun i => n (e i)) hopen hne
    (fun i => hr (e i) (e i).property)
    (fun i => hsub (e i) (e i).property)
    (fun i j hij => hdisj (e i).property (e j).property
      (fun heq => hij (e.injective (Subtype.ext heq))))
  rw [hsum_nat] at hp
  rw [hsum (fun i => physicalNeutralEnergy q z m (ball (c i) (r i)) (n i))] at hp
  exact hp

end LiebThirring.ThermoNeutral

end
