/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.ThermoForm.SmoothCore
public import LiebThirring.Variational.TrialConstruction

/-! # Compact smooth joint electron and nucleus trials

Argument thermodynamic confined form estimates. A Slater electron amplitude is multiplied
by a symmetric product of one spatial nuclear bump.
-/

public section

open MeasureTheory WithLp Set Function
open scoped ENNReal NNReal ContDiff SchwartzMap

namespace LiebThirring

@[expose] noncomputable def nuclearTrialProduct (M : ℕ) (b : Position → ℝ)
    (R : Configuration M) : ℝ := ∏ k : Fin M, b (particlePosition R k)

theorem contDiff_nuclearTrialProduct (M : ℕ) (b : Position → ℝ)
    (hb : ContDiff ℝ ∞ b) : ContDiff ℝ ∞ (nuclearTrialProduct M b) := by
  apply contDiff_prod
  intro k _
  exact hb.comp (contDiff_particlePosition k)

theorem nuclearTrialProduct_permute {M : ℕ} (b : Position → ℝ)
    (τ : Equiv.Perm (Fin M)) (R : Configuration M) :
    nuclearTrialProduct M b (permutePositions τ R) = nuclearTrialProduct M b R := by
  simp only [nuclearTrialProduct, particlePosition_permutePositions]
  exact Equiv.prod_comp τ (fun k => b (particlePosition R k))

theorem hasCompactSupport_nuclearTrialProduct (M : ℕ) (b : Position → ℝ)
    (hb : HasCompactSupport b) : HasCompactSupport (nuclearTrialProduct M b) := by
  classical
  apply HasCompactSupport.of_support_subset_isCompact
    ((trialConfigurationHomeomorph M).isCompact_preimage.mpr
      (isCompact_univ_pi (fun _ : Fin M => hb)))
  intro R hR
  change ∀ k ∈ (univ : Set (Fin M)), particlePosition R k ∈ tsupport b
  intro k _
  apply subset_tsupport
  change b (particlePosition R k) ≠ 0
  exact (Finset.prod_ne_zero_iff.mp hR) k (Finset.mem_univ k)

@[expose] noncomputable def jointTrialProduct {N M q : ℕ}
    (f : Configuration N → SpinAmplitudes N q) (b : Configuration M → ℝ)
    (X : QuantumConfiguration N M) : SpinAmplitudes N q := b X.snd • f X.fst

theorem contDiff_jointTrialProduct {N M q : ℕ}
    (f : Configuration N → SpinAmplitudes N q) (b : Configuration M → ℝ)
    (hf : ContDiff ℝ ∞ f) (hb : ContDiff ℝ ∞ b) :
    ContDiff ℝ ∞ (jointTrialProduct f b) :=
  (hb.comp (WithLp.sndL 2 ℝ (Configuration N) (Configuration M)).contDiff).smul
    (hf.comp (WithLp.fstL 2 ℝ (Configuration N) (Configuration M)).contDiff)

theorem hasCompactSupport_jointTrialProduct {N M q : ℕ}
    (f : Configuration N → SpinAmplitudes N q) (b : Configuration M → ℝ)
    (hf : HasCompactSupport f) (hb : HasCompactSupport b) :
    HasCompactSupport (jointTrialProduct f b) := by
  apply HasCompactSupport.of_support_subset_isCompact
    ((WithLp.prodContinuousLinearEquiv 2 ℝ (Configuration N) (Configuration M)).toHomeomorph.isCompact_preimage.mpr (hf.prod hb))
  intro X hX
  change X.fst ∈ tsupport f ∧ X.snd ∈ tsupport b
  constructor
  · apply subset_tsupport
    intro h
    exact hX (by simp only [jointTrialProduct, h, smul_zero])
  · apply subset_tsupport
    intro h
    exact hX (by simp only [jointTrialProduct, h, zero_smul])

theorem exists_compact_schwartz_joint_trial (N M q : ℕ) (hq : 1 ≤ q) :
    ∃ f : 𝓢(QuantumConfiguration N M, SpinAmplitudes N q), f ≠ 0 ∧
      HasCompactSupport (fun X => f X) ∧
      (∀ (σ : Equiv.Perm (Fin N)) (X : QuantumConfiguration N M) (s : SpinLabels N q),
        f (toLp 2 (permutePositions σ X.fst, X.snd)) (permuteSpins σ s) =
          (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : ℂ) * f X s) ∧
      (∀ (τ : Equiv.Perm (Fin M)) (X : QuantumConfiguration N M) (s : SpinLabels N q),
        f (toLp 2 (X.fst, permutePositions τ X.snd)) s = f X s) := by
  classical
  obtain ⟨f, hf, hc, ha⟩ := exists_compact_schwartz_antisymmetric q hq N
  obtain ⟨b, _, hb, hs, _, h0⟩ := exists_contDiff_tsupport_subset
    (n := (⊤ : ℕ∞)) (Metric.ball_mem_nhds (0 : Position) (by norm_num : (0 : ℝ) < 1))
  let g := nuclearTrialProduct M b
  have hg : HasCompactSupport g := hasCompactSupport_nuclearTrialProduct M b hb
  let F : 𝓢(QuantumConfiguration N M, SpinAmplitudes N q) :=
    (hasCompactSupport_jointTrialProduct (fun x => f x) g hc hg).toSchwartzMap
      (contDiff_jointTrialProduct (fun x => f x) g (f.smooth _)
        (contDiff_nuclearTrialProduct M b hs))
  have hg0 : g 0 = 1 := by
    have hz (k : Fin M) : particlePosition (0 : Configuration M) k = 0 := rfl
    simp only [g, nuclearTrialProduct, hz, h0, Finset.prod_const_one]
  refine ⟨F, ?_, hasCompactSupport_jointTrialProduct (fun x => f x) g hc hg, ?_, ?_⟩
  · intro hF
    apply hf
    ext x s
    have h := congrArg (fun u : 𝓢(QuantumConfiguration N M, SpinAmplitudes N q) =>
      u (toLp 2 (x, (0 : Configuration M))) s) hF
    change (g 0 : ℂ) * f x s = 0 at h
    simpa only [hg0, Complex.ofReal_one, one_mul, zero_apply, PiLp.zero_apply] using h
  · intro σ X s
    change (g X.snd : ℂ) * f (permutePositions σ X.fst) (permuteSpins σ s) =
      (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : ℂ) * ((g X.snd : ℂ) * f X.fst s)
    rw [ha]
    ring
  · intro τ X s
    change (g (permutePositions τ X.snd) : ℂ) * f X.fst s = (g X.snd : ℂ) * f X.fst s
    dsimp only [g]
    rw [nuclearTrialProduct_permute]

end LiebThirring

end
