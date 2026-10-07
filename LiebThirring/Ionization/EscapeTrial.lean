/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Ionization.EscapeVariational
public import LiebThirring.Ionization.EscapeTrialBound
public import LiebThirring.Ionization.EscapeSpinOrbital
public import LiebThirring.Ionization.EscapeLimit

/-!
# Normalized remote-electron trials

Construct the actual normalized antisymmetric wedge, account for
every kinetic and Coulomb term, and choose a finite scale making its energy
arbitrarily close from above to the old compact state's energy.
-/

public section

open MeasureTheory
open scoped ENNReal NNReal SchwartzMap

namespace LiebThirring

/-- A compact normalized antisymmetric state admits one more electron with arbitrarily
small additional energy. The trial is the actual remote-orbital wedge. -/
theorem escape_exists_trial_energy_lt (q : ℕ) (hq : 1 ≤ q) {N : ℕ} (Z : ℝ≥0)
    (f : 𝓢(Configuration N, SpinAmplitudes N q))
    (hc : HasCompactSupport (fun x => f x))
    (hf : ∀ (σ : Equiv.Perm (Fin N)) (x : Configuration N) (s : SpinLabels N q),
      f (permutePositions σ x) (permuteSpins σ s) = escapePermutationSign σ * f x s)
    (hn : ‖f.toLp 2 (volume : Measure (Configuration N))‖ = 1)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ u : FormDomain (N + 1) q, ‖(u : State (N + 1) q)‖ = 1 ∧
      realEnergy (fun _ : Fin 1 => Z) (fun _ => 0)
        (fun _ _ _ => Subsingleton.elim _ _) u < escapeAtomicSchwartzEnergy Z f + ε := by
  obtain ⟨R, hR, hRf⟩ := escape_exists_support_radius (fun x => f x) hc
  obtain ⟨K, _, hfamily⟩ := exists_remote_spin_orbitals q hq R
  obtain ⟨L, hL, herror⟩ := escape_exists_scale K N ε hε
  obtain ⟨h, hnorm, hcompact, hsupport, hkinetic⟩ := hfamily L hL
  have hLh (y : Position) (hy : y ∈ tsupport (fun p => h p)) :
      ‖y - escapeCenter R L‖ ≤ L := by
    simpa only [Metric.mem_closedBall, dist_eq_norm] using hsupport hy
  let g := escapeWedgeSchwartz f h hc hcompact
  have hg : ∀ (σ : Equiv.Perm (Fin (N + 1))) (x : Configuration (N + 1))
      (s : SpinLabels (N + 1) q),
      g (permutePositions σ x) (permuteSpins σ s) = escapePermutationSign σ * g x s := by
    intro σ x s
    change escapeWedge (fun y t => f y t) (fun y t => h y t)
      (permutePositions σ x) (permuteSpins σ s) =
        escapePermutationSign σ * escapeWedge (fun y t => f y t) (fun y t => h y t) x s
    exact escapeWedge_permute (fun y t => f y t) (fun y t => h y t) hf σ x s
  let u := escapeSchwartzForm g hg
  refine ⟨u, ?_, ?_⟩
  · change ‖g.toLp 2 (volume : Measure (Configuration (N + 1)))‖ = 1
    have hmass : (∫ p, ‖h p‖ ^ 2) = 1 := by
      rw [escape_schwartz_integral_mass, hnorm, one_pow]
    exact escapeWedgeSchwartz_norm f h hc hcompact hn hmass hR.le hL hRf hLh
  · rw [← escapeAtomicSchwartzEnergy_eq_realEnergy Z g u rfl]
    have he := escapeAtomicSchwartzEnergy_wedge_le Z f h hc hcompact hn hnorm
      hR.le hL hRf hLh
    rw [hkinetic] at he
    exact he.trans_lt (by linarith only [herror])

end LiebThirring

end
