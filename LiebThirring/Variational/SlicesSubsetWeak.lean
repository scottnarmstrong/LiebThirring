/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Variational.SlicesSubsetSmooth
public import LiebThirring.Variational.SlicesWeakRegularity

/-! # Outer weak-graph fields for arbitrary selected particle blocks -/

@[expose] public section

open MeasureTheory WithLp
open scoped ENNReal NNReal Classical SchwartzMap
open Filter Topology

namespace LiebThirring.Variational

/-- A fixed complementary-spin sector of the selected-block field. -/
noncomputable def subsetSliceFieldCLM {N k q : ℕ} (S : Set (Fin N))
    (e : Fin k ≃ S) (α : SubsetSpectatorSpins S q) :
    State N q →L[ℂ] Lp (State k q) 2 (volume : Measure (SubsetSpectatorConfiguration S)) :=
  let A := (subsetParticleField S e).toContinuousLinearEquiv.toContinuousLinearMap
  let B := (finiteLpPiLpEquiv (volume : Measure (SubsetSpectatorConfiguration S))
    (fun _ : SubsetSpectatorSpins S q => State k q)).toContinuousLinearEquiv.toContinuousLinearMap
  let P := PiLp.proj (𝕜 := ℂ) 2 (fun _ : SubsetSpectatorSpins S q =>
    Lp (State k q) 2 (volume : Measure (SubsetSpectatorConfiguration S))) α
  P.comp (B.comp A)

theorem subsetSliceFieldCLM_ae {N k q : ℕ} (S : Set (Fin N))
    (e : Fin k ≃ S) (α : SubsetSpectatorSpins S q) (u : State N q) :
    ∀ᵐ y : SubsetSpectatorConfiguration S,
      subsetSliceFieldCLM S e α u y = subsetParticleSlice S e u y α := by
  change ∀ᵐ y, ((finiteLpPiLpEquiv (volume : Measure (SubsetSpectatorConfiguration S))
    (fun _ : SubsetSpectatorSpins S q => State k q)) (subsetParticleField S e u)) α y = _
  exact finiteLpPiLpEquiv_apply_ae (volume : Measure (SubsetSpectatorConfiguration S))
    (fun _ : SubsetSpectatorSpins S q => State k q) (subsetParticleField S e u) α

/-- Package a slice and all its selected-coordinate derivatives. -/
noncomputable def subsetGraphField {N k q : ℕ} (S : Set (Fin N))
    (e : Fin k ≃ S) (α : SubsetSpectatorSpins S q) (u : State N q)
    (g : (Fin N × Fin 3) → State N q) :
    Lp (Sobolev.FormGraphAmbient k q) 2
      (volume : Measure (SubsetSpectatorConfiguration S)) :=
  (finiteLpPiLpEquiv (volume : Measure (SubsetSpectatorConfiguration S))
    (fun _ : Option (Fin k × Fin 3) => State k q)).symm
      (toLp 2 fun t => match t with
        | none => subsetSliceFieldCLM S e α u
        | some a => subsetSliceFieldCLM S e α (g ((e a.1).val, a.2)))

theorem subsetGraphField_none {N k q : ℕ} (S : Set (Fin N))
    (e : Fin k ≃ S) (α : SubsetSpectatorSpins S q) (u : State N q)
    (g : (Fin N × Fin 3) → State N q) :
    (finiteLpPiLpEquiv (volume : Measure (SubsetSpectatorConfiguration S))
      (fun _ : Option (Fin k × Fin 3) => State k q) (subsetGraphField S e α u g)) none =
      subsetSliceFieldCLM S e α u := by
  rw [subsetGraphField, LinearIsometryEquiv.apply_symm_apply]

theorem subsetGraphField_some {N k q : ℕ} (S : Set (Fin N))
    (e : Fin k ≃ S) (α : SubsetSpectatorSpins S q) (u : State N q)
    (g : (Fin N × Fin 3) → State N q) (a : Fin k × Fin 3) :
    (finiteLpPiLpEquiv (volume : Measure (SubsetSpectatorConfiguration S))
      (fun _ : Option (Fin k × Fin 3) => State k q) (subsetGraphField S e α u g)) (some a) =
      subsetSliceFieldCLM S e α (g ((e a.1).val, a.2)) := by
  rw [subsetGraphField, LinearIsometryEquiv.apply_symm_apply]

theorem subsetGraphField_tendsto {N k q : ℕ} (S : Set (Fin N))
    (e : Fin k ≃ S) (α : SubsetSpectatorSpins S q)
    (u : ℕ → State N q) (u0 : State N q)
    (g : ℕ → (Fin N × Fin 3) → State N q)
    (g0 : (Fin N × Fin 3) → State N q)
    (hu : Tendsto u atTop (𝓝 u0))
    (hg : ∀ a, Tendsto (fun n => g n a) atTop (𝓝 (g0 a))) :
    Tendsto (fun n => subsetGraphField S e α (u n) (g n)) atTop
      (𝓝 (subsetGraphField S e α u0 g0)) := by
  unfold subsetGraphField
  apply ((finiteLpPiLpEquiv (volume : Measure (SubsetSpectatorConfiguration S))
    (fun _ : Option (Fin k × Fin 3) => State k q)).symm.continuous.tendsto _).comp
  apply (PiLp.continuous_toLp 2
    (fun _ : Option (Fin k × Fin 3) =>
      Lp (State k q) 2 (volume : Measure (SubsetSpectatorConfiguration S))) |>.tendsto _).comp
  apply tendsto_pi_nhds.mpr
  intro t
  cases t with
  | none => exact ((subsetSliceFieldCLM S e α).continuous.tendsto u0).comp hu
  | some a => exact ((subsetSliceFieldCLM S e α).continuous.tendsto
      (g0 ((e a.1).val, a.2))).comp (hg ((e a.1).val, a.2))

theorem subsetGraphField_ae_slots {N k q : ℕ} (S : Set (Fin N))
    (e : Fin k ≃ S) (α : SubsetSpectatorSpins S q) (u : State N q)
    (g : (Fin N × Fin 3) → State N q) :
    ∀ᵐ y : SubsetSpectatorConfiguration S, ∀ t : Option (Fin k × Fin 3),
      subsetGraphField S e α u g y t = match t with
        | none => subsetParticleSlice S e u y α
        | some a => subsetParticleSlice S e (g ((e a.1).val, a.2)) y α := by
  rw [ae_all_iff]
  intro t
  cases t with
  | none =>
      filter_upwards [finiteLpPiLpEquiv_apply_ae
          (volume : Measure (SubsetSpectatorConfiguration S))
          (fun _ : Option (Fin k × Fin 3) => State k q)
          (subsetGraphField S e α u g) none,
        subsetSliceFieldCLM_ae S e α u] with y ht hs
      rw [subsetGraphField_none] at ht
      exact ht.symm.trans hs
  | some a =>
      filter_upwards [finiteLpPiLpEquiv_apply_ae
          (volume : Measure (SubsetSpectatorConfiguration S))
          (fun _ : Option (Fin k × Fin 3) => State k q)
          (subsetGraphField S e α u g) (some a),
        subsetSliceFieldCLM_ae S e α (g ((e a.1).val, a.2))] with y ht hs
      rw [subsetGraphField_some] at ht
      exact ht.symm.trans hs

/-- A smooth selected-block restriction represents the corresponding L² slice. -/
theorem subsetParticleSlice_schwartz_ae {N k q : ℕ} (S : Set (Fin N))
    (e : Fin k ≃ S) (f : 𝓢(Configuration N, SpinAmplitudes N q)) :
    ∀ᵐ y : SubsetSpectatorConfiguration S, ∀ α : SubsetSpectatorSpins S q,
      subsetParticleSlice S e (f.toLp 2 volume) y α =
        (subsetParticleSchwartz S e y α f).toLp 2 volume := by
  have hfins : ∀ᵐ z : SubsetSpectatorConfiguration S × Configuration k,
      (f.toLp 2 volume) (subsetOrderedInsertion S e z) =
        f (subsetOrderedInsertion S e z) :=
    (measurePreserving_subsetOrderedInsertion S e).quasiMeasurePreserving.ae
      (f.coeFn_toLp 2 (volume : Measure (Configuration N)))
  have hfxy := Measure.ae_ae_of_ae_prod hfins
  filter_upwards [subsetParticleSlice_ae S e (f.toLp 2 volume), hfxy] with y hs hy
  intro α
  apply Lp.ext
  filter_upwards [hs α, hy, (subsetParticleSchwartz S e y α f).coeFn_toLp 2 volume]
    with x hslice hf hto
  ext s
  rw [hslice s, hto, subsetParticleSchwartz_apply]
  exact congrArg (fun v : SpinAmplitudes N q => v (subsetOrderedSpinEquiv S e (α, s))) hf

/-- Smooth selected-block restriction commutes with every selected weak derivative. -/
theorem hasWeakDerivative_subsetParticleSlice_schwartz_ae {N k q : ℕ}
    (S : Set (Fin N)) (e : Fin k ≃ S)
    (f : 𝓢(Configuration N, SpinAmplitudes N q)) :
    ∀ᵐ y : SubsetSpectatorConfiguration S, ∀ α : SubsetSpectatorSpins S q,
      ∀ a : Fin k × Fin 3,
      Sobolev.HasWeakDerivative a (subsetParticleSlice S e (f.toLp 2 volume) y α)
        (subsetParticleSlice S e
          (Sobolev.schwartzCoordinateDerivativeL2 f ((e a.1).val, a.2)) y α) := by
  have hdall : ∀ᵐ y : SubsetSpectatorConfiguration S, ∀ a : Fin k × Fin 3,
      ∀ α : SubsetSpectatorSpins S q,
      subsetParticleSlice S e
          ((LineDeriv.lineDerivOp
            (Sobolev.coordinateVector ((e a.1).val, a.2)) f).toLp 2 volume) y α =
        (subsetParticleSchwartz S e y α
          (LineDeriv.lineDerivOp
            (Sobolev.coordinateVector ((e a.1).val, a.2)) f)).toLp 2 volume := by
    rw [ae_all_iff]
    intro a
    exact subsetParticleSlice_schwartz_ae S e
      (LineDeriv.lineDerivOp (Sobolev.coordinateVector ((e a.1).val, a.2)) f)
  filter_upwards [subsetParticleSlice_schwartz_ae S e f, hdall] with y hu hd
  intro α a
  rw [hu α]
  rw [schwartzCoordinateDerivativeL2_eq_toLp]
  rw [hd a α, ← lineDerivOp_subsetParticleSchwartz S e y α f a.1 a.2]
  rw [← schwartzCoordinateDerivativeL2_eq_toLp]
  exact Sobolev.hasWeakDerivative_schwartzCoordinateDerivativeL2
    (subsetParticleSchwartz S e y α f) a

theorem subsetGraphField_schwartz_mem_formGraph_ae {N k q : ℕ}
    (S : Set (Fin N)) (e : Fin k ≃ S) (α : SubsetSpectatorSpins S q)
    (f : 𝓢(Configuration N, SpinAmplitudes N q)) :
    ∀ᵐ y : SubsetSpectatorConfiguration S,
      subsetGraphField S e α (f.toLp 2 volume)
        (fun a => Sobolev.schwartzCoordinateDerivativeL2 f a) y ∈ Sobolev.formGraph k q := by
  filter_upwards [subsetGraphField_ae_slots S e α (f.toLp 2 volume)
      (fun a => Sobolev.schwartzCoordinateDerivativeL2 f a),
    hasWeakDerivative_subsetParticleSlice_schwartz_ae S e f] with y hslots hweak
  rw [Sobolev.mem_formGraph]
  intro a
  rw [hslots none, hslots (some a)]
  exact hweak α a

/-- Arbitrary selected-block slices inherit every selected weak derivative. -/
theorem hasWeakDerivative_subsetParticleSlice_ae {N k q : ℕ}
    (S : Set (Fin N)) (e : Fin k ≃ S) (u : State N q)
    (g : (Fin N × Fin 3) → State N q)
    (hg : ∀ a, Sobolev.HasWeakDerivative a u (g a)) :
    ∀ᵐ y : SubsetSpectatorConfiguration S, ∀ α : SubsetSpectatorSpins S q,
      ∀ a : Fin k × Fin 3,
      Sobolev.HasWeakDerivative a (subsetParticleSlice S e u y α)
        (subsetParticleSlice S e (g ((e a.1).val, a.2)) y α) := by
  obtain ⟨f, -, hfu, hfg⟩ := Sobolev.exists_compact_smooth_weakDerivative_sequence u g hg
  rw [ae_all_iff]
  intro α
  have hmem : ∀ n, ∀ᵐ y : SubsetSpectatorConfiguration S,
      subsetGraphField S e α ((f n).toLp 2 volume)
        (fun a => Sobolev.schwartzCoordinateDerivativeL2 (f n) a) y ∈
          Sobolev.formGraph k q :=
    fun n => subsetGraphField_schwartz_mem_formGraph_ae S e α (f n)
  have htend := subsetGraphField_tendsto S e α
    (fun n => (f n).toLp 2 volume) u
    (fun n a => Sobolev.schwartzCoordinateDerivativeL2 (f n) a) g hfu hfg
  have hlimit := mem_formGraph_ae_of_tendsto_L2 _ _ hmem htend
  filter_upwards [hlimit, subsetGraphField_ae_slots S e α u g] with y hy hslots
  rw [Sobolev.mem_formGraph] at hy
  intro a
  simpa only [hslots none, hslots (some a)] using hy a

/-- Almost every selected-block slice has finite kinetic energy. -/
theorem subsetParticleSlice_kineticEnergy_lt_top_ae {N k q : ℕ}
    (S : Set (Fin N)) (e : Fin k ≃ S) (u : State N q)
    (hu : kineticEnergy u < ⊤) :
    ∀ᵐ y : SubsetSpectatorConfiguration S, ∀ α : SubsetSpectatorSpins S q,
      kineticEnergy (subsetParticleSlice S e u y α) < ⊤ := by
  obtain ⟨g, hg⟩ := Sobolev.exists_weakDerivatives_of_kineticEnergy_lt_top u hu
  filter_upwards [hasWeakDerivative_subsetParticleSlice_ae S e u g hg] with y hy
  intro α
  exact (Sobolev.kineticEnergy_lt_top_iff_exists_weakDerivatives _).2
    ⟨fun a => subsetParticleSlice S e (g ((e a.1).val, a.2)) y α, hy α⟩

end LiebThirring.Variational
end
