/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Variational.SlicesWeakField

/-! # Weak Sobolev regularity of residual particle slices -/

@[expose] public section

open MeasureTheory WithLp
open scoped ENNReal SchwartzMap FourierTransform
open Filter Topology
open LineDeriv

namespace LiebThirring.Variational

open Sobolev

/-- The opaque density derivative is the literal L² bundle of the Schwartz derivative. -/
theorem schwartzCoordinateDerivativeL2_eq_toLp {N q : ℕ}
    (f : 𝓢(Configuration N, SpinAmplitudes N q)) (a : Fin N × Fin 3) :
    schwartzCoordinateDerivativeL2 f a =
      (lineDerivOp (coordinateVector a) f).toLp 2 volume := by
  apply HasWeakDerivative.unique (hasWeakDerivative_schwartzCoordinateDerivativeL2 f a)
  rw [hasWeakDerivative_iff_fourier_eq_symbol]
  have hderiv : 𝓕 ((lineDerivOp (coordinateVector a) f).toLp 2 volume) =
      (𝓕 (lineDerivOp (coordinateVector a) f)).toLp 2 volume :=
    SchwartzMap.toLp_fourier_eq _
  have hstate : 𝓕 (f.toLp 2 volume) = (𝓕 f).toLp 2 volume :=
    SchwartzMap.toLp_fourier_eq f
  filter_upwards [(𝓕 (lineDerivOp (coordinateVector a) f)).coeFn_toLp 2 volume,
    (𝓕 f).coeFn_toLp 2 volume] with ξ hd hu
  rw [hderiv, hstate, hd, hu, fourier_lineDeriv_coordinate]

/-- A smooth residual restriction represents the corresponding residual L² slice. -/
theorem residualParticleSlice_schwartz_ae {N k q : ℕ} (i : Fin N)
    (e : Fin k ≃ {j : Fin N // j ≠ i})
    (f : 𝓢(Configuration N, SpinAmplitudes N q)) :
    ∀ᵐ x : Position, ∀ s : Fin q,
      residualParticleSlice i e (f.toLp 2 volume) x s =
        (residualParticleSchwartz i e x s f).toLp 2 volume := by
  have hfins : ∀ᵐ z : Position × OtherConfiguration i,
      (f.toLp 2 volume) (insertParticle i z.1 z.2) = f (insertParticle i z.1 z.2) := by
    have h := (measurePreserving_insertion i).quasiMeasurePreserving.ae
      (f.coeFn_toLp 2 (volume : Measure (Configuration N)))
    simpa only [← insertionMeasurableEquiv_apply] using h
  have hfxy := Measure.ae_ae_of_ae_prod hfins
  filter_upwards [residualParticleSlice_ae i e (f.toLp 2 volume), hfxy] with x hs hx
  intro s
  apply Lp.ext
  have hxr := (Sobolev.measurePreserving_configurationReindex e).quasiMeasurePreserving.ae hx
  filter_upwards [hs s, hxr, (residualParticleSchwartz i e x s f).coeFn_toLp 2 volume]
    with y hslice hf hto
  ext t
  rw [hslice t, hto, residualParticleSchwartz_apply, residualAffineInsertion_eq]
  exact congrArg (fun v : SpinAmplitudes N q => v (insertSpin i s (fun j => t (e.symm j)))) hf

/-- Smooth residual restriction commutes with every residual weak coordinate derivative. -/
theorem hasWeakDerivative_residualParticleSlice_schwartz_ae {N k q : ℕ} (i : Fin N)
    (e : Fin k ≃ {j : Fin N // j ≠ i})
    (f : 𝓢(Configuration N, SpinAmplitudes N q)) :
    ∀ᵐ x : Position, ∀ s : Fin q, ∀ a : Fin k × Fin 3,
      HasWeakDerivative a (residualParticleSlice i e (f.toLp 2 volume) x s)
        (residualParticleSlice i e
          (schwartzCoordinateDerivativeL2 f ((e a.1).val, a.2)) x s) := by
  have hdall : ∀ᵐ x : Position, ∀ a : Fin k × Fin 3, ∀ s : Fin q,
      residualParticleSlice i e
          ((LineDeriv.lineDerivOp (coordinateVector ((e a.1).val, a.2)) f).toLp 2 volume) x s =
        (residualParticleSchwartz i e x s
          (LineDeriv.lineDerivOp (coordinateVector ((e a.1).val, a.2)) f)).toLp 2 volume := by
    rw [ae_all_iff]
    intro a
    exact residualParticleSlice_schwartz_ae i e
      (LineDeriv.lineDerivOp (coordinateVector ((e a.1).val, a.2)) f)
  filter_upwards [residualParticleSlice_schwartz_ae i e f, hdall] with x hu hd
  intro s a
  rw [hu s]
  rw [schwartzCoordinateDerivativeL2_eq_toLp]
  rw [hd a s, ← lineDerivOp_residualParticleSchwartz i e x s f a.1 a.2]
  rw [← schwartzCoordinateDerivativeL2_eq_toLp]
  exact hasWeakDerivative_schwartzCoordinateDerivativeL2
    (residualParticleSchwartz i e x s f) a

/-- Smooth packed residual graph fields lie in the closed weak graph almost everywhere. -/
theorem residualGraphField_schwartz_mem_formGraph_ae {N k q : ℕ} (i : Fin N)
    (e : Fin k ≃ {j : Fin N // j ≠ i}) (s : Fin q)
    (f : 𝓢(Configuration N, SpinAmplitudes N q)) :
    ∀ᵐ x : Position,
      residualGraphField i e s (f.toLp 2 volume)
        (fun a => schwartzCoordinateDerivativeL2 f a) x ∈ formGraph k q := by
  filter_upwards [residualGraphField_ae_slots i e s (f.toLp 2 volume)
      (fun a => schwartzCoordinateDerivativeL2 f a),
    hasWeakDerivative_residualParticleSlice_schwartz_ae i e f] with x hslots hweak
  rw [mem_formGraph]
  intro a
  rw [hslots none, hslots (some a)]
  exact hweak s a

/-- Residual slices inherit all weak spectator derivatives from a finite-energy state. -/
theorem hasWeakDerivative_residualParticleSlice_ae {N k q : ℕ} (i : Fin N)
    (e : Fin k ≃ {j : Fin N // j ≠ i}) (u : State N q)
    (g : (Fin N × Fin 3) → State N q) (hg : ∀ a, HasWeakDerivative a u (g a)) :
    ∀ᵐ x : Position, ∀ s : Fin q, ∀ a : Fin k × Fin 3,
      HasWeakDerivative a (residualParticleSlice i e u x s)
        (residualParticleSlice i e (g ((e a.1).val, a.2)) x s) := by
  obtain ⟨f, -, hfu, hfg⟩ := exists_compact_smooth_weakDerivative_sequence u g hg
  rw [ae_all_iff]
  intro s
  have hmem : ∀ n, ∀ᵐ x : Position,
      residualGraphField i e s ((f n).toLp 2 volume)
        (fun a => schwartzCoordinateDerivativeL2 (f n) a) x ∈ formGraph k q :=
    fun n => residualGraphField_schwartz_mem_formGraph_ae i e s (f n)
  have htend := residualGraphField_tendsto i e s
    (fun n => (f n).toLp 2 volume) u
    (fun n a => schwartzCoordinateDerivativeL2 (f n) a) g hfu hfg
  have hlimit := mem_formGraph_ae_of_tendsto_L2 _ _ hmem htend
  filter_upwards [hlimit, residualGraphField_ae_slots i e s u g] with x hx hslots
  rw [mem_formGraph] at hx
  intro a
  simpa only [hslots none, hslots (some a)] using hx a

/-- Every residual particle slice has finite spectator kinetic energy almost everywhere. -/
theorem residualParticleSlice_kineticEnergy_lt_top_ae {N k q : ℕ} (i : Fin N)
    (e : Fin k ≃ {j : Fin N // j ≠ i}) (u : State N q)
    (hu : kineticEnergy u < ⊤) :
    ∀ᵐ x : Position, ∀ s : Fin q,
      kineticEnergy (residualParticleSlice i e u x s) < ⊤ := by
  obtain ⟨g, hg⟩ := exists_weakDerivatives_of_kineticEnergy_lt_top u hu
  filter_upwards [hasWeakDerivative_residualParticleSlice_ae i e u g hg] with x hx
  intro s
  exact (kineticEnergy_lt_top_iff_exists_weakDerivatives _).2
    ⟨fun a => residualParticleSlice i e (g ((e a.1).val, a.2)) x s, hx s⟩

end LiebThirring.Variational

end
