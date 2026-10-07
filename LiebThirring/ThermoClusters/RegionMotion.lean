/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.ThermoClusters.Trials
public import LiebThirring.ThermoClusters.DirichletMotion

/-! # Rigid motion of an admissible compact cluster trial

The smooth cluster representative, its form-domain state and its literal
Dirichlet support are transported together. This makes rigid-motion and domain-inclusion identities and cluster assembly usable
with the same carrier, including rotations used by neutral variational packing. Source: Lieb–Lebowitz (1972) II.A, (2.3), (2.5), (2.9), pp. 324–326.
-/

public section
open MeasureTheory Set
open scoped NNReal SchwartzMap
namespace LiebThirring

/-- Rigid transport of a normalized smooth region trial. -/
@[expose] noncomputable def SmoothRegionTrial.motion {N M q : ℕ} {Ω : Set Position}
    (Q : Position ≃ₗᵢ[ℝ] Position) (c : Position) (f : SmoothRegionTrial N M q Ω) :
    SmoothRegionTrial N M q (spatialRigidMotion Q c '' Ω) := by
  refine ⟨quantumSchwartzMotion Q c f.val, ?_, ?_, ?_, ?_, ?_⟩
  · rw [tsupport_quantumSchwartzMotion]
    exact f.property.1.image (quantumRigidMotion Q c).continuous
  · rw [tsupport_quantumSchwartzMotion]
    rintro X ⟨Y, hY, rfl⟩
    refine ⟨fun i => ?_, fun k => ?_⟩
    · exact ⟨particlePosition Y.fst i, (f.property.2.1 hY).1 i,
        (particlePosition_quantumRigidMotion_fst Q c Y i).symm⟩
    · exact ⟨particlePosition Y.snd k, (f.property.2.1 hY).2 k,
        (particlePosition_quantumRigidMotion_snd Q c Y k).symm⟩
  · rw [quantumSchwartzMotion_toLp]
    exact quantum_antisymmetric_quantumStateMotion Q c _ f.property.2.2.1
  · rw [quantumSchwartzMotion_toLp]
    exact nuclear_symmetric_quantumStateMotion Q c _ f.property.2.2.2.1
  · rw [quantumSchwartzMotion_toLp, norm_quantumStateMotion]
    exact f.property.2.2.2.2

/-- The transported smooth carrier represents exactly the already-proved form-domain motion. -/
theorem SmoothRegionTrial.formDomain_motion {N M q : ℕ} {Ω : Set Position}
    (Q : Position ≃ₗᵢ[ℝ] Position) (c : Position) (f : SmoothRegionTrial N M q Ω) :
    (f.motion Q c).formDomain = quantumFormDomainMotion Q c f.formDomain := by
  apply Subtype.ext
  exact quantumSchwartzMotion_toLp Q c f.val

/-- The actual full energy of a compact cluster trial is unchanged. -/
theorem SmoothRegionTrial.energy_motion {N M q : ℕ} {Ω : Set Position}
    (Q : Position ≃ₗᵢ[ℝ] Position) (c : Position) (z : ℕ)
    (m : {m : ℝ≥0 // 0 < m}) (f : SmoothRegionTrial N M q Ω) :
    quantumEnergy z m (f.motion Q c).formDomain = quantumEnergy z m f.formDomain := by
  rw [f.formDomain_motion, quantumEnergy_quantumFormDomainMotion]

end LiebThirring
end
