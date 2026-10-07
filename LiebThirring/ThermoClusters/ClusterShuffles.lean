/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.ThermoClusters.BlockPermutation
public import LiebThirring.ThermoClusters.Pointwise
public import Mathlib.LinearAlgebra.Alternating.DomCoprod
public import Mathlib.GroupTheory.Perm.Subgroup
public import LiebThirring.ThermoClusters.Permutations

/-! # Binary shuffles of correlated quantum clusters -/

public section
open MeasureTheory WithLp
open scoped SchwartzMap
namespace LiebThirring

/-- The ordered product of two correlated cluster states has the required
fermionic signs under permutations internal to the two electron blocks. -/
theorem clusterProduct_electron_block_alternating {n₁ n₂ m₁ m₂ q : ℕ}
    (f : 𝓢(QuantumConfiguration n₁ m₁, SpinAmplitudes n₁ q))
    (h : 𝓢(QuantumConfiguration n₂ m₂, SpinAmplitudes n₂ q))
    (hf : quantum_antisymmetric (f.toLp 2 volume))
    (hh : quantum_antisymmetric (h.toLp 2 volume))
    (σ₁ : Equiv.Perm (Fin n₁)) (σ₂ : Equiv.Perm (Fin n₂))
    (X : QuantumConfiguration (n₁+n₂) (m₁+m₂)) (s : SpinLabels (n₁+n₂) q) :
    clusterProduct (fun X => f X) (fun X => h X)
        (toLp 2 (permutePositions (blockPermutation σ₁ σ₂) X.fst, X.snd))
        (permuteSpins (blockPermutation σ₁ σ₂) s) =
      (((Equiv.Perm.sign σ₁ : ℤˣ) : ℤ) : ℂ) *
        (((Equiv.Perm.sign σ₂ : ℤˣ) : ℤ) : ℂ) *
          clusterProduct (fun X => f X) (fun X => h X) X s := by
  rw [clusterProduct, clusterProduct]
  have hsplit := quantumClusterSplit_permute_block σ₁ σ₂
    (1 : Equiv.Perm (Fin m₁)) (1 : Equiv.Perm (Fin m₂)) X
  simp only [blockPermutation_one, permutePositions_one] at hsplit
  rw [hsplit]
  simp only [WithLp.toLp_fst, WithLp.toLp_snd]
  simp only [clusterSpinTensor, PiLp.toLp_apply]
  rw [clusterSpinEquiv_symm_permute_block]
  rw [(quantum_antisymmetric_schwartz_iff f).mp hf σ₁]
  rw [(quantum_antisymmetric_schwartz_iff h).mp hh σ₂]
  ring

/-- The ordered product of two correlated cluster states is invariant under
permutations internal to the two nuclear blocks. -/
theorem clusterProduct_nuclear_block_invariant {n₁ n₂ m₁ m₂ q : ℕ}
    (f : 𝓢(QuantumConfiguration n₁ m₁, SpinAmplitudes n₁ q))
    (h : 𝓢(QuantumConfiguration n₂ m₂, SpinAmplitudes n₂ q))
    (hf : nuclear_symmetric (f.toLp 2 volume))
    (hh : nuclear_symmetric (h.toLp 2 volume))
    (τ₁ : Equiv.Perm (Fin m₁)) (τ₂ : Equiv.Perm (Fin m₂))
    (X : QuantumConfiguration (n₁+n₂) (m₁+m₂)) (s : SpinLabels (n₁+n₂) q) :
    clusterProduct (fun X => f X) (fun X => h X)
        (toLp 2 (X.fst, permutePositions (blockPermutation τ₁ τ₂) X.snd)) s =
      clusterProduct (fun X => f X) (fun X => h X) X s := by
  rw [clusterProduct, clusterProduct]
  have hsplit := quantumClusterSplit_permute_block
    (1 : Equiv.Perm (Fin n₁)) (1 : Equiv.Perm (Fin n₂)) τ₁ τ₂ X
  simp only [blockPermutation_one, permutePositions_one] at hsplit
  rw [hsplit]
  simp only [WithLp.toLp_fst, WithLp.toLp_snd]
  simp only [clusterSpinTensor, PiLp.toLp_apply]
  rw [(nuclear_symmetric_schwartz_iff f).mp hf τ₁]
  rw [(nuclear_symmetric_schwartz_iff h).mp hh τ₂]

/-- Internal block permutations act on the ordered Schwartz product by the
product of the two electronic signs; nuclear block permutations contribute no
sign.  This is the representative-independence input for the two shuffle
quotients. -/
theorem quantumSchwartzPermutation_clusterProductSchwartz_block {n₁ n₂ m₁ m₂ q : ℕ}
    (f : 𝓢(QuantumConfiguration n₁ m₁, SpinAmplitudes n₁ q))
    (h : 𝓢(QuantumConfiguration n₂ m₂, SpinAmplitudes n₂ q))
    (hfc : HasCompactSupport (fun X => f X)) (hhc : HasCompactSupport (fun X => h X))
    (hfa : quantum_antisymmetric (f.toLp 2 volume))
    (hha : quantum_antisymmetric (h.toLp 2 volume))
    (hfs : nuclear_symmetric (f.toLp 2 volume))
    (hhs : nuclear_symmetric (h.toLp 2 volume))
    (σ₁ : Equiv.Perm (Fin n₁)) (σ₂ : Equiv.Perm (Fin n₂))
    (τ₁ : Equiv.Perm (Fin m₁)) (τ₂ : Equiv.Perm (Fin m₂)) :
    quantumSchwartzPermutation (blockPermutation σ₁ σ₂) (blockPermutation τ₁ τ₂)
        (clusterProductSchwartz f h hfc hhc) =
      ((((Equiv.Perm.sign σ₁ : ℤˣ) : ℤ) : ℂ) *
        (((Equiv.Perm.sign σ₂ : ℤˣ) : ℤ) : ℂ)) •
          clusterProductSchwartz f h hfc hhc := by
  ext X s
  simp only [quantumSchwartzPermutation, quantumPermutation,
    smul_apply, PiLp.smul_apply]
  rw [clusterProductSchwartz]
  change clusterProduct (fun X => f X) (fun X => h X)
    (toLp 2 (permutePositions (blockPermutation σ₁ σ₂) X.fst,
      permutePositions (blockPermutation τ₁ τ₂) X.snd))
    (permuteSpins (blockPermutation σ₁ σ₂) s) = _
  have hE := clusterProduct_electron_block_alternating f h hfa hha σ₁ σ₂
    (toLp 2 (X.fst, permutePositions (blockPermutation τ₁ τ₂) X.snd)) s
  simp only [WithLp.toLp_fst, WithLp.toLp_snd] at hE
  rw [hE]
  rw [clusterProduct_nuclear_block_invariant f h hfs hhs τ₁ τ₂]
  change _ = _ * clusterProduct (fun X => f X) (fun X => h X) X s
  ring

theorem quantumSchwartzPermutation_comp {N M q : ℕ}
    (σ₁ σ₂ : Equiv.Perm (Fin N)) (τ₁ τ₂ : Equiv.Perm (Fin M))
    (F : 𝓢(QuantumConfiguration N M, SpinAmplitudes N q)) :
    quantumSchwartzPermutation σ₁ τ₁ (quantumSchwartzPermutation σ₂ τ₂ F) =
      quantumSchwartzPermutation (σ₁ * σ₂) (τ₁ * τ₂) F := by
  ext X s
  rfl



/-- The joint Schwartz permutation commutes with complex scalar multiplication. -/
theorem quantumSchwartzPermutation_smul {N M q : ℕ}
    (σ : Equiv.Perm (Fin N)) (τ : Equiv.Perm (Fin M)) (c : ℂ)
    (F : 𝓢(QuantumConfiguration N M, SpinAmplitudes N q)) :
    quantumSchwartzPermutation σ τ (c • F) = c • quantumSchwartzPermutation σ τ F := by
  unfold quantumSchwartzPermutation
  rw [map_smul, map_smul]

/-- One genuine electron/nuclear shuffle of two correlated compact clusters. -/
@[expose] noncomputable def binaryClusterShuffleTerm {n₁ n₂ m₁ m₂ q : ℕ}
    (f : 𝓢(QuantumConfiguration n₁ m₁, SpinAmplitudes n₁ q))
    (h : 𝓢(QuantumConfiguration n₂ m₂, SpinAmplitudes n₂ q))
    (hfc : HasCompactSupport (fun X => f X)) (hhc : HasCompactSupport (fun X => h X))
    (hfa : quantum_antisymmetric (f.toLp 2 volume))
    (hha : quantum_antisymmetric (h.toLp 2 volume))
    (hfs : nuclear_symmetric (f.toLp 2 volume))
    (hhs : nuclear_symmetric (h.toLp 2 volume))
    (e : Equiv.Perm.ModSumCongr (Fin n₁) (Fin n₂))
    (a : Equiv.Perm.ModSumCongr (Fin m₁) (Fin m₂)) :
    𝓢(QuantumConfiguration (n₁+n₂) (m₁+m₂), SpinAmplitudes (n₁+n₂) q) :=
  Quotient.liftOn' e (fun σ => Quotient.liftOn' a (fun τ =>
    ((((Equiv.Perm.sign σ : ℤˣ) : ℤ) : ℂ)) •
      quantumSchwartzPermutation (finSumFinEquiv.permCongr σ)
        (finSumFinEquiv.permCongr τ) (clusterProductSchwartz f h hfc hhc))
    (by
      intro τ₁ τ₂ H
      rw [QuotientGroup.leftRel_apply] at H
      obtain ⟨⟨ul, ur⟩, hu⟩ := H
      replace hu := inv_mul_eq_iff_eq_mul.mp hu.symm
      rw [hu]
      have hp : finSumFinEquiv.permCongr
          (τ₁ * (Equiv.Perm.sumCongrHom (Fin m₁) (Fin m₂)) (ul, ur)) =
          finSumFinEquiv.permCongr τ₁ * blockPermutation ul ur := by
        ext i
        simp only [Equiv.permCongr_apply, Equiv.Perm.mul_apply, blockPermutation,
          Equiv.Perm.sumCongrHom_apply, Equiv.symm_apply_apply]
      have hb : quantumSchwartzPermutation (1 : Equiv.Perm (Fin (n₁+n₂)))
          (blockPermutation ul ur) (clusterProductSchwartz f h hfc hhc) =
          clusterProductSchwartz f h hfc hhc := by
        simpa using quantumSchwartzPermutation_clusterProductSchwartz_block f h hfc hhc
          hfa hha hfs hhs 1 1 ul ur
      have hc := quantumSchwartzPermutation_comp (finSumFinEquiv.permCongr σ)
        (1 : Equiv.Perm (Fin (n₁+n₂))) (finSumFinEquiv.permCongr τ₁)
        (blockPermutation ul ur) (clusterProductSchwartz f h hfc hhc)
      have he : quantumSchwartzPermutation (finSumFinEquiv.permCongr σ)
          (finSumFinEquiv.permCongr τ₁) (clusterProductSchwartz f h hfc hhc) =
          quantumSchwartzPermutation (finSumFinEquiv.permCongr σ)
            (finSumFinEquiv.permCongr τ₁ * blockPermutation ul ur)
              (clusterProductSchwartz f h hfc hhc) := by
        simpa only [mul_one, hb] using hc
      rw [hp, ← he]))
    (by
      intro σ₁ σ₂ H
      induction a using Quotient.inductionOn' with
      | h τ =>
        rw [QuotientGroup.leftRel_apply] at H
        obtain ⟨⟨sl, sr⟩, hs⟩ := H
        replace hs := inv_mul_eq_iff_eq_mul.mp hs.symm
        simp only [Quotient.liftOn'_mk'']
        rw [hs, Equiv.Perm.sign_mul]
        have hp : finSumFinEquiv.permCongr
            (σ₁ * (Equiv.Perm.sumCongrHom (Fin n₁) (Fin n₂)) (sl, sr)) =
            finSumFinEquiv.permCongr σ₁ * blockPermutation sl sr := by
          ext i
          simp only [Equiv.permCongr_apply, Equiv.Perm.mul_apply, blockPermutation,
            Equiv.Perm.sumCongrHom_apply, Equiv.symm_apply_apply]
        have hb : quantumSchwartzPermutation (blockPermutation sl sr)
            (1 : Equiv.Perm (Fin (m₁+m₂))) (clusterProductSchwartz f h hfc hhc) =
            ((((Equiv.Perm.sign sl : ℤˣ) : ℤ) : ℂ) *
              (((Equiv.Perm.sign sr : ℤˣ) : ℤ) : ℂ)) •
                clusterProductSchwartz f h hfc hhc := by
          simpa only [blockPermutation_one] using
            quantumSchwartzPermutation_clusterProductSchwartz_block f h hfc hhc
              hfa hha hfs hhs sl sr 1 1
        have hc := quantumSchwartzPermutation_comp (finSumFinEquiv.permCongr σ₁)
          (blockPermutation sl sr) (finSumFinEquiv.permCongr τ)
          (1 : Equiv.Perm (Fin (m₁+m₂))) (clusterProductSchwartz f h hfc hhc)
        have he : quantumSchwartzPermutation
            (finSumFinEquiv.permCongr σ₁ * blockPermutation sl sr)
            (finSumFinEquiv.permCongr τ) (clusterProductSchwartz f h hfc hhc) =
            ((((Equiv.Perm.sign sl : ℤˣ) : ℤ) : ℂ) *
              (((Equiv.Perm.sign sr : ℤˣ) : ℤ) : ℂ)) •
                quantumSchwartzPermutation (finSumFinEquiv.permCongr σ₁)
                  (finSumFinEquiv.permCongr τ) (clusterProductSchwartz f h hfc hhc) := by
          simpa only [mul_one, hb, quantumSchwartzPermutation_smul] using hc.symm
        rw [hp, he]
        rcases Int.units_eq_one_or (Equiv.Perm.sign sl) with hsl | hsl <;>
          rcases Int.units_eq_one_or (Equiv.Perm.sign sr) with hsr | hsr <;>
          simp [hsl, hsr])

theorem binaryClusterShuffleTerm_mk_mk {n₁ n₂ m₁ m₂ q : ℕ}
    (f : 𝓢(QuantumConfiguration n₁ m₁, SpinAmplitudes n₁ q))
    (h : 𝓢(QuantumConfiguration n₂ m₂, SpinAmplitudes n₂ q))
    (hfc : HasCompactSupport (fun X => f X)) (hhc : HasCompactSupport (fun X => h X))
    (hfa : quantum_antisymmetric (f.toLp 2 volume))
    (hha : quantum_antisymmetric (h.toLp 2 volume))
    (hfs : nuclear_symmetric (f.toLp 2 volume))
    (hhs : nuclear_symmetric (h.toLp 2 volume))
    (σ : Equiv.Perm (Fin n₁ ⊕ Fin n₂)) (τ : Equiv.Perm (Fin m₁ ⊕ Fin m₂)) :
    binaryClusterShuffleTerm f h hfc hhc hfa hha hfs hhs ⟦σ⟧ ⟦τ⟧ =
      ((((Equiv.Perm.sign σ : ℤˣ) : ℤ) : ℂ)) •
        quantumSchwartzPermutation (finSumFinEquiv.permCongr σ)
          (finSumFinEquiv.permCongr τ) (clusterProductSchwartz f h hfc hhc) := by
  rfl

/-- The finite sum over the genuine electron and nuclear shuffle quotients. -/
@[expose] noncomputable def binaryClusterShuffleSum {n₁ n₂ m₁ m₂ q : ℕ}
    (f : 𝓢(QuantumConfiguration n₁ m₁, SpinAmplitudes n₁ q))
    (h : 𝓢(QuantumConfiguration n₂ m₂, SpinAmplitudes n₂ q))
    (hfc : HasCompactSupport (fun X => f X)) (hhc : HasCompactSupport (fun X => h X))
    (hfa : quantum_antisymmetric (f.toLp 2 volume))
    (hha : quantum_antisymmetric (h.toLp 2 volume))
    (hfs : nuclear_symmetric (f.toLp 2 volume))
    (hhs : nuclear_symmetric (h.toLp 2 volume)) :
    𝓢(QuantumConfiguration (n₁+n₂) (m₁+m₂), SpinAmplitudes (n₁+n₂) q) :=
  ∑ e : Equiv.Perm.ModSumCongr (Fin n₁) (Fin n₂),
    ∑ a : Equiv.Perm.ModSumCongr (Fin m₁) (Fin m₂),
      binaryClusterShuffleTerm f h hfc hhc hfa hha hfs hhs e a

/-- Binary assembly with the exact reciprocal square-root shuffle normalization. -/
@[expose] noncomputable def binaryClusterAssembly {n₁ n₂ m₁ m₂ q : ℕ}
    (f : 𝓢(QuantumConfiguration n₁ m₁, SpinAmplitudes n₁ q))
    (h : 𝓢(QuantumConfiguration n₂ m₂, SpinAmplitudes n₂ q))
    (hfc : HasCompactSupport (fun X => f X)) (hhc : HasCompactSupport (fun X => h X))
    (hfa : quantum_antisymmetric (f.toLp 2 volume))
    (hha : quantum_antisymmetric (h.toLp 2 volume))
    (hfs : nuclear_symmetric (f.toLp 2 volume))
    (hhs : nuclear_symmetric (h.toLp 2 volume)) :
    𝓢(QuantumConfiguration (n₁+n₂) (m₁+m₂), SpinAmplitudes (n₁+n₂) q) :=
  (Real.sqrt (Fintype.card (Equiv.Perm.ModSumCongr (Fin n₁) (Fin n₂)) *
    Fintype.card (Equiv.Perm.ModSumCongr (Fin m₁) (Fin m₂))))⁻¹ •
      binaryClusterShuffleSum f h hfc hhc hfa hha hfs hhs

end LiebThirring
end
