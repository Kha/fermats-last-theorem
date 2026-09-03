import Mathlib.RingTheory.WittVector.DiscreteValuationRing
import Mathlib.RingTheory.WittVector.Complete
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import P2M.Util
import P2M.Sol.S_WittVector_exists_ringHom_isLocalHom_and_residue_comp_eq_comp_constantCoeff

theorem WittVector.exists_ringHom_isLocalHom_and_residue_comp_eq_comp_constantCoeff (p : ℕ) [Fact p.Prime]
    (k₀ : Type) [Field k₀] [Finite k₀] [CharP k₀ p]
    (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪]
    (hp𝒪 : (p : 𝒪) ∈ IsLocalRing.maximalIdeal 𝒪)
    (f : k₀ →+* IsLocalRing.ResidueField 𝒪) :
    ∃ g : WittVector p k₀ →+* 𝒪, IsLocalHom g ∧
      (IsLocalRing.residue 𝒪).comp g =
        f.comp (WittVector.constantCoeff : WittVector p k₀ →+* k₀) := by p2m_exact_reverting @_root_.P2MW.S_WittVector_exists_ringHom_isLocalHom_and_residue_comp_eq_comp_constantCoeff.solution
