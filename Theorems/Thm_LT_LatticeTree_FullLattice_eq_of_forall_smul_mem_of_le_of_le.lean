import Mathlib
import Definitions.Def_LatticeTreeOrbital
import P2M.Util
import P2M.Sol.S_LT_LatticeTree_FullLattice_eq_of_forall_smul_mem_of_le_of_le

set_option autoImplicit false

open LT.LatticeTree

theorem LT.LatticeTree.FullLattice.eq_of_forall_smul_mem_of_le_of_le
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K]
    (π : 𝒪) (hπ : Irreducible π) (M : FullLattice 𝒪 K) (R₁ R₂ : Submodule 𝒪 (Fin 2 → K))
    (hπM : ∀ v ∈ M.1, (algebraMap 𝒪 K π) • v ∈ R₁) (h₁₂ : R₁ ≤ R₂) (h₂M : R₂ ≤ M.1)
    (hne₁ : ∃ v ∈ R₁, ∀ w ∈ M.1, v ≠ (algebraMap 𝒪 K π) • w) (hne₂ : R₂ ≠ M.1) :
    R₁ = R₂ := by p2m_exact_reverting @_root_.P2MW.S_LT_LatticeTree_FullLattice_eq_of_forall_smul_mem_of_le_of_le.solution
