import Definitions.Def_CuspForm_HeckeLocal
import P2M.Util
import P2M.Sol.S_CuspForm_heckeLocal_exists_algHom_of_subset

theorem CuspForm.heckeLocal.exists_algHom_of_subset
    (N : ℕ) [NeZero N] (S S₀ : Set ℕ) (hS : S₀ ⊆ S)
    (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪]
    [Fact (CuspForm.HasIntegralStructure N 2)]
    (θ₀ : CuspForm.heckeAlgebra N 2 S₀ →+* IsLocalRing.ResidueField 𝒪)
    (θ : CuspForm.heckeAlgebra N 2 S →+* IsLocalRing.ResidueField 𝒪)
    (hθ : ∀ t : CuspForm.heckeAlgebra N 2 S,
      θ t = θ₀ (Subalgebra.inclusion (CuspForm.heckeAlgebra_mono hS) t)) :
    ∃ Ψ : CuspForm.heckeLocal N S 𝒪 θ →ₐ[𝒪] CuspForm.heckeLocal N S₀ 𝒪 θ₀,
      IsLocalHom (Ψ : CuspForm.heckeLocal N S 𝒪 θ →+* CuspForm.heckeLocal N S₀ 𝒪 θ₀) ∧
      ∀ t : CuspForm.heckeAlgebra N 2 S,
        Ψ (CuspForm.heckeLocal.π N S 𝒪 θ t) =
          CuspForm.heckeLocal.π N S₀ 𝒪 θ₀ (Subalgebra.inclusion (CuspForm.heckeAlgebra_mono hS) t) := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_heckeLocal_exists_algHom_of_subset.solution
