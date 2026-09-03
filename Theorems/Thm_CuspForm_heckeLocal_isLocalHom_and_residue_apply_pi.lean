import Definitions.Def_CuspForm_HeckeLocal
import P2M.Util
import P2M.Sol.S_CuspForm_heckeLocal_isLocalHom_and_residue_apply_pi

set_option autoImplicit false

theorem CuspForm.heckeLocal.isLocalHom_and_residue_apply_pi
    (N : ℕ) [NeZero N] (S : Set ℕ) (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪]
    (θ : ↥(CuspForm.heckeAlgebra N 2 S) →+* IsLocalRing.ResidueField 𝒪)
    [Fact (CuspForm.HasIntegralStructure N 2)]
    {𝒪' : Type} [CommRing 𝒪'] [IsLocalRing 𝒪'] [Algebra 𝒪 𝒪'] [IsLocalHom (algebraMap 𝒪 𝒪')]
    (ψ : CuspForm.heckeLocal N S 𝒪 θ →ₐ[𝒪] 𝒪') :
    IsLocalHom (ψ : CuspForm.heckeLocal N S 𝒪 θ →+* 𝒪') ∧
    ∀ t : ↥(CuspForm.heckeAlgebra N 2 S),
      IsLocalRing.residue 𝒪' (ψ (CuspForm.heckeLocal.π N S 𝒪 θ t)) =
        IsLocalRing.ResidueField.map (algebraMap 𝒪 𝒪') (θ t) := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_heckeLocal_isLocalHom_and_residue_apply_pi.solution
