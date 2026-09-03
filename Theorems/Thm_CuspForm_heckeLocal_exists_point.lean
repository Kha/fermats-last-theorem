import Definitions.Def_CuspForm_HeckeLocal
import P2M.Util
import P2M.Sol.S_CuspForm_heckeLocal_exists_point

open CuspForm
theorem CuspForm.heckeLocal.exists_point (N : ℕ) [NeZero N] (S : Set ℕ)
    (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪]
    (θ : heckeAlgebra N 2 S →+* IsLocalRing.ResidueField 𝒪)
    (hint : HasIntegralStructure N 2)
    (χ : heckeAlgebra N 2 S →+* 𝒪) (hχ : ∀ t, IsLocalRing.residue 𝒪 (χ t) = θ t) :
    ∃ ψ : heckeLocal N S 𝒪 θ →ₐ[𝒪] 𝒪, ∀ t, ψ (heckeLocal.π N S 𝒪 θ t) = χ t := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_heckeLocal_exists_point.solution
