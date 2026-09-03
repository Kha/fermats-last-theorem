import Definitions.Def_CuspForm_HeckeLocal
import P2M.Util
import P2M.Sol.S_CuspForm_heckeLocal_exists_factor_algHom

open CuspForm
theorem CuspForm.heckeLocal.exists_factor_algHom (N : ℕ) [NeZero N] (S : Set ℕ)
    (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪]
    (θ : heckeAlgebra N 2 S →+* IsLocalRing.ResidueField 𝒪)
    (hint : HasIntegralStructure N 2)
    (T : Type) [CommRing T] [IsLocalRing T] [Algebra 𝒪 T] [IsLocalHom (algebraMap 𝒪 T)]
    (π' : heckeAlgebra N 2 S →+* T)
    (hπ' : ∀ t, IsLocalRing.residue T (π' t) =
      IsLocalRing.ResidueField.map (algebraMap 𝒪 T) (θ t)) :
    ∃ f : heckeLocal N S 𝒪 θ →ₐ[𝒪] T,
      IsLocalHom f.toRingHom ∧ ∀ t, f (heckeLocal.π N S 𝒪 θ t) = π' t := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_heckeLocal_exists_factor_algHom.solution
