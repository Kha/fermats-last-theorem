import Definitions.Def_CuspForm_HeckeLocal
import P2M.Util
import P2M.Sol.S_CuspForm_heckeLocal_adjoin_range_pi

theorem CuspForm.heckeLocal.adjoin_range_pi (N : ℕ) [NeZero N] (S : Set ℕ) (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪] (θ : CuspForm.heckeAlgebra N 2 S →+* IsLocalRing.ResidueField 𝒪) (hint : CuspForm.HasIntegralStructure N 2) : Algebra.adjoin 𝒪 (Set.range (CuspForm.heckeLocal.π N S 𝒪 θ)) = ⊤ := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_heckeLocal_adjoin_range_pi.solution
