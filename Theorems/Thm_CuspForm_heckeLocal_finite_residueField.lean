import Definitions.Def_CuspForm_HeckeLocal
import P2M.Util
import P2M.Sol.S_CuspForm_heckeLocal_finite_residueField

theorem CuspForm.heckeLocal.finite_residueField (N : ℕ) [NeZero N] (S : Set ℕ) (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪] (θ : ↥(CuspForm.heckeAlgebra N 2 S) →+* IsLocalRing.ResidueField 𝒪) [Fact (CuspForm.HasIntegralStructure N 2)] [Finite (IsLocalRing.ResidueField 𝒪)] : Finite (IsLocalRing.ResidueField (CuspForm.heckeLocal N S 𝒪 θ)) := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_heckeLocal_finite_residueField.solution
