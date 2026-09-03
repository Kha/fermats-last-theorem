import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_AdelicIndex
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_mem_principalRepartitions_iff_coe_mem_globalSub

namespace AlgebraicCurve
theorem mem_principalRepartitions_iff_coe_mem_globalSub {K F : Type*} [Field K] [Field F] [Algebra K F] {α : ↥(repartitions K F)} :
    α ∈ principalRepartitions K F ↔ (α : Place K F → F) ∈ globalSub K F := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_mem_principalRepartitions_iff_coe_mem_globalSub.solution
end AlgebraicCurve
