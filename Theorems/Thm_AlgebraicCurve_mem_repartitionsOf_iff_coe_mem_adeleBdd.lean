import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_AdelicIndex
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_mem_repartitionsOf_iff_coe_mem_adeleBdd

namespace AlgebraicCurve
theorem mem_repartitionsOf_iff_coe_mem_adeleBdd {K F : Type*} [Field K] [Field F] [Algebra K F] {D : Divisor K F} {α : ↥(repartitions K F)} :
    α ∈ repartitionsOf D ↔ (α : Place K F → F) ∈ adeleBdd D := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_mem_repartitionsOf_iff_coe_mem_adeleBdd.solution
end AlgebraicCurve
