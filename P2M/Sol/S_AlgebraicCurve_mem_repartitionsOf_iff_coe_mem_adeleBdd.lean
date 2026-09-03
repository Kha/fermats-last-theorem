import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_AdelicIndex
import P2M.Util
namespace P2MW.S_AlgebraicCurve_mem_repartitionsOf_iff_coe_mem_adeleBdd

set_option autoImplicit false

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Divisor repartitions repartitionsOf adeleBdd"
p2m_open "AlgebraicCurve"

open WithZero

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

end AlgebraicCurve

open _root_.AlgebraicCurve _root_.P2MW.S_AlgebraicCurve_mem_repartitionsOf_iff_coe_mem_adeleBdd.AlgebraicCurve WithZero in
theorem solution {K F : Type*} [Field K] [Field F] [Algebra K F] {D : Divisor K F} {α : ↥(repartitions K F)} :
    α ∈ repartitionsOf D ↔ (α : Place K F → F) ∈ adeleBdd D := Iff.rfl
