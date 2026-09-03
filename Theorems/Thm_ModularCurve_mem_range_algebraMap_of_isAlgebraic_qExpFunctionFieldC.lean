import Mathlib
import Definitions.Def_ModularCurve_X1
import P2M.Util
import P2M.Sol.S_ModularCurve_mem_range_algebraMap_of_isAlgebraic_qExpFunctionFieldC

set_option autoImplicit false

open scoped MatrixGroups

theorem ModularCurve.mem_range_algebraMap_of_isAlgebraic_qExpFunctionFieldC
    (κ : Type*) [Field κ] (Γ : Subgroup SL(2, ℤ))
    (y : ↥(ModularCurve.qExpFunctionFieldC κ Γ)) (hy : IsAlgebraic κ y) :
    y ∈ (algebraMap κ ↥(ModularCurve.qExpFunctionFieldC κ Γ)).range := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_mem_range_algebraMap_of_isAlgebraic_qExpFunctionFieldC.solution
