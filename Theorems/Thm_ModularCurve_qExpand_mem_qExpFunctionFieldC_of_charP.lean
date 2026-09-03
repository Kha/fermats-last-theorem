import Definitions.Def_ModularCurve_X1
import P2M.Util
import P2M.Sol.S_ModularCurve_qExpand_mem_qExpFunctionFieldC_of_charP

set_option autoImplicit false

open scoped MatrixGroups

theorem ModularCurve.qExpand_mem_qExpFunctionFieldC_of_charP
    (κ : Type*) [Field κ] (q : ℕ) [Fact q.Prime] [CharP κ q] (Γ : Subgroup SL(2, ℤ))
    (e : LaurentSeries κ) (he : e ∈ ModularCurve.qExpFunctionFieldC κ Γ) :
    ModularCurve.qExpand κ q e ∈ ModularCurve.qExpFunctionFieldC κ Γ := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_qExpand_mem_qExpFunctionFieldC_of_charP.solution
