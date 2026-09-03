import Mathlib
import Definitions.Def_ModularCurve_PeriodOf
import P2M.Util
import P2M.Sol.S_ModularCurve_periodMapOf_mem_parabolicHoms

set_option autoImplicit false

open scoped MatrixGroups

theorem ModularCurve.periodMapOf_mem_parabolicHoms (Γ : Subgroup SL(2, ℤ)) (f : CuspForm Γ 2) :
    ModularCurve.periodMapOf Γ f ∈ ModularCurve.Period.parabolicHoms ℂ Γ ℂ := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_periodMapOf_mem_parabolicHoms.solution
