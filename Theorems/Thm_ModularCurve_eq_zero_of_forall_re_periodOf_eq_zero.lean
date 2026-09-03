import Mathlib
import Definitions.Def_ModularCurve_PeriodOf
import P2M.Util
import P2M.Sol.S_ModularCurve_eq_zero_of_forall_re_periodOf_eq_zero

set_option autoImplicit false

open scoped MatrixGroups

theorem ModularCurve.eq_zero_of_forall_re_periodOf_eq_zero (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex]
    (f : CuspForm Γ 2)
    (h : ∀ γ : Γ, (ModularCurve.periodOf Γ γ f).re = 0) : f = 0 := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_eq_zero_of_forall_re_periodOf_eq_zero.solution
