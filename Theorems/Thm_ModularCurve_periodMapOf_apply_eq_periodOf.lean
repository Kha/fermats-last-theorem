import Mathlib
import Definitions.Def_ModularCurve_PeriodOf
import P2M.Util
import P2M.Sol.S_ModularCurve_periodMapOf_apply_eq_periodOf

set_option autoImplicit false

open scoped MatrixGroups

theorem ModularCurve.periodMapOf_apply_eq_periodOf (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex]
    (f : CuspForm Γ 2) (γ : Γ) :
    ModularCurve.periodMapOf Γ f (Additive.ofMul γ) = ModularCurve.periodOf Γ γ f := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_periodMapOf_apply_eq_periodOf.solution
