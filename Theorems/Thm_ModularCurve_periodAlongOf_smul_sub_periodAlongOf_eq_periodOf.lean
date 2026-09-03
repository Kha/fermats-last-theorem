import Mathlib
import Definitions.Def_ModularCurve_PeriodOf
import P2M.Util
import P2M.Sol.S_ModularCurve_periodAlongOf_smul_sub_periodAlongOf_eq_periodOf

set_option autoImplicit false

open UpperHalfPlane
open scoped MatrixGroups

theorem ModularCurve.periodAlongOf_smul_sub_periodAlongOf_eq_periodOf
    (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (γ : Γ) (τ : UpperHalfPlane) :
    ModularCurve.periodAlongOf Γ UpperHalfPlane.I ((γ : SL(2, ℤ)) • τ) -
      ModularCurve.periodAlongOf Γ UpperHalfPlane.I τ = ModularCurve.periodOf Γ γ := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_periodAlongOf_smul_sub_periodAlongOf_eq_periodOf.solution
