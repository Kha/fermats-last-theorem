import Mathlib
import Definitions.Def_ModularCurve_PeriodOf
import P2M.Util
import P2M.Sol.S_ModularCurve_addSubgroupClosure_range_periodAlongOf_eq_top

set_option autoImplicit false

open scoped MatrixGroups

theorem ModularCurve.addSubgroupClosure_range_periodAlongOf_eq_top
    (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] :
    AddSubgroup.closure
        (Set.range fun p : UpperHalfPlane × UpperHalfPlane =>
          ModularCurve.periodAlongOf Γ p.1 p.2) =
      (⊤ : AddSubgroup (Module.Dual ℂ (CuspForm Γ 2))) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_addSubgroupClosure_range_periodAlongOf_eq_top.solution
