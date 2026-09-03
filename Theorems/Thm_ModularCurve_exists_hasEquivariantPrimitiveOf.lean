import Mathlib
import Definitions.Def_ModularCurve_PeriodOf
import P2M.Util
import P2M.Sol.S_ModularCurve_exists_hasEquivariantPrimitiveOf

set_option autoImplicit false

open scoped MatrixGroups

theorem ModularCurve.exists_hasEquivariantPrimitiveOf (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex]
    (f : CuspForm Γ 2) :
    ∃ F : UpperHalfPlane → ℂ, ModularCurve.HasEquivariantPrimitiveOf Γ f F := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_hasEquivariantPrimitiveOf.solution
