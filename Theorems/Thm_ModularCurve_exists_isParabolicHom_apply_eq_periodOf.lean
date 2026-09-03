import Mathlib
import Definitions.Def_ModularCurve_PeriodOf
import P2M.Util
import P2M.Sol.S_ModularCurve_exists_isParabolicHom_apply_eq_periodOf

set_option autoImplicit false

open UpperHalfPlane MeasureTheory
open scoped MatrixGroups Topology ComplexConjugate

theorem ModularCurve.exists_isParabolicHom_apply_eq_periodOf (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] :
    ∃ Φ : Additive Γ →+ Module.Dual ℂ (CuspForm Γ 2),
      ModularCurve.Period.IsParabolicHom Γ Φ ∧
        ∀ γ : Γ, Φ (Additive.ofMul γ) = ModularCurve.periodOf Γ γ := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_isParabolicHom_apply_eq_periodOf.solution
