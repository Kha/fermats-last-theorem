import Mathlib
import Definitions.Def_ModularCurve_PeriodOf
import P2M.Util
import P2M.Sol.S_ModularCurve_periodAlongOf_apply_eq_sub_of_hasDerivAt

set_option autoImplicit false

open UpperHalfPlane
open scoped MatrixGroups

theorem ModularCurve.periodAlongOf_apply_eq_sub_of_hasDerivAt (Γ : Subgroup SL(2, ℤ))
    (f : CuspForm Γ 2) {F : UpperHalfPlane → ℂ}
    (hF : ∀ τ : UpperHalfPlane, HasDerivAt (F ∘ ofComplex) (f τ) (τ : ℂ)) (τ₀ τ₁ : UpperHalfPlane) :
    ModularCurve.periodAlongOf Γ τ₀ τ₁ f = F τ₁ - F τ₀ := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_periodAlongOf_apply_eq_sub_of_hasDerivAt.solution
