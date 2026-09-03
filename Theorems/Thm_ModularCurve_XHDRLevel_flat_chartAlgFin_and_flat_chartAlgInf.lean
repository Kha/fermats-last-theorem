import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import P2M.Util
import P2M.Sol.S_ModularCurve_XHDRLevel_flat_chartAlgFin_and_flat_chartAlgInf

set_option autoImplicit false

open AlgebraicCurve ModularCurve ModularCurve.XHDRLevel
open scoped MatrixGroups

theorem ModularCurve.XHDRLevel.flat_chartAlgFin_and_flat_chartAlgInf
    (p : ℕ) (Γ : Subgroup SL(2, ℤ)) (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ))) :
    Module.Flat (R p) ↥(chartAlgFin p Γ hj) ∧ Module.Flat (R p) ↥(chartAlgInf p Γ hj) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_XHDRLevel_flat_chartAlgFin_and_flat_chartAlgInf.solution
