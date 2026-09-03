import Mathlib
import Definitions.Def_ModularCurve_X1
import P2M.Util
import P2M.Sol.S_ModularCurve_mem_qExpFunctionFieldC_rat_iff_mem_intFormRatiosC

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped MatrixGroups

theorem ModularCurve.mem_qExpFunctionFieldC_rat_iff_mem_intFormRatiosC
    (Γ : Subgroup SL(2, ℤ)) (hΓ : (1 : ℝ) ∈ ((Γ : Subgroup (GL (Fin 2) ℝ))).strictPeriods)
    (x : LaurentSeries ℚ) :
    x ∈ ModularCurve.qExpFunctionFieldC ℚ Γ ↔ x ∈ ModularCurve.intFormRatiosC ℚ Γ := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_mem_qExpFunctionFieldC_rat_iff_mem_intFormRatiosC.solution
