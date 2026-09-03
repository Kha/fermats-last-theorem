import Mathlib
import Definitions.Def_ModularCurve_X1
import P2M.Util
import P2M.Sol.S_ModularCurve_mem_intFormRatiosC_of_coe_eq_intSeriesC_div
attribute [-simp] ModularCurve.baseAut_x1ArithFrobC_apply ModularCurve.coe_qExpCoeffRingAut_apply ModularCurve.qExpCoeffSemilinearAutHom_apply ModularCurve.baseAut_x1x0ArithFrobC_apply ModularCurve.baseAut_qExpArithFrobC_apply ModularCurve.baseAut_qExpCoeffSemilinearAut ModularCurve.toRingAut_qExpCoeffSemilinearAut

set_option autoImplicit false

theorem ModularCurve.mem_intFormRatiosC_of_coe_eq_intSeriesC_div
    (K : Type*) [Field K] (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ))
    (hT : ModularGroup.T ∈ Γ)
    (x : ModularCurve.qExpFunctionFieldC K Γ) (P Q : PowerSeries ℤ)
    (hQ : ModularCurve.intSeriesC K Q ≠ 0)
    (hx : (x : LaurentSeries K) = ModularCurve.intSeriesC K P / ModularCurve.intSeriesC K Q) :
    (x : LaurentSeries K) ∈ ModularCurve.intFormRatiosC K Γ := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_mem_intFormRatiosC_of_coe_eq_intSeriesC_div.solution
