import Mathlib
import Definitions.Def_ModularCurve_X1
import P2M.Util
import P2M.Sol.S_ModularCurve_exists_mem_qExpFunctionFieldC_single_mul_intSeriesC_mul_eq_of_mem_intFormRatiosC

set_option autoImplicit false

open scoped MatrixGroups

theorem ModularCurve.exists_mem_qExpFunctionFieldC_single_mul_intSeriesC_mul_eq_of_mem_intFormRatiosC
    (K : Type*) [Field K] (Γ : Subgroup SL(2, ℤ)) (hΓ : (1 : ℝ) ∈ ((Γ : Subgroup (GL (Fin 2) ℝ))).strictPeriods)
    (r : LaurentSeries K) (hr : r ∈ ModularCurve.intFormRatiosC K Γ) :
    ∃ (a b : LaurentSeries K) (m n : ℤ) (P Q : PowerSeries ℤ),
      a ∈ ModularCurve.qExpFunctionFieldC K Γ ∧ b ∈ ModularCurve.qExpFunctionFieldC K Γ ∧
      a = HahnSeries.single m 1 * ModularCurve.intSeriesC K P ∧
      b = HahnSeries.single n 1 * ModularCurve.intSeriesC K Q ∧
      b ≠ 0 ∧ r * b = a := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_mem_qExpFunctionFieldC_single_mul_intSeriesC_mul_eq_of_mem_intFormRatiosC.solution
