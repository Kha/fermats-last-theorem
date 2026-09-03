import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_IgusaScheme
import P2M.Util
import P2M.Sol.S_ModularCurve_IgusaScheme_exists_algHom_int_chartAlgInf_eq_coeff_zero

set_option autoImplicit false

open ModularCurve AlgebraicCurve.TwoChartIntegralModel
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

theorem ModularCurve.IgusaScheme.exists_algHom_int_chartAlgInf_eq_coeff_zero (N : ℕ) [NeZero N] :
    ∃ φ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf ℤ ↥(modularFunctionFieldFull N)
        (ModularCurve.IgusaScheme.jFull N)) →ₐ[ℤ] ℤ,
      ∀ x : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf ℤ ↥(modularFunctionFieldFull N)
        (ModularCurve.IgusaScheme.jFull N)),
        ((φ x : ℤ) : ℚ) = ((x : ↥(modularFunctionFieldFull N)) : LaurentSeries ℚ).coeff 0 := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_IgusaScheme_exists_algHom_int_chartAlgInf_eq_coeff_zero.solution
