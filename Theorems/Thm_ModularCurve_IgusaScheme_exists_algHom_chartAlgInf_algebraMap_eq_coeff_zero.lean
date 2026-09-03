import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_IgusaScheme
import P2M.Util
import P2M.Sol.S_ModularCurve_IgusaScheme_exists_algHom_chartAlgInf_algebraMap_eq_coeff_zero

set_option autoImplicit false

open ModularCurve AlgebraicCurve.TwoChartIntegralModel
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

theorem ModularCurve.IgusaScheme.exists_algHom_chartAlgInf_algebraMap_eq_coeff_zero
    (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [Algebra R ℚ] [IsFractionRing R ℚ]
    (N : ℕ) [NeZero N] [Algebra R ↥(modularFunctionFieldFull N)] [IsScalarTower R ℚ ↥(modularFunctionFieldFull N)] :
    ∃ φ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf R ↥(modularFunctionFieldFull N)
        (ModularCurve.IgusaScheme.jFull N)) →ₐ[R] R,
      ∀ x : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf R ↥(modularFunctionFieldFull N)
        (ModularCurve.IgusaScheme.jFull N)),
        algebraMap R ℚ (φ x) = ((x : ↥(modularFunctionFieldFull N)) : LaurentSeries ℚ).coeff 0 := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_IgusaScheme_exists_algHom_chartAlgInf_algebraMap_eq_coeff_zero.solution
