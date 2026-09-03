import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_IgusaScheme
import Theorems.Thm_ModularCurve_IgusaScheme_exists_algHom_chartAlgInf_algebraMap_eq_coeff_zero
import P2M.Util
namespace P2MW.S_ModularCurve_IgusaScheme_exists_algHom_int_chartAlgInf_eq_coeff_zero

set_option autoImplicit false

open ModularCurve AlgebraicCurve.TwoChartIntegralModel

theorem solution (N : ℕ) [NeZero N] :
    ∃ φ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf ℤ ↥(modularFunctionFieldFull N)
        (ModularCurve.IgusaScheme.jFull N)) →ₐ[ℤ] ℤ,
      ∀ x : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf ℤ ↥(modularFunctionFieldFull N)
        (ModularCurve.IgusaScheme.jFull N)),
        ((φ x : ℤ) : ℚ) = ((x : ↥(modularFunctionFieldFull N)) : LaurentSeries ℚ).coeff 0 := by
  haveI : IsScalarTower ℤ ℚ ↥(modularFunctionFieldFull N) := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  obtain ⟨φ, hφ⟩ := ModularCurve.IgusaScheme.exists_algHom_chartAlgInf_algebraMap_eq_coeff_zero ℤ N
  exact ⟨φ, fun x => by rw [← hφ x]; rfl⟩
