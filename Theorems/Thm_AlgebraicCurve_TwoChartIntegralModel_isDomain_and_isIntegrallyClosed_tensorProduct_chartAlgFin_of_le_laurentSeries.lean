import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_TwoChartIntegralModel_isDomain_and_isIntegrallyClosed_tensorProduct_chartAlgFin_of_le_laurentSeries
attribute [-simp] ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single

set_option autoImplicit false

open scoped TensorProduct
open AlgebraicCurve.TwoChartIntegralModel

universe u

theorem AlgebraicCurve.TwoChartIntegralModel.isDomain_and_isIntegrallyClosed_tensorProduct_chartAlgFin_of_le_laurentSeries
    (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R] [UniqueFactorizationMonoid R]
    (K₀ : Type u) [Field K₀] [CharZero K₀] [Algebra R K₀] [IsFractionRing R K₀]
    (F : IntermediateField K₀ (LaurentSeries K₀)) [Algebra R ↥F] [IsScalarTower R K₀ ↥F]
    (j : ↥F) [Fact (j ≠ 0)] (htj : Transcendental R j)
    (hFD : FiniteDimensional ↥(IntermediateField.adjoin K₀ ({j} : Set ↥F)) ↥F)
    (hsep : Algebra.IsSeparable ↥(IntermediateField.adjoin K₀ ({j} : Set ↥F)) ↥F)
    (L : Type u) [Field L] [Algebra K₀ L] [Algebra R L] [IsScalarTower R K₀ L] :
    IsDomain (L ⊗[R] ↥(chartAlgFin R ↥F j)) ∧ IsIntegrallyClosed (L ⊗[R] ↥(chartAlgFin R ↥F j)) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_TwoChartIntegralModel_isDomain_and_isIntegrallyClosed_tensorProduct_chartAlgFin_of_le_laurentSeries.solution
