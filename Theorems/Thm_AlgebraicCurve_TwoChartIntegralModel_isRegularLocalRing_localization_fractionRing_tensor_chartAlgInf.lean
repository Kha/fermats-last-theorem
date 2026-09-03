import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_TwoChartIntegralModel_isRegularLocalRing_localization_fractionRing_tensor_chartAlgInf

set_option autoImplicit false

universe u

open scoped TensorProduct

theorem AlgebraicCurve.TwoChartIntegralModel.isRegularLocalRing_localization_fractionRing_tensor_chartAlgInf
    (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]
    (K₀ : Type u) [Field K₀] [Algebra R K₀] [IsFractionRing R K₀]
    (F : Type u) [Field F] [Algebra R F] [Algebra K₀ F] [IsScalarTower R K₀ F]
    (j : F) [Fact (j ≠ 0)] (htj : Transcendental R j)
    (hFD : FiniteDimensional ↥(IntermediateField.adjoin K₀ ({j} : Set F)) F)
    (hsep : Algebra.IsSeparable ↥(IntermediateField.adjoin K₀ ({j} : Set F)) F)
    (m : Ideal (K₀ ⊗[R] ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf R F j))) [m.IsMaximal] :
    IsRegularLocalRing (Localization.AtPrime m) ∧
      ringKrullDim (Localization.AtPrime m) = (1 : ℕ∞) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_TwoChartIntegralModel_isRegularLocalRing_localization_fractionRing_tensor_chartAlgInf.solution
