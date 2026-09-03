import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_TwoChartIntegralModel_germToFunctionField_jChartFin_mul_germToFunctionField_jInvChartInf

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve TopologicalSpace
universe u

theorem AlgebraicCurve.TwoChartIntegralModel.germToFunctionField_jChartFin_mul_germToFunctionField_jInvChartInf
    (R : Type u) [CommRing R] (F : Type u) [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)]
    {Y : Scheme.{u}} [IsIntegral Y] (f : Y ⟶ AlgebraicCurve.TwoChartIntegralModel R F j)
    [hU : Nonempty (Scheme.Opens.toScheme (f ⁻¹ᵁ ((TwoChartIntegralModel.ιFin R F j) ''ᵁ ⊤)))]
    [hV : Nonempty (Scheme.Opens.toScheme (f ⁻¹ᵁ ((TwoChartIntegralModel.ιInf R F j) ''ᵁ ⊤)))] :
    Y.germToFunctionField (f ⁻¹ᵁ ((TwoChartIntegralModel.ιFin R F j) ''ᵁ ⊤))
        (((f.app ((TwoChartIntegralModel.ιFin R F j) ''ᵁ ⊤)).hom
          (((TwoChartIntegralModel.ιFin R F j).appIso ⊤).inv
            ((Scheme.ΓSpecIso (CommRingCat.of ↥(TwoChartIntegralModel.chartAlgFin R F j))).inv
              (TwoChartIntegralModel.jChartFin R F j))))) *
      Y.germToFunctionField (f ⁻¹ᵁ ((TwoChartIntegralModel.ιInf R F j) ''ᵁ ⊤))
        (((f.app ((TwoChartIntegralModel.ιInf R F j) ''ᵁ ⊤)).hom
          (((TwoChartIntegralModel.ιInf R F j).appIso ⊤).inv
            ((Scheme.ΓSpecIso (CommRingCat.of ↥(TwoChartIntegralModel.chartAlgInf R F j))).inv
              (TwoChartIntegralModel.jInvChartInf R F j))))) = 1 := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_TwoChartIntegralModel_germToFunctionField_jChartFin_mul_germToFunctionField_jInvChartInf.solution
