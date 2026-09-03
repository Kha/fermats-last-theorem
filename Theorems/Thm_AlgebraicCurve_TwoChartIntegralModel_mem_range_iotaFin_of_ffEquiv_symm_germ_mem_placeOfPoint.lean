import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_AlgebraicCurve_CurveModel
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_TwoChartIntegralModel_mem_range_iotaFin_of_ffEquiv_symm_germ_mem_placeOfPoint

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve

universe u v

theorem AlgebraicCurve.TwoChartIntegralModel.mem_range_iotaFin_of_ffEquiv_symm_germ_mem_placeOfPoint
    (R : Type u) [CommRing R] (F : Type u) [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)]
    {K : Type u} [Field K] {L : Type v} [Field L] [Algebra K L] (M : CurveModel K L)
    (Φ : M.C ⟶ AlgebraicCurve.TwoChartIntegralModel R F j)
    [hMne : Nonempty (Scheme.Opens.toScheme (Φ ⁻¹ᵁ ((TwoChartIntegralModel.ιFin R F j) ''ᵁ ⊤)))]
    (x : closedPoints M.C)
    (hj : M.ffEquiv.symm (M.C.germToFunctionField (Φ ⁻¹ᵁ ((TwoChartIntegralModel.ιFin R F j) ''ᵁ ⊤))
        ((Φ.app ((TwoChartIntegralModel.ιFin R F j) ''ᵁ ⊤)).hom (((TwoChartIntegralModel.ιFin R F j).appIso ⊤).inv
          ((Scheme.ΓSpecIso (CommRingCat.of ↥(TwoChartIntegralModel.chartAlgFin R F j))).inv (TwoChartIntegralModel.jChartFin R F j)))))
        ∈ (M.placeOfPoint x).toValuationSubring) :
    Φ.base x.1 ∈ Set.range (TwoChartIntegralModel.ιFin R F j).base := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_TwoChartIntegralModel_mem_range_iotaFin_of_ffEquiv_symm_germ_mem_placeOfPoint.solution
