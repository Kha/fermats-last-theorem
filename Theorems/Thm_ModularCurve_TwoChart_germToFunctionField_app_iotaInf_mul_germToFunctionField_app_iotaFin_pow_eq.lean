import Mathlib
import Definitions.Def_ModularCurve_TwoChartModel
import P2M.Util
import P2M.Sol.S_ModularCurve_TwoChart_germToFunctionField_app_iotaInf_mul_germToFunctionField_app_iotaFin_pow_eq

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

universe u

theorem ModularCurve.TwoChart.germToFunctionField_app_iotaInf_mul_germToFunctionField_app_iotaFin_pow_eq
    (A : Type u) [CommRing A] (K : Type u) [Field K] [Algebra A K] (j : K) [Fact (j ≠ 0)]
    {Z : Scheme.{u}} [AlgebraicGeometry.IsIntegral Z] (h : Z ⟶ ModularCurve.TwoChartModel A K j)
    [Nonempty (Scheme.Opens.toScheme (h ⁻¹ᵁ ((ModularCurve.TwoChart.ιFin A K j) ''ᵁ ⊤)))]
    [Nonempty (Scheme.Opens.toScheme (h ⁻¹ᵁ ((ModularCurve.TwoChart.ιInf A K j) ''ᵁ ⊤)))]
    (b' : ↥(ModularCurve.TwoChart.chartAlgInf A K j)) (a : ↥(ModularCurve.TwoChart.chartAlgFin A K j)) (n : ℕ) (hab : (b' : K) * j ^ n = (a : K)) :
    (Z.germToFunctionField (h ⁻¹ᵁ ((ModularCurve.TwoChart.ιInf A K j) ''ᵁ ⊤)))
        ((h.app ((ModularCurve.TwoChart.ιInf A K j) ''ᵁ ⊤)).hom (((ModularCurve.TwoChart.ιInf A K j).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(ModularCurve.TwoChart.chartAlgInf A K j))).inv b'))) *
      ((Z.germToFunctionField (h ⁻¹ᵁ ((ModularCurve.TwoChart.ιFin A K j) ''ᵁ ⊤)))
        ((h.app ((ModularCurve.TwoChart.ιFin A K j) ''ᵁ ⊤)).hom (((ModularCurve.TwoChart.ιFin A K j).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(ModularCurve.TwoChart.chartAlgFin A K j))).inv (ModularCurve.TwoChart.jChartFin A K j))))) ^ n =
      (Z.germToFunctionField (h ⁻¹ᵁ ((ModularCurve.TwoChart.ιFin A K j) ''ᵁ ⊤)))
        ((h.app ((ModularCurve.TwoChart.ιFin A K j) ''ᵁ ⊤)).hom (((ModularCurve.TwoChart.ιFin A K j).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(ModularCurve.TwoChart.chartAlgFin A K j))).inv a))) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_TwoChart_germToFunctionField_app_iotaInf_mul_germToFunctionField_app_iotaFin_pow_eq.solution
