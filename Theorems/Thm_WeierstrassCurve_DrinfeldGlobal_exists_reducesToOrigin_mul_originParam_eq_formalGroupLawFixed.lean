import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_FormalGroup_DrinfeldBasis
import Definitions.Def_WeierstrassCurve_FormalGroupLaw
import Definitions.Def_WeierstrassCurve_FormalGroup
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_DrinfeldGlobal_exists_reducesToOrigin_mul_originParam_eq_formalGroupLawFixed
attribute [-instance] WeierstrassProjModel.quotGradingSubmoduleDegreeZeroFiniteType WeierstrassProjModel.kw_lrChart_tensorCommRing WeierstrassProjModel.kw_lrChart_biGrading_gradedAlgebra WeierstrassProjModel.projModel_isIso_spec_mapCR WeierstrassProjModel.kw_lrSymOC_isDomain_ℬ₀ WeierstrassProjModel.isProper_projModelStrCR WeierstrassProjModel.homogeneousSubmoduleDegreeZeroFiniteType
attribute [-simp] WeierstrassProjModel.kw_lrAdd_substHom_X WeierstrassProjModel.kw_lrSym_substHom_X WeierstrassProjModel.kw_lrThird_substHom_X WeierstrassCurve.DrinfeldGlobal.LevelTransport.mk.injEq WeierstrassCurve.DrinfeldGlobal.LevelTransport.mk.sizeOf_spec

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal IsLocalRing

attribute [local instance] MvPolynomial.gradedAlgebra

theorem WeierstrassCurve.DrinfeldGlobal.exists_reducesToOrigin_mul_originParam_eq_formalGroupLawFixed
    {A : Type} [CommRing A] [IsDomain A] [IsNoetherianRing A] (W : WeierstrassCurve A) [W.IsElliptic]
    (G₀ : RelativeGroupLaw (MvPowerSeries (Fin 2) A)
      (projModelStrCR (W.map (algebraMap A (MvPowerSeries (Fin 2) A)))))
    (hGpts : ∃ ev, IsPointsEval (W.map (algebraMap A (MvPowerSeries (Fin 2) A))) G₀ ev)
    (hGone : ∃ χ : OriginChartRing (W.map (algebraMap A (MvPowerSeries (Fin 2) A))) →+* MvPowerSeries (Fin 2) A,
      IsOriginChartSection (G₀.one (𝟙 _)) χ ∧
        χ (xOverY (W.map (algebraMap A (MvPowerSeries (Fin 2) A)))) = 0 ∧
        χ (zOverY (W.map (algebraMap A (MvPowerSeries (Fin 2) A)))) = 0)
    (P₁ P₂ : Section (W.map (algebraMap A (MvPowerSeries (Fin 2) A))))
    (χ₁ χ₂ : OriginChartRing (W.map (algebraMap A (MvPowerSeries (Fin 2) A))) →+* MvPowerSeries (Fin 2) A)
    (h₁ : ReducesToOrigin P₁ χ₁ (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) A), MvPowerSeries.X 1}))
    (h₂ : ReducesToOrigin P₂ χ₂ (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) A), MvPowerSeries.X 1}))
    (hz₁ : originParam χ₁ = MvPowerSeries.X 0) (hz₂ : originParam χ₂ = MvPowerSeries.X 1) :
    ∃ χ : OriginChartRing (W.map (algebraMap A (MvPowerSeries (Fin 2) A))) →+* MvPowerSeries (Fin 2) A,
      ReducesToOrigin (G₀.mul (𝟙 _) P₁ P₂) χ
        (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) A), MvPowerSeries.X 1}) ∧
      originParam χ = W.formalGroupLawFixed := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_DrinfeldGlobal_exists_reducesToOrigin_mul_originParam_eq_formalGroupLawFixed.solution
