import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_WeierstrassCurve_FormalGroupLaw
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Theorems.Thm_Ideal_map_algebraMap_localization_atPrime_eq_of_map_comp_eq_of_faithfullyFlat
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_exists_ringHom_localization_atPrime_powerSeries_comp_eq_and_faithfullyFlat
import P2M.Util
namespace P2MW.S_WeierstrassCurve_DrinfeldGlobal_map_algebraMap_localization_atPrime_eq_of_map_originChart_powerSeries_eq
attribute [-instance] WeierstrassProjModel.quotGradingSubmoduleDegreeZeroFiniteType WeierstrassProjModel.kw_lrChart_tensorCommRing WeierstrassProjModel.kw_lrChart_biGrading_gradedAlgebra WeierstrassProjModel.projModel_isIso_spec_mapCR WeierstrassProjModel.kw_lrSymOC_isDomain_ℬ₀ WeierstrassProjModel.isProper_projModelStrCR WeierstrassProjModel.homogeneousSubmoduleDegreeZeroFiniteType
attribute [-simp] WeierstrassProjModel.kw_lrAdd_substHom_X WeierstrassProjModel.kw_lrSym_substHom_X

set_option autoImplicit false

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal IsLocalRing HomogeneousLocalization

attribute [local instance] MvPolynomial.gradedAlgebra

theorem solution
    {T : Type} [CommRing T] [IsLocalRing T] [IsNoetherianRing T] [IsAdicComplete (maximalIdeal T) T]
    (W : WeierstrassCurve T)
    (Φ : OriginChartRing W →+* PowerSeries T)
    (hΦsc : ∀ t : T, Φ (fromZeroRingHom (projModelGradingCR W) _ (algebraMap T ((projModelGradingCR W) 0) t)) =
      PowerSeries.C t)
    (hΦx : Φ (xOverY W) = - PowerSeries.X) (hΦz : Φ (zOverY W) = - W.formalW)
    (I J : Ideal (OriginChartRing W)) (h : I.map Φ = J.map Φ) :
    I.map (algebraMap (OriginChartRing W)
      (Localization.AtPrime (Ideal.comap Φ (maximalIdeal (PowerSeries T))))) =
    J.map (algebraMap (OriginChartRing W)
      (Localization.AtPrime (Ideal.comap Φ (maximalIdeal (PowerSeries T))))) := by
  obtain ⟨ψ, hψ, hff⟩ :=
    WeierstrassCurve.DrinfeldGlobal.exists_ringHom_localization_atPrime_powerSeries_comp_eq_and_faithfullyFlat
      W Φ hΦsc hΦx hΦz
  refine Ideal.map_algebraMap_localization_atPrime_eq_of_map_comp_eq_of_faithfullyFlat
    (Ideal.comap Φ (maximalIdeal (PowerSeries T))) ψ hff I J ?_
  rw [hψ]
  exact h
