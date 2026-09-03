import Mathlib
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_PointChart
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import Definitions.Def_WeierstrassCurve_FormalGroupLaw
import P2M.Util
import P2M.Sol.S_WeierstrassProjModel_coeff_laurent_zChart_of_iso_of_kwZeroSect_comp_eq
attribute [-simp] MvPowerSeries.kw_coeff_pderiv FormalGroup.nthSeries_zero FormalGroup.evalNSMul_zero

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory NeronModelInfra WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal HomogeneousLocalization
attribute [local instance] MvPolynomial.gradedAlgebra

theorem WeierstrassProjModel.coeff_laurent_zChart_of_iso_of_kwZeroSect_comp_eq
    (T : Type) [CommRing T] [IsLocalRing T]
    (W W' : WeierstrassCurve T)
    (Ψ : projModelCR W.toProjective ≅ projModelCR W'.toProjective)
    (hΨ : Ψ.hom ≫ projModelStrCR W'.toProjective = projModelStrCR W.toProjective)
    (hΨO : (kwZeroSect T W).1 ≫ Ψ.hom = (kwZeroSect T W').1)
    (e : ZChartRing W'.toProjective →+* ZChartRing W.toProjective)
    (he : Spec.map (CommRingCat.ofHom e) ≫ zChartι W'.toProjective = zChartι W.toProjective ≫ Ψ.hom)
    (Φ : OriginChartRing W.toProjective →+* PowerSeries T)
    (hΦc : ∀ t : T, Φ (fromZeroRingHom (projModelGradingCR W.toProjective) _ (algebraMap T ((projModelGradingCR W.toProjective) 0) t)) =
      PowerSeries.C t)
    (hΦx : Φ (xOverY W.toProjective) = - PowerSeries.X) (hΦz : Φ (zOverY W.toProjective) = - W.formalW)
    (lam : ZChartRing W.toProjective →+* LaurentSeries T)
    (hlamc : ∀ t : T, lam (fromZeroRingHom (projModelGradingCR W.toProjective) _ (algebraMap T ((projModelGradingCR W.toProjective) 0) t)) =
      HahnSeries.C t)
    (hlamx : lam (xOverZ W.toProjective) * HahnSeries.ofPowerSeries ℤ T (Φ (zOverY W.toProjective)) =
      HahnSeries.ofPowerSeries ℤ T (Φ (xOverY W.toProjective)))
    (hlamy : lam (yOverZ W.toProjective) * HahnSeries.ofPowerSeries ℤ T (Φ (zOverY W.toProjective)) = 1) :
    (∀ n : ℤ, n < -2 → (lam (e (xOverZ W'.toProjective))).coeff n = 0) ∧
      IsUnit ((lam (e (xOverZ W'.toProjective))).coeff (-2)) ∧
      (∀ n : ℤ, n < -3 → (lam (e (yOverZ W'.toProjective))).coeff n = 0) ∧
      IsUnit ((lam (e (yOverZ W'.toProjective))).coeff (-3)) := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassProjModel_coeff_laurent_zChart_of_iso_of_kwZeroSect_comp_eq.solution
