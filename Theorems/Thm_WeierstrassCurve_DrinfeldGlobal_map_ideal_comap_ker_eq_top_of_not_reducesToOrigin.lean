import Mathlib
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_FormalGroupLaw
import Definitions.Def_FormalGroup_NSeries
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_DrinfeldGlobal_map_ideal_comap_ker_eq_top_of_not_reducesToOrigin

set_option autoImplicit false

universe u

open AlgebraicGeometry CategoryTheory WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal IsLocalRing
  HomogeneousLocalization

attribute [local instance] MvPolynomial.gradedAlgebra

theorem WeierstrassCurve.DrinfeldGlobal.map_ideal_comap_ker_eq_top_of_not_reducesToOrigin
    {T : Type u} [CommRing T] [IsLocalRing T] (W : WeierstrassCurve T) (P : Section W)
    (hP : ∀ χ : OriginChartRing W →+* T, ¬ ReducesToOrigin P χ (maximalIdeal T))
    (Φ : OriginChartRing W →+* PowerSeries T)
    (hΦsc : ∀ t : T, Φ (fromZeroRingHom (projModelGradingCR W) _ (algebraMap T ((projModelGradingCR W) 0) t)) =
      PowerSeries.C t)
    (hΦx : Φ (xOverY W) = - PowerSeries.X) (hΦz : Φ (zOverY W) = - W.formalW) :
    Ideal.map (Φ.comp (Scheme.ΓSpecIso (CommRingCat.of (OriginChartRing W))).hom.hom)
      (((Scheme.Hom.ker P.1).comap (originChartι W)).ideal ⟨⊤, AlgebraicGeometry.isAffineOpen_top _⟩) = ⊤ := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_DrinfeldGlobal_map_ideal_comap_ker_eq_top_of_not_reducesToOrigin.solution
