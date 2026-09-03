import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_WeierstrassCurve_FormalGroupLaw
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_DrinfeldGlobal_graphOver_base_closedPoint_eq_of_reducesToOrigin

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra WeierstrassProjModel
  WeierstrassCurve.DrinfeldGlobal IsLocalRing HomogeneousLocalization

attribute [local instance] MvPolynomial.gradedAlgebra

theorem WeierstrassCurve.DrinfeldGlobal.graphOver_base_closedPoint_eq_of_reducesToOrigin
    {T : Type} [CommRing T] [IsLocalRing T] [IsAdicComplete (maximalIdeal T) T] (W : WeierstrassCurve T)
    (s : Section W) (χ : OriginChartRing W →+* T) (hs : ReducesToOrigin s χ (maximalIdeal T))
    (Φ : OriginChartRing W →+* PowerSeries T)
    (hΦsc : ∀ t : T, Φ (fromZeroRingHom (projModelGradingCR W) _ (algebraMap T ((projModelGradingCR W) 0) t)) =
      PowerSeries.C t)
    (hΦx : Φ (xOverY W) = - PowerSeries.X) (hΦz : Φ (zOverY W) = - W.formalW) :
    (graphOver (projModelStrCR W) s.1 s.2).base (IsLocalRing.closedPoint T) =
      (originChartι W ≫ toPullbackId).base
        (⟨Ideal.comap Φ (maximalIdeal (PowerSeries T)), inferInstance⟩ : PrimeSpectrum (OriginChartRing W)) := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_DrinfeldGlobal_graphOver_base_closedPoint_eq_of_reducesToOrigin.solution
