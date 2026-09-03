import Mathlib
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_FormalGroupLaw
import Definitions.Def_FormalGroup_NSeries
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_DrinfeldGlobal_ker_eq_span_of_originChartRing

set_option autoImplicit false

universe u

open AlgebraicGeometry CategoryTheory WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal IsLocalRing
  HomogeneousLocalization

attribute [local instance] MvPolynomial.gradedAlgebra

theorem WeierstrassCurve.DrinfeldGlobal.ker_eq_span_of_originChartRing
    {T : Type u} [CommRing T] (W : WeierstrassCurve T) (χ : OriginChartRing W →+* T)
    (hsc : ∀ t : T, χ (fromZeroRingHom (projModelGradingCR W) _ (algebraMap T ((projModelGradingCR W) 0) t)) = t) :
    RingHom.ker χ = Ideal.span
      {xOverY W - fromZeroRingHom (projModelGradingCR W) _ (algebraMap T ((projModelGradingCR W) 0) (χ (xOverY W))),
       zOverY W - fromZeroRingHom (projModelGradingCR W) _ (algebraMap T ((projModelGradingCR W) 0) (χ (zOverY W)))} := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_DrinfeldGlobal_ker_eq_span_of_originChartRing.solution
