import Mathlib
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_DrinfeldGlobal_originChart_rel

set_option autoImplicit false

universe u

open AlgebraicGeometry CategoryTheory WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal IsLocalRing
  HomogeneousLocalization

attribute [local instance] MvPolynomial.gradedAlgebra

theorem WeierstrassCurve.DrinfeldGlobal.originChart_rel
    {T : Type u} [CommRing T] (W : WeierstrassCurve T) {B : Type u} [CommRing B] [Algebra T B]
    (χ : OriginChartRing W →+* B)
    (hsc : ∀ t : T, χ (fromZeroRingHom (projModelGradingCR W) _ (algebraMap T ((projModelGradingCR W) 0) t)) =
      algebraMap T B t) :
    χ (zOverY W) + algebraMap T B W.a₁ * χ (xOverY W) * χ (zOverY W) + algebraMap T B W.a₃ * χ (zOverY W) ^ 2 =
      χ (xOverY W) ^ 3 + algebraMap T B W.a₂ * χ (xOverY W) ^ 2 * χ (zOverY W) +
        algebraMap T B W.a₄ * χ (xOverY W) * χ (zOverY W) ^ 2 + algebraMap T B W.a₆ * χ (zOverY W) ^ 3 := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_DrinfeldGlobal_originChart_rel.solution
