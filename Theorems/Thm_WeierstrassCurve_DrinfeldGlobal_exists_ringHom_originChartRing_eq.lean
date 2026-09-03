import Mathlib
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_DrinfeldGlobal_exists_ringHom_originChartRing_eq

set_option autoImplicit false

universe u

open AlgebraicGeometry CategoryTheory WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal IsLocalRing
  HomogeneousLocalization

attribute [local instance] MvPolynomial.gradedAlgebra

theorem WeierstrassCurve.DrinfeldGlobal.exists_ringHom_originChartRing_eq
    {T : Type u} [CommRing T] (W : WeierstrassCurve T) {B : Type u} [CommRing B] [Algebra T B] (x v : B)
    (h : v + algebraMap T B W.a₁ * x * v + algebraMap T B W.a₃ * v ^ 2 =
      x ^ 3 + algebraMap T B W.a₂ * x ^ 2 * v + algebraMap T B W.a₄ * x * v ^ 2 + algebraMap T B W.a₆ * v ^ 3) :
    ∃ χ : OriginChartRing W →+* B,
      (∀ t : T, χ (fromZeroRingHom (projModelGradingCR W) _ (algebraMap T ((projModelGradingCR W) 0) t)) =
        algebraMap T B t) ∧ χ (xOverY W) = x ∧ χ (zOverY W) = v := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_DrinfeldGlobal_exists_ringHom_originChartRing_eq.solution
