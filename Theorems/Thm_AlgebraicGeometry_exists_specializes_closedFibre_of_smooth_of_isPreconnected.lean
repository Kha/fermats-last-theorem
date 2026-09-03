import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_exists_specializes_closedFibre_of_smooth_of_isPreconnected
attribute [-simp] RegularLocalRingQuotientAscent.dualNumberFst_apply

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry Opposite

theorem AlgebraicGeometry.exists_specializes_closedFibre_of_smooth_of_isPreconnected
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {G : Scheme.{u}} (g : G ⟶ Spec (CommRingCat.of R)) [Smooth g] [QuasiCompact g]
    (hne : ∃ x : G, g.base x = IsLocalRing.closedPoint R)
    (hconn : _root_.IsPreconnected {x : G | g.base x = IsLocalRing.closedPoint R}) :
    ∃ η : G, g.base η = IsLocalRing.closedPoint R ∧
      (∀ x : G, g.base x = IsLocalRing.closedPoint R → η ⤳ x) ∧
      (∀ y : G, y ⤳ η → g.base y = IsLocalRing.closedPoint R → y = η) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_exists_specializes_closedFibre_of_smooth_of_isPreconnected.solution
