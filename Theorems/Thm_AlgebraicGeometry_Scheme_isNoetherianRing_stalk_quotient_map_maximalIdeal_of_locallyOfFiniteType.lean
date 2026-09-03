import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_isNoetherianRing_stalk_quotient_map_maximalIdeal_of_locallyOfFiniteType

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory IsLocalRing

theorem AlgebraicGeometry.Scheme.isNoetherianRing_stalk_quotient_map_maximalIdeal_of_locallyOfFiniteType
    (A : Type) [CommRing A] [IsLocalRing A]
    (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of A)) [LocallyOfFiniteType f]
    (x : X) (hx : f.base x = closedPoint A) :
    IsNoetherianRing
      ((X.presheaf.stalk x) ⧸ Ideal.map
        ((X.presheaf.germ ⊤ x trivial).hom.comp (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom))
        (maximalIdeal A)) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_isNoetherianRing_stalk_quotient_map_maximalIdeal_of_locallyOfFiniteType.solution
