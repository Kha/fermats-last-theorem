import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_isPullback_specMap_awayToAwayRight_awayToAwayLeft

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.isPullback_specMap_awayToAwayRight_awayToAwayLeft
    {R : Type u} [CommRing R] (f g : R) :
    IsPullback
      (Spec.map (CommRingCat.ofHom (IsLocalization.Away.awayToAwayRight f g :
        Localization.Away f →+* Localization.Away (f * g))))
      (Spec.map (CommRingCat.ofHom (IsLocalization.Away.awayToAwayLeft g f :
        Localization.Away g →+* Localization.Away (f * g))))
      (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away f))))
      (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away g)))) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_isPullback_specMap_awayToAwayRight_awayToAwayLeft.solution
