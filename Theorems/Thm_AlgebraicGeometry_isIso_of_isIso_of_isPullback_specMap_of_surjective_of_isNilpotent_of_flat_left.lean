import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_isIso_of_isIso_of_isPullback_specMap_of_surjective_of_isNilpotent_of_flat_left

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.isIso_of_isIso_of_isPullback_specMap_of_surjective_of_isNilpotent_of_flat_left
    {P B' : Type} [CommRing P] [CommRing B'] (π : P →+* B') (hπ : Function.Surjective π) (hn : IsNilpotent (RingHom.ker π))
    {X Y X' Y' : Scheme.{0}} (fX : X ⟶ Spec (CommRingCat.of P)) [Flat fX] (fY : Y ⟶ Spec (CommRingCat.of P))
    (u : X ⟶ Y) (hu : u ≫ fY = fX)
    (fX' : X' ⟶ Spec (CommRingCat.of B')) (fY' : Y' ⟶ Spec (CommRingCat.of B'))
    (iX : X' ⟶ X) (hiX : IsPullback iX fX' fX (Spec.map (CommRingCat.ofHom π)))
    (iY : Y' ⟶ Y) (hiY : IsPullback iY fY' fY (Spec.map (CommRingCat.ofHom π)))
    (u' : X' ⟶ Y') (hu' : iX ≫ u = u' ≫ iY) [IsIso u'] :
    IsIso u := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_isIso_of_isIso_of_isPullback_specMap_of_surjective_of_isNilpotent_of_flat_left.solution
