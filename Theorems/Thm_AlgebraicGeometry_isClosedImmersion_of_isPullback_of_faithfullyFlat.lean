import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_isClosedImmersion_of_isPullback_of_faithfullyFlat

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

theorem AlgebraicGeometry.isClosedImmersion_of_isPullback_of_faithfullyFlat
    {S : Type u} [CommRing S] (S' : Type u) [CommRing S'] [Algebra S S'] [Module.FaithfullyFlat S S']
    {X Y X' Y' : Scheme.{u}} (g : Y ⟶ Spec (CommRingCat.of S)) (g' : Y' ⟶ Spec (CommRingCat.of S')) (cY : Y' ⟶ Y)
    (hY : IsPullback cY g' g (Spec.map (CommRingCat.ofHom (algebraMap S S'))))
    (i : X ⟶ Y) (i' : X' ⟶ Y') (cX : X' ⟶ X) (hX : IsPullback cX i' i cY)
    (h : IsClosedImmersion i') :
    IsClosedImmersion i := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_isClosedImmersion_of_isPullback_of_faithfullyFlat.solution
