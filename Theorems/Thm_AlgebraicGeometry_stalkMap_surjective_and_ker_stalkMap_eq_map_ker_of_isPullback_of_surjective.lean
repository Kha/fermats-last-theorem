import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_stalkMap_surjective_and_ker_stalkMap_eq_map_ker_of_isPullback_of_surjective

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.stalkMap_surjective_and_ker_stalkMap_eq_map_ker_of_isPullback_of_surjective
    {O κ : Type u} [CommRing O] [CommRing κ] (q : O →+* κ) (hq : Function.Surjective q)
    {X Y : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of O)) (g : Y ⟶ X) (t : Y ⟶ Spec (CommRingCat.of κ))
    (H : IsPullback g t f (Spec.map (CommRingCat.ofHom q))) (y : Y) :
    Function.Surjective (g.stalkMap y).hom ∧
      RingHom.ker (g.stalkMap y).hom =
        Ideal.map ((X.presheaf.germ ⊤ (g.base y) trivial).hom.comp
          ((f.appTop).hom.comp (Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom)) (RingHom.ker q) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_stalkMap_surjective_and_ker_stalkMap_eq_map_ker_of_isPullback_of_surjective.solution
