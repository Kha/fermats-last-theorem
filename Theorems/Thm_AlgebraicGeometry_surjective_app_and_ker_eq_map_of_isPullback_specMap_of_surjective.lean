import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_surjective_app_and_ker_eq_map_of_isPullback_specMap_of_surjective

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

theorem AlgebraicGeometry.surjective_app_and_ker_eq_map_of_isPullback_specMap_of_surjective
    {A A' : CommRingCat.{u}} (φ : A ⟶ A') (hφ : Function.Surjective φ.hom)
    {Y Y' : Scheme.{u}} {g : Y' ⟶ Y} {iY : Y ⟶ Spec A} {iY' : Y' ⟶ Spec A'}
    (H : IsPullback g iY' iY (Spec.map φ))
    (W : Y.Opens) (hW : IsAffineOpen W) :
    Function.Surjective (g.app W).hom ∧
      RingHom.ker (g.app W).hom = Ideal.map ((Scheme.ΓSpecIso A).inv ≫ iY.appLE ⊤ W le_top).hom (RingHom.ker φ.hom) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_surjective_app_and_ker_eq_map_of_isPullback_specMap_of_surjective.solution
