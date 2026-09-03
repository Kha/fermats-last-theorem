import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_comp_section_comp_eq_of_isClosedMap_of_surjective_app

open AlgebraicGeometry CategoryTheory

universe u

theorem AlgebraicGeometry.comp_section_comp_eq_of_isClosedMap_of_surjective_app
    {X B Y : Scheme.{u}} (p : X ⟶ B) (ε : B ⟶ X) (hε : ε ≫ p = 𝟙 B)
    (hp : IsClosedMap p)
    (hH0 : ∀ U : B.Opens, IsAffineOpen U → Function.Surjective (p.app U))
    (f : X ⟶ Y) (hf : ∀ x : X, f (ε (p x)) = f x) :
    p ≫ ε ≫ f = f := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_comp_section_comp_eq_of_isClosedMap_of_surjective_app.solution
