import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_Hom_exists_comp_eq_of_isIntegralHom_of_surjective

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Hom.exists_comp_eq_of_isIntegralHom_of_surjective
    {X Y : Scheme.{0}} (f : X ⟶ Y) [IsIntegralHom f] [Surjective f]
    (k : Type) [Field k] [IsAlgClosed k] (y : Spec (CommRingCat.of k) ⟶ Y) :
    ∃ x : Spec (CommRingCat.of k) ⟶ X, x ≫ f = y := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Hom_exists_comp_eq_of_isIntegralHom_of_surjective.solution
