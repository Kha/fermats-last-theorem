import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_eq_of_specMap_comp_eq_of_field

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.eq_of_specMap_comp_eq_of_field
    {X : Scheme.{0}} {κ κ' : Type} [Field κ] [Field κ'] (i : κ →+* κ')
    (P Q : Spec (CommRingCat.of κ) ⟶ X)
    (h : Spec.map (CommRingCat.ofHom i) ≫ P = Spec.map (CommRingCat.ofHom i) ≫ Q) :
    P = Q := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_eq_of_specMap_comp_eq_of_field.solution
