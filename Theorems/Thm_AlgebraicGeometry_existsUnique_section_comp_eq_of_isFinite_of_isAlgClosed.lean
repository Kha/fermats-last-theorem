import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_existsUnique_section_comp_eq_of_isFinite_of_isAlgClosed

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.existsUnique_section_comp_eq_of_isFinite_of_isAlgClosed
    {κ : Type u} [Field κ] [IsAlgClosed κ] {k : Type u} [Field k] (j : κ →+* k)
    {Z : Scheme.{u}} (g : Z ⟶ Spec (CommRingCat.of κ)) [IsFinite g]
    (x : Spec (CommRingCat.of k) ⟶ Z) (hx : x ≫ g = Spec.map (CommRingCat.ofHom j)) :
    ∃! z : Spec (CommRingCat.of κ) ⟶ Z, z ≫ g = 𝟙 _ ∧ Spec.map (CommRingCat.ofHom j) ≫ z = x := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_existsUnique_section_comp_eq_of_isFinite_of_isAlgClosed.solution
