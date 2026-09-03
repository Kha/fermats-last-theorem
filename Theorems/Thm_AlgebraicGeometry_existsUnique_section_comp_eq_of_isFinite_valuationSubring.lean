import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_existsUnique_section_comp_eq_of_isFinite_valuationSubring

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.existsUnique_section_comp_eq_of_isFinite_valuationSubring
    {L : Type u} [Field L] (O : ValuationSubring L)
    {Z : Scheme.{u}} (f : Z ⟶ Spec (CommRingCat.of ↥O)) [IsFinite f]
    (x : Spec (CommRingCat.of L) ⟶ Z) (hx : x ≫ f = Spec.map (CommRingCat.ofHom O.subtype)) :
    ∃! z : Spec (CommRingCat.of ↥O) ⟶ Z, z ≫ f = 𝟙 _ ∧ Spec.map (CommRingCat.ofHom O.subtype) ≫ z = x := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_existsUnique_section_comp_eq_of_isFinite_valuationSubring.solution
