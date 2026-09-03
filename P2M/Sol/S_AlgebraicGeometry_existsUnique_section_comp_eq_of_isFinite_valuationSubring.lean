import Mathlib
import Theorems.Thm_AlgebraicGeometry_existsUnique_section_comp_eq_of_universallyClosed_of_isSeparated
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_existsUnique_section_comp_eq_of_isFinite_valuationSubring

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem solution
    {L : Type u} [Field L] (O : ValuationSubring L)
    {Z : Scheme.{u}} (f : Z ⟶ Spec (CommRingCat.of ↥O)) [IsFinite f]
    (x : Spec (CommRingCat.of L) ⟶ Z) (hx : x ≫ f = Spec.map (CommRingCat.ofHom O.subtype)) :
    ∃! z : Spec (CommRingCat.of ↥O) ⟶ Z, z ≫ f = 𝟙 _ ∧ Spec.map (CommRingCat.ofHom O.subtype) ≫ z = x := by
  haveI : IsProper f := inferInstance
  haveI : UniversallyClosed f := inferInstance
  haveI : IsSeparated f := inferInstance
  exact AlgebraicGeometry.existsUnique_section_comp_eq_of_universallyClosed_of_isSeparated
    (R := ↥O) (K := L) f x hx
