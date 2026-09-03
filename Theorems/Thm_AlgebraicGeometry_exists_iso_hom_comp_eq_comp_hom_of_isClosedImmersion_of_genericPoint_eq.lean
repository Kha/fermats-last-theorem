import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_exists_iso_hom_comp_eq_comp_hom_of_isClosedImmersion_of_genericPoint_eq

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.exists_iso_hom_comp_eq_comp_hom_of_isClosedImmersion_of_genericPoint_eq
    {S Z C : Scheme.{u}} (q : Z ⟶ S) (c : C ⟶ S) (i : C ⟶ Z) [IsClosedImmersion i] [IsIntegral C]
    (hi : i ≫ q = c) (g : Z ≅ Z) (hg : g.hom ≫ q = q)
    (hfix : g.hom.base (i.base (genericPoint C)) = i.base (genericPoint C)) :
    ∃ α : C ≅ C, α.hom ≫ c = c ∧ α.hom ≫ i = i ≫ g.hom := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_exists_iso_hom_comp_eq_comp_hom_of_isClosedImmersion_of_genericPoint_eq.solution
