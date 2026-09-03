import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_IsClosedImmersion_existsUnique_comp_eq_of_specMap_subtype_comp_eq

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.IsClosedImmersion.existsUnique_comp_eq_of_specMap_subtype_comp_eq
    {Ω : Type u} [Field Ω] (O : Subring Ω)
    {Y Z : Scheme.{u}} (ι : Z ⟶ Y) [IsClosedImmersion ι] (z : Spec (CommRingCat.of ↥O) ⟶ Y)
    (ψ : Spec (CommRingCat.of Ω) ⟶ Z) (hψ : ψ ≫ ι = Spec.map (CommRingCat.ofHom O.subtype) ≫ z) :
    ∃! χ : Spec (CommRingCat.of ↥O) ⟶ Z, χ ≫ ι = z := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_IsClosedImmersion_existsUnique_comp_eq_of_specMap_subtype_comp_eq.solution
