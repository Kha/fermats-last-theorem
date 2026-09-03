import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_exists_iso_comp_homOfLE_eq_homOfLE_comp_of_preimage_eq

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u
theorem AlgebraicGeometry.Scheme.exists_iso_comp_homOfLE_eq_homOfLE_comp_of_preimage_eq
    {Y Y' : Scheme.{u}} (V : Y.Opens) (V' : Y'.Opens) (φ : (V : Scheme.{u}) ≅ (V' : Scheme.{u}))
    (Z : Y.Opens) (Z' : Y'.Opens) (hZ : Z ≤ V) (hZ' : Z' ≤ V')
    (hφ : φ.hom ⁻¹ᵁ (V'.ι ⁻¹ᵁ Z') = V.ι ⁻¹ᵁ Z) :
    ∃ τ : (Z : Scheme.{u}) ≅ (Z' : Scheme.{u}),
      τ.hom ≫ Y'.homOfLE hZ' = Y.homOfLE hZ ≫ φ.hom ∧
      τ.inv ≫ Y.homOfLE hZ = Y'.homOfLE hZ' ≫ φ.inv := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_exists_iso_comp_homOfLE_eq_homOfLE_comp_of_preimage_eq.solution
