import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_IsClosedImmersion_exists_ringEquiv_residueField_functionField_of_isIntegral

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

universe u

theorem AlgebraicGeometry.IsClosedImmersion.exists_ringEquiv_residueField_functionField_of_isIntegral
    {C Y : Scheme.{u}} [IsIntegral C] (i : C ⟶ Y) [IsClosedImmersion i] :
    ∃ θ : Y.residueField (i.base (genericPoint C)) ≃+* C.functionField,
      ∀ s : Y.presheaf.stalk (i.base (genericPoint C)),
        θ ((Y.residue (i.base (genericPoint C))).hom s) = (i.stalkMap (genericPoint C)).hom s := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_IsClosedImmersion_exists_ringEquiv_residueField_functionField_of_isIntegral.solution
