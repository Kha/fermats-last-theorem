import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_charZero_functionField_of_hom_spec_of_charZero

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct

theorem AlgebraicGeometry.charZero_functionField_of_hom_spec_of_charZero
    (X : Scheme.{0}) [IsIntegral X]
    (C : Type) [Field C] [CharZero C] (f : Spec (CommRingCat.of C) ⟶ X) :
    CharZero X.functionField := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_charZero_functionField_of_hom_spec_of_charZero.solution
