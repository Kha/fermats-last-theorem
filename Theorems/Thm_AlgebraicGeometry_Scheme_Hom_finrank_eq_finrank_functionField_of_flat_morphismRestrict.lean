import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_Hom_finrank_eq_finrank_functionField_of_flat_morphismRestrict

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Hom.finrank_eq_finrank_functionField_of_flat_morphismRestrict
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] (π : X ⟶ Y) [IsFinite π] (hsurj : Function.Surjective π)
    (φ : Y.functionField →+* X.functionField)
    (hφ : X.fromSpecStalk (genericPoint X) ≫ π = Spec.map (CommRingCat.ofHom φ) ≫ Y.fromSpecStalk (genericPoint Y))
    (V : Y.Opens) [Flat (π ∣_ V)] [LocallyOfFinitePresentation (π ∣_ V)] (y : Y) (hy : y ∈ V) :
    π.finrank y = (letI := φ.toAlgebra; Module.finrank Y.functionField X.functionField) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Hom_finrank_eq_finrank_functionField_of_flat_morphismRestrict.solution
