import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_germToFunctionField_app_eq_of_fromSpecStalk_comp_eq

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicCurve.germToFunctionField_app_eq_of_fromSpecStalk_comp_eq
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] (π : Y ⟶ X)
    (φ : X.functionField →+* Y.functionField)
    (hφπ : Y.fromSpecStalk (genericPoint Y) ≫ π =
      Spec.map (CommRingCat.ofHom φ) ≫ X.fromSpecStalk (genericPoint X))
    (U : X.Opens) [Nonempty (U : Scheme.{u})] [Nonempty ((π ⁻¹ᵁ U : Y.Opens) : Scheme.{u})] (s : Γ(X, U)) :
    (Y.germToFunctionField (π ⁻¹ᵁ U)).hom (π.app U s) = φ ((X.germToFunctionField U).hom s) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_germToFunctionField_app_eq_of_fromSpecStalk_comp_eq.solution
