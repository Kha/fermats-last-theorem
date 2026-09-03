import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_exists_isStandardSmoothOfRelativeDimension_appLE_fiberToSpecResidueField

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.exists_isStandardSmoothOfRelativeDimension_appLE_fiberToSpecResidueField
    {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X) (m : ℕ)
    (U : Y.Opens) (hU : IsAffineOpen U) (V : X.Opens) (hV : IsAffineOpen V) (hxV : x ∈ V) (e : V ≤ f ⁻¹ᵁ U)
    (h : (f.appLE U V e).hom.IsStandardSmoothOfRelativeDimension m) :
    ∃ (U' : (Spec (Y.residueField (f.base x))).Opens) (V' : (f.fiber (f.base x)).Opens) (_ : IsAffineOpen V')
      (_ : f.asFiber x ∈ V') (e' : V' ≤ (f.fiberToSpecResidueField (f.base x)) ⁻¹ᵁ U'),
      ((f.fiberToSpecResidueField (f.base x)).appLE U' V' e').hom.IsStandardSmoothOfRelativeDimension m := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_exists_isStandardSmoothOfRelativeDimension_appLE_fiberToSpecResidueField.solution
