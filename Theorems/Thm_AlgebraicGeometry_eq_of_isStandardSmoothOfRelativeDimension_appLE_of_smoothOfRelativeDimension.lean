import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_eq_of_isStandardSmoothOfRelativeDimension_appLE_of_smoothOfRelativeDimension

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.eq_of_isStandardSmoothOfRelativeDimension_appLE_of_smoothOfRelativeDimension
    {k : Type u} [Field k] {F : Scheme.{u}} (g : F ⟶ Spec (CommRingCat.of k)) (n : ℕ)
    (hg : SmoothOfRelativeDimension n g)
    (m : ℕ) (U : (Spec (CommRingCat.of k)).Opens) (W : F.Opens) (hW : IsAffineOpen W)
    (w : F) (hw : w ∈ W) (e : W ≤ g ⁻¹ᵁ U)
    (hm : (g.appLE U W e).hom.IsStandardSmoothOfRelativeDimension m) : m = n := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_eq_of_isStandardSmoothOfRelativeDimension_appLE_of_smoothOfRelativeDimension.solution
