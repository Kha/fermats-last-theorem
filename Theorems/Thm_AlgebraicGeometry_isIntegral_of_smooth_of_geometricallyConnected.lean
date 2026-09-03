import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_isIntegral_of_smooth_of_geometricallyConnected
attribute [-simp] RegularLocalRingQuotientAscent.dualNumberFst_apply

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.isIntegral_of_smooth_of_geometricallyConnected
    (k : Type u) [Field k] [IsAlgClosed k] {X : Scheme.{u}} (t : X ⟶ Spec (CommRingCat.of k))
    (hsm : Smooth t) (hgc : GeometricallyConnected t)
    (e : Spec (CommRingCat.of k) ⟶ X) (he : e ≫ t = 𝟙 _) :
    IsIntegral X := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_isIntegral_of_smooth_of_geometricallyConnected.solution
