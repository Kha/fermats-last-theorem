import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_finrank_cotangentSpace_eq_of_smoothOfRelativeDimension

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.finrank_cotangentSpace_eq_of_smoothOfRelativeDimension
    {K : Type u} [Field K] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of K)) (n : ℕ)
    [SmoothOfRelativeDimension n f]
    (z : Spec (CommRingCat.of K) ⟶ X) (hz : z ≫ f = 𝟙 (Spec (CommRingCat.of K))) :
    Module.finrank
        (IsLocalRing.ResidueField (X.presheaf.stalk (z.base (IsLocalRing.closedPoint K))))
        (IsLocalRing.CotangentSpace (X.presheaf.stalk (z.base (IsLocalRing.closedPoint K)))) = n := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_finrank_cotangentSpace_eq_of_smoothOfRelativeDimension.solution
