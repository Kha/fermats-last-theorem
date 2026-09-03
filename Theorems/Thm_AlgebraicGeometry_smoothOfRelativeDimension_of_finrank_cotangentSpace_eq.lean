import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_smoothOfRelativeDimension_of_finrank_cotangentSpace_eq

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.smoothOfRelativeDimension_of_finrank_cotangentSpace_eq
    {K : Type u} [Field K] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of K))
    [Smooth f] [IrreducibleSpace X]
    (z : Spec (CommRingCat.of K) ⟶ X) (hz : z ≫ f = 𝟙 (Spec (CommRingCat.of K))) (n : ℕ)
    (hn : Module.finrank
        (IsLocalRing.ResidueField (X.presheaf.stalk (z.base (IsLocalRing.closedPoint K))))
        (IsLocalRing.CotangentSpace (X.presheaf.stalk (z.base (IsLocalRing.closedPoint K)))) = n) :
    SmoothOfRelativeDimension n f := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_smoothOfRelativeDimension_of_finrank_cotangentSpace_eq.solution
