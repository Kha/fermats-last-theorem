import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_Hom_natCard_le_finrank_of_isFinite

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Hom.natCard_le_finrank_of_isFinite
    {k : Type u} [Field k] {Z : Scheme.{u}} (z : Z ⟶ Spec (CommRingCat.of k)) [IsFinite z]
    (t : Spec (CommRingCat.of k)) :
    Nat.card Z ≤ Scheme.Hom.finrank z t := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Hom_natCard_le_finrank_of_isFinite.solution
