import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_isIso_of_isFinite_of_finrank_closedPoint_eq_one

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.isIso_of_isFinite_of_finrank_closedPoint_eq_one
    (K : Type) [Field K] {Z : Scheme.{0}} (p : Z ⟶ Spec (CommRingCat.of K)) [IsFinite p]
    (h : p.finrank (IsLocalRing.closedPoint K) = 1) :
    IsIso p := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_isIso_of_isFinite_of_finrank_closedPoint_eq_one.solution
