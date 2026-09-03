import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_flat_of_forall_isClosed_natCast_mem_nonZeroDivisors_stalk

set_option autoImplicit false

p2m_open "CategoryTheory AlgebraicGeometry~flat_iff_forall_appLE_mul_eq_zero_of_isDedekindDomain"

theorem AlgebraicGeometry.flat_of_forall_isClosed_natCast_mem_nonZeroDivisors_stalk
    {q : ℕ} [Fact q.Prime]
    {Y : Scheme.{0}} (πY : Y ⟶ Spec (CommRingCat.of ℤ_[q])) [LocallyOfFiniteType πY]
    (h : ∀ y : Y, IsClosed ({y} : Set Y) → πY y = IsLocalRing.closedPoint ℤ_[q] →
      ((q : ℕ) : Y.presheaf.stalk y) ∈ nonZeroDivisors (Y.presheaf.stalk y)) :
    Flat πY := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_flat_of_forall_isClosed_natCast_mem_nonZeroDivisors_stalk.solution
