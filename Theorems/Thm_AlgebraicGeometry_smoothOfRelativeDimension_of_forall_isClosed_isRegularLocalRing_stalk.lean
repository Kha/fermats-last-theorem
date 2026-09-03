import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_smoothOfRelativeDimension_of_forall_isClosed_isRegularLocalRing_stalk

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry IsLocalRing

theorem AlgebraicGeometry.smoothOfRelativeDimension_of_forall_isClosed_isRegularLocalRing_stalk
    (k : Type u) [Field k] [IsAlgClosed k] {Y : Scheme.{u}} (g : Y ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType g] (n : ℕ)
    (h : ∀ y : ↥Y, IsClosed ({y} : Set ↥Y) →
      IsRegularLocalRing (Y.presheaf.stalk y) ∧ ringKrullDim (Y.presheaf.stalk y) = (n : ℕ∞)) :
    SmoothOfRelativeDimension n g := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_smoothOfRelativeDimension_of_forall_isClosed_isRegularLocalRing_stalk.solution
