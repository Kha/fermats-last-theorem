import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_smoothOfRelativeDimension_one_of_forall_nonempty_adicCompletion_stalk_ringEquiv_powerSeries
attribute [-instance] AdicCompletion.instIsLocalRingMaximalIdeal

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry IsLocalRing

theorem AlgebraicGeometry.smoothOfRelativeDimension_one_of_forall_nonempty_adicCompletion_stalk_ringEquiv_powerSeries
    (k : Type u) [Field k] [IsAlgClosed k] {Y : Scheme.{u}} (g : Y ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType g]
    (h : ∀ y : ↥Y, IsClosed ({y} : Set ↥Y) →
      Nonempty (AdicCompletion (maximalIdeal (Y.presheaf.stalk y)) (Y.presheaf.stalk y) ≃+* PowerSeries k)) :
    SmoothOfRelativeDimension 1 g := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_smoothOfRelativeDimension_one_of_forall_nonempty_adicCompletion_stalk_ringEquiv_powerSeries.solution
