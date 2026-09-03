import Mathlib
import Definitions.Def_AlgebraicCurve_RelCartier
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_IdealSheafData_isInvertible_vanishingIdeal_closure_of_isRegularLocalRing

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

theorem AlgebraicGeometry.Scheme.IdealSheafData.isInvertible_vanishingIdeal_closure_of_isRegularLocalRing
    {Y : Scheme.{u}} [IsLocallyNoetherian Y] (η : Y)
    (hη : ringKrullDim (Y.presheaf.stalk η) = 1)
    (hreg : ∀ y ∈ closure ({η} : Set Y),
      IsRegularLocalRing (Y.presheaf.stalk y) ∧ ringKrullDim (Y.presheaf.stalk y) ≤ 2) :
    (Scheme.IdealSheafData.vanishingIdeal (X := Y) ⟨closure ({η} : Set Y), isClosed_closure⟩).IsInvertible := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_isInvertible_vanishingIdeal_closure_of_isRegularLocalRing.solution
