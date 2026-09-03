import Mathlib
import Definitions.Def_AlgebraicCurve_RelCartier
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_comap_of_isReduced_of_forall_specializes

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.IdealSheafData.IsInvertible.comap_of_isReduced_of_forall_specializes
    {X Y : Scheme.{u}} [IsReduced X] {I : Y.IdealSheafData} (hI : I.IsInvertible) (g : X ⟶ Y)
    (h : ∀ ξ : X, (∀ y : X, y ⤳ ξ → y = ξ) → ξ ∉ ((I.comap g).support : Set X)) :
    (I.comap g).IsInvertible := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_comap_of_isReduced_of_forall_specializes.solution
