import Mathlib
import Definitions.Def_AlgebraicCurve_RelCartier
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_of_comap_of_support_subset_range

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.IdealSheafData.IsInvertible.of_comap_of_support_subset_range
    {W X : Scheme.{u}} (j : W ⟶ X) [IsOpenImmersion j] (I : X.IdealSheafData)
    (hsupp : (I.support : Set ↥X) ⊆ Set.range ⇑j) (h : (I.comap j).IsInvertible) :
    I.IsInvertible := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_of_comap_of_support_subset_range.solution
