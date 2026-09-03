import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
import Definitions.Def_AlgebraicCurve_RelCartier
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_IdealSheafData_isInvertible_of_isInvertible_comap

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.IdealSheafData.isInvertible_of_isInvertible_comap
    {X Y : Scheme.{u}} (π : Y ⟶ X) [IsFinite π] [Flat π] [Surjective π]
    (I : X.IdealSheafData) (h : (I.comap π).IsInvertible) : I.IsInvertible := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_isInvertible_of_isInvertible_comap.solution
