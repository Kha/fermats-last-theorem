import Mathlib
import Definitions.Def_AlgebraicCurve_RelCartier
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_IdealSheafData_isInvertible_ofIdealTop_span_singleton

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.IdealSheafData.isInvertible_ofIdealTop_span_singleton
    {X : Scheme.{u}} [IsAffine X] (r : Γ(X, ⊤)) (hr : r ∈ nonZeroDivisors Γ(X, ⊤)) :
    (Scheme.IdealSheafData.ofIdealTop (Ideal.span {r})).IsInvertible := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_isInvertible_ofIdealTop_span_singleton.solution
