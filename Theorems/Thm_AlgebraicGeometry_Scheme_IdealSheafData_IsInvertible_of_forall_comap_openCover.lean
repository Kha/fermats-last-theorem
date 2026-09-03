import Mathlib
import Definitions.Def_AlgebraicCurve_RelCartier
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_of_forall_comap_openCover

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.IdealSheafData.IsInvertible.of_forall_comap_openCover
    {X : Scheme.{u}} (𝒰 : X.OpenCover) (I : X.IdealSheafData)
    (h : ∀ i, (I.comap (𝒰.f i)).IsInvertible) : I.IsInvertible := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_of_forall_comap_openCover.solution
