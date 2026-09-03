import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_formallySmooth_cover_A0

universe u

open CategoryTheory

theorem AlgebraicGeometry.Scheme.TwoAffineOpenCover.formallySmooth_cover_A0 {R : Type u} [CommRing R] {X : AlgebraicGeometry.Scheme.{u}} (𝒱 : X.TwoAffineOpenCover)
    (c : X ⟶ AlgebraicGeometry.Spec (.of R)) [AlgebraicGeometry.Smooth c] :
    Algebra.FormallySmooth R (𝒱.cover c).A0 := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_formallySmooth_cover_A0.solution
