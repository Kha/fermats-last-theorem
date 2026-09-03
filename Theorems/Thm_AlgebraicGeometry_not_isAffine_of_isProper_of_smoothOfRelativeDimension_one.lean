import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_not_isAffine_of_isProper_of_smoothOfRelativeDimension_one

open CategoryTheory AlgebraicGeometry

universe u
theorem AlgebraicGeometry.not_isAffine_of_isProper_of_smoothOfRelativeDimension_one {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    [IsIntegral X] [IsProper f] [SmoothOfRelativeDimension 1 f] : ¬ IsAffine X := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_not_isAffine_of_isProper_of_smoothOfRelativeDimension_one.solution
