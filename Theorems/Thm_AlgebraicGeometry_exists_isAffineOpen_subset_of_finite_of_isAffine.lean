import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_exists_isAffineOpen_subset_of_finite_of_isAffine

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.exists_isAffineOpen_subset_of_finite_of_isAffine
    {X : Scheme.{u}} [IsAffine X] (V : X.Opens) (F : Set V.toScheme) (hF : F.Finite) :
    ∃ W : (V.toScheme).Opens, IsAffineOpen W ∧ F ⊆ (W : Set V.toScheme) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_exists_isAffineOpen_subset_of_finite_of_isAffine.solution
