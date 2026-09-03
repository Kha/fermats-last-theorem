import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpace
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_ProjSpace_flat_pi

set_option autoImplicit false

attribute [local instance] MvPolynomial.gradedAlgebra

open CategoryTheory AlgebraicGeometry

universe u

theorem AlgebraicGeometry.ProjSpace.flat_pi (R : Type u) [CommRing R] (n : ℕ) : Flat (ProjSpace.π R n) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_ProjSpace_flat_pi.solution
