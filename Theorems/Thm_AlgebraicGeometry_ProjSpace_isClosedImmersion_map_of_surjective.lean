import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpace
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_ProjSpace_isClosedImmersion_map_of_surjective

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.ProjSpace.isClosedImmersion_map_of_surjective
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A] (h : Function.Surjective (algebraMap R A)) (n : ℕ) :
    IsClosedImmersion (ProjSpace.map R A n) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_ProjSpace_isClosedImmersion_map_of_surjective.solution
