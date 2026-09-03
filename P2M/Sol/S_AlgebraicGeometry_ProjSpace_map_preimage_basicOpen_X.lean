import Definitions.Def_AlgebraicGeometry_ProjSpace
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_ProjSpace_map_preimage_basicOpen_X

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

theorem solution (R A : Type u) [CommRing R] [CommRing A] [Algebra R A] (n : ℕ) (j : Fin (n + 1)) :
    ProjSpace.map R A n ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) (MvPolynomial.X j)
      = Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A) (MvPolynomial.X j) := by
  rw [ProjSpace.map_eq, AlgebraicGeometry.Proj.map_preimage_basicOpen]
  exact congrArg (AlgebraicGeometry.Proj.basicOpen _) (MvPolynomial.map_X _ j)

end
