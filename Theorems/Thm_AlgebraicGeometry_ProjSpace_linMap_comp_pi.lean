import Definitions.Def_AlgebraicGeometry_ProjSpaceLinMap
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_ProjSpace_linMap_comp_pi

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped BigOperators

attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.ProjSpace.linMap_comp_pi {R : Type u} [CommRing R] (n : ℕ)
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) R) (hM : IsUnit M) :
    ProjSpace.linMap R n M hM ≫ ProjSpace.π R n = ProjSpace.π R n := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_ProjSpace_linMap_comp_pi.solution
