import Definitions.Def_AlgebraicGeometry_ProjSpaceLinMap
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_ProjSpace_linMap_map_comp_map

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped BigOperators

attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.ProjSpace.linMap_map_comp_map {R A : Type u} [CommRing R] [CommRing A] [Algebra R A] (n : ℕ)
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) R) (hM : IsUnit M) (hMA : IsUnit (M.map (algebraMap R A))) :
    ProjSpace.linMap A n (M.map (algebraMap R A)) hMA ≫ ProjSpace.map R A n =
      ProjSpace.map R A n ≫ ProjSpace.linMap R n M hM := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_ProjSpace_linMap_map_comp_map.solution
