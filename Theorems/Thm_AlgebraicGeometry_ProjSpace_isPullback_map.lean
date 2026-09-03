import Definitions.Def_AlgebraicGeometry_ProjSpace
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_ProjSpace_isPullback_map

open CategoryTheory AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

universe u
theorem AlgebraicGeometry.ProjSpace.isPullback_map (R A : Type u) [CommRing R] [CommRing A] [Algebra R A] (n : ℕ) :
    IsPullback (ProjSpace.map R A n) (ProjSpace.π A n) (ProjSpace.π R n)
      (Spec.map (CommRingCat.ofHom (algebraMap R A))) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_ProjSpace_isPullback_map.solution
