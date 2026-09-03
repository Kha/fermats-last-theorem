import Definitions.Def_AlgebraicGeometry_ProjSpace
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_exists_isClosedImmersion_projSpace_pullback_of_isClosedImmersion

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra
theorem AlgebraicGeometry.exists_isClosedImmersion_projSpace_pullback_of_isClosedImmersion
    {R : Type u} [CommRing R] {X Y : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) (g : Y ⟶ Spec (CommRingCat.of R))
    (N : ℕ) (ιX : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R))
    (hιX : IsClosedImmersion ιX) (hιXf : ιX ≫ ProjSpace.π R N = f)
    (M : ℕ) (ιY : Y ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (M + 1)) R))
    (hιY : IsClosedImmersion ιY) (hιYg : ιY ≫ ProjSpace.π R M = g) :
    ∃ (K : ℕ) (ι : pullback f g ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (K + 1)) R)),
      K + 1 = (N + 1) * (M + 1) ∧ IsClosedImmersion ι ∧ ι ≫ ProjSpace.π R K = pullback.fst f g ≫ f := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_exists_isClosedImmersion_projSpace_pullback_of_isClosedImmersion.solution
