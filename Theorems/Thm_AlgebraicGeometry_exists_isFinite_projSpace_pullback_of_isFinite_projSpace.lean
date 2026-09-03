import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpace
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_exists_isFinite_projSpace_pullback_of_isFinite_projSpace

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry~exists_isClosedImmersion_projSpace_pullback_of_isClosedImmersion"

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.exists_isFinite_projSpace_pullback_of_isFinite_projSpace
    {R : Type u} [CommRing R] {X Y : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) (g : Y ⟶ Spec (CommRingCat.of R))
    (a : ℕ) (GX : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (a + 1)) R)) [IsFinite GX] (hGX : GX ≫ ProjSpace.π R a = f)
    (b : ℕ) (GY : Y ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (b + 1)) R)) [IsFinite GY] (hGY : GY ≫ ProjSpace.π R b = g) :
    ∃ (K : ℕ) (GP : pullback f g ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (K + 1)) R)),
      IsFinite GP ∧ GP ≫ ProjSpace.π R K = pullback.fst f g ≫ f := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_exists_isFinite_projSpace_pullback_of_isFinite_projSpace.solution
