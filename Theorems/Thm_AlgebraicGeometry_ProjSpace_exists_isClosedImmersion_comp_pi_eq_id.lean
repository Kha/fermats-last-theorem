import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpace
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_ProjSpace_exists_isClosedImmersion_comp_pi_eq_id

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.ProjSpace.exists_isClosedImmersion_comp_pi_eq_id
    (R : Type u) [CommRing R] (r : ℕ) :
    ∃ σ : Spec (CommRingCat.of R) ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) R),
      IsClosedImmersion σ ∧ σ ≫ ProjSpace.π R r = 𝟙 _ := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_ProjSpace_exists_isClosedImmersion_comp_pi_eq_id.solution
