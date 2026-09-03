import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpace
import Definitions.Def_AlgebraicGeometry_ProjSpaceCover
import Definitions.Def_AlgebraicGeometry_ProjTwistDatum
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_ProjSpace_exists_twistObj_top_forall_res_eq_of_mem_H0_twist

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial TensorProduct

attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.ProjSpace.exists_twistObj_top_forall_res_eq_of_mem_H0_twist
    {A : Type u} [CommRing A] {n : ℕ} {Z : Scheme.{u}}
    (φ : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A)) [IsAffineHom φ] (m : ℕ)
    (c : (ProjSpace.twist (φ ≫ ProjSpace.π A n) φ m).cochain (ProjSpace.stdCoverPullback φ) 0)
    (hc : c ∈ (ProjSpace.twist (φ ≫ ProjSpace.π A n) φ m).H0 (ProjSpace.stdCoverPullback φ)) :
    ∃ g : ProjSpace.twistObj (φ ≫ ProjSpace.π A n) φ m ⊤,
      ∀ s : (ProjSpace.stdCoverPullback φ).Idx 0,
        (ProjSpace.twist (φ ≫ ProjSpace.π A n) φ m).res (le_top : (ProjSpace.stdCoverPullback φ).inter s ≤ ⊤) g = c s := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_ProjSpace_exists_twistObj_top_forall_res_eq_of_mem_H0_twist.solution
