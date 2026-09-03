import Mathlib
import Definitions.Def_AlgebraicGeometry_ThetaAdaptedFrame
import Definitions.Def_AlgebraicGeometry_ProjSpace
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_exists_isAffineOpen_forall_mem_forall_preimage_eq_of_isSeparated_of_finset

set_option autoImplicit false

attribute [local instance] MvPolynomial.gradedAlgebra

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation
open scoped BigOperators TensorProduct

theorem AlgebraicGeometry.Scheme.exists_isAffineOpen_forall_mem_forall_preimage_eq_of_isSeparated_of_finset
    {B : Type} [CommRing B] {X : Scheme.{0}} (πX : X ⟶ Spec (CommRingCat.of B)) (hsep : IsSeparated πX)
    (hAF : ∀ F : Finset X, ∃ U : X.Opens, IsAffineOpen U ∧ ∀ x ∈ F, x ∈ U)
    {G : Type} [Group G] [Finite G] (ρ : G →* Aut X) (F : Finset X) :
    ∃ U : X.Opens, IsAffineOpen U ∧ (∀ x ∈ F, x ∈ U) ∧ ∀ g : G, (ρ g).hom ⁻¹ᵁ U = U := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_exists_isAffineOpen_forall_mem_forall_preimage_eq_of_isSeparated_of_finset.solution
