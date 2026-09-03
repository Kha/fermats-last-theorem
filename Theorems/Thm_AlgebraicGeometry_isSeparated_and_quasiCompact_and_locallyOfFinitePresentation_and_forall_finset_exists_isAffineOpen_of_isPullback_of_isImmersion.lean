import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpace
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_isSeparated_and_quasiCompact_and_locallyOfFinitePresentation_and_forall_finset_exists_isAffineOpen_of_isPullback_of_isImmersion

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.isSeparated_and_quasiCompact_and_locallyOfFinitePresentation_and_forall_finset_exists_isAffineOpen_of_isPullback_of_isImmersion
    {R : Type} [CommRing R] [IsNoetherianRing R] {M : ℕ} {H : Scheme.{0}}
    (j : H ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (M + 1)) R))
    [IsImmersion j] [LocallyOfFiniteType j] [QuasiCompact j]
    (𝒪 : Type) [CommRing 𝒪] [Algebra R 𝒪]
    {H' : Scheme.{0}} (π' : H' ⟶ Spec (CommRingCat.of 𝒪)) (g : H' ⟶ H)
    (hg : IsPullback g π' (j ≫ ProjSpace.π R M) (Spec.map (CommRingCat.ofHom (algebraMap R 𝒪)))) :
    IsSeparated π' ∧ QuasiCompact π' ∧ LocallyOfFinitePresentation π' ∧
      (∀ F : Finset H', ∃ V : H'.Opens, IsAffineOpen V ∧ ∀ x ∈ F, x ∈ V) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_isSeparated_and_quasiCompact_and_locallyOfFinitePresentation_and_forall_finset_exists_isAffineOpen_of_isPullback_of_isImmersion.solution
