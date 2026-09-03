import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_exists_isAffineOpen_mem_forall_preimage_eq_of_finite_group

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.exists_isAffineOpen_mem_forall_preimage_eq_of_finite_group
    (A : Type) [CommRing A] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of A)) [IsSeparated f]
    (haff : ∀ S : Set X, S.Finite → ∃ U : X.Opens, IsAffineOpen U ∧ S ⊆ (U : Set X))
    (G : Type) [Group G] [Finite G] (a : G →* Aut X) (ha : ∀ g : G, (a g).hom ≫ f = f) (x : X) :
    ∃ U : X.Opens, IsAffineOpen U ∧ x ∈ U ∧ ∀ g : G, (a g).hom ⁻¹ᵁ U = U := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_exists_isAffineOpen_mem_forall_preimage_eq_of_finite_group.solution
