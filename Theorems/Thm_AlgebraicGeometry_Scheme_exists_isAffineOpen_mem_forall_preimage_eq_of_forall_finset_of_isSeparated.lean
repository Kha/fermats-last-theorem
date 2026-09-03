import Mathlib
import Definitions.Def_AlgebraicGeometry_OModulePresheafHom
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_exists_isAffineOpen_mem_forall_preimage_eq_of_forall_finset_of_isSeparated

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

theorem AlgebraicGeometry.Scheme.exists_isAffineOpen_mem_forall_preimage_eq_of_forall_finset_of_isSeparated
    {R : Type u} [CommRing R] {X : Scheme.{u}} (π : X ⟶ Spec (.of R)) [IsSeparated π]
    {G : Type v} [Group G] [Finite G] (ρ : G →* Aut X)
    (hAF : ∀ F : Finset X, ∃ U : X.Opens, IsAffineOpen U ∧ ∀ x ∈ F, x ∈ U)
    (x : X) : ∃ U : X.Opens, IsAffineOpen U ∧ x ∈ U ∧ ∀ g : G, (ρ g).hom ⁻¹ᵁ U = U := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_exists_isAffineOpen_mem_forall_preimage_eq_of_forall_finset_of_isSeparated.solution
