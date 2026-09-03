import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_exists_spec_map_comp_eq_of_forall_spec_map_comp_eq_of_forall_mem_iff

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.exists_spec_map_comp_eq_of_forall_spec_map_comp_eq_of_forall_mem_iff
    (Ω : Type) [Field Ω] (X : Scheme.{0}) (x : Spec (CommRingCat.of Ω) ⟶ X)
    (S : Set (Ω ≃+* Ω)) (hx : ∀ σ ∈ S, Spec.map (CommRingCat.ofHom (σ : Ω →+* Ω)) ≫ x = x)
    (F : Subfield Ω) (hF : ∀ a : Ω, a ∈ F ↔ ∀ σ ∈ S, σ a = a) :
    ∃ y : Spec (CommRingCat.of ↥F) ⟶ X, Spec.map (CommRingCat.ofHom F.subtype) ≫ y = x := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_exists_spec_map_comp_eq_of_forall_spec_map_comp_eq_of_forall_mem_iff.solution
