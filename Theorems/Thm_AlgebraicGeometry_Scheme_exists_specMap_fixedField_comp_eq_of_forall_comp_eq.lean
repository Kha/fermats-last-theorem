import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_exists_specMap_fixedField_comp_eq_of_forall_comp_eq

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.Scheme.exists_specMap_fixedField_comp_eq_of_forall_comp_eq
    {F L : Type u} [Field F] [Field L] [Algebra F L] (H : Subgroup (L ≃ₐ[F] L))
    {X : Scheme.{u}} (x : Spec (CommRingCat.of L) ⟶ X)
    (hx : ∀ σ ∈ H, Spec.map (CommRingCat.ofHom (σ : L ≃ₐ[F] L).toRingEquiv.toRingHom) ≫ x = x) :
    ∃ y : Spec (CommRingCat.of ↥(IntermediateField.fixedField H)) ⟶ X,
      Spec.map (CommRingCat.ofHom (algebraMap ↥(IntermediateField.fixedField H) L)) ≫ y = x := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_exists_specMap_fixedField_comp_eq_of_forall_comp_eq.solution
