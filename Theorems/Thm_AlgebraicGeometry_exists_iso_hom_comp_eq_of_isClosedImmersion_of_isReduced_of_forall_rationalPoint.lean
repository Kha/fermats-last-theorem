import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_exists_iso_hom_comp_eq_of_isClosedImmersion_of_isReduced_of_forall_rationalPoint

set_option autoImplicit false

open scoped TensorProduct
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.exists_iso_hom_comp_eq_of_isClosedImmersion_of_isReduced_of_forall_rationalPoint
    {k : Type} [Field k] [IsAlgClosed k] {Y : Scheme.{0}} (f : Y ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f]
    {Z₁ Z₂ : Scheme.{0}} (i₁ : Z₁ ⟶ Y) (i₂ : Z₂ ⟶ Y) [IsClosedImmersion i₁] [IsClosedImmersion i₂]
    [IsReduced Z₁] [IsReduced Z₂]
    (h : ∀ y : Spec (CommRingCat.of k) ⟶ Y, y ≫ f = 𝟙 _ →
      ((∃ z : Spec (CommRingCat.of k) ⟶ Z₁, z ≫ i₁ = y) ↔ (∃ z : Spec (CommRingCat.of k) ⟶ Z₂, z ≫ i₂ = y))) :
    ∃ e : Z₁ ≅ Z₂, e.hom ≫ i₂ = i₁ := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_exists_iso_hom_comp_eq_of_isClosedImmersion_of_isReduced_of_forall_rationalPoint.solution
