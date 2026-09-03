import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_exists_isAlgClosed_factor_residueField_of_range_subset_singleton

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.exists_isAlgClosed_factor_residueField_of_range_subset_singleton
    {T : Scheme.{u}} (x : T)
    {k₁ : Type u} [Field k₁] (s₁ : Spec (CommRingCat.of k₁) ⟶ T) (hs₁ : Set.range ⇑s₁ ⊆ {x})
    {k₂ : Type u} [Field k₂] (s₂ : Spec (CommRingCat.of k₂) ⟶ T) (hs₂ : Set.range ⇑s₂ ⊆ {x}) :
    ∃ (ι₁ : T.residueField x ⟶ CommRingCat.of k₁) (ι₂ : T.residueField x ⟶ CommRingCat.of k₂)
      (Ω : Type u) (_ : Field Ω) (_ : IsAlgClosed Ω) (_ : Algebra k₁ Ω) (_ : Algebra k₂ Ω),
      Spec.map ι₁ ≫ T.fromSpecResidueField x = s₁ ∧
      Spec.map ι₂ ≫ T.fromSpecResidueField x = s₂ ∧
      ι₁ ≫ CommRingCat.ofHom (algebraMap k₁ Ω) = ι₂ ≫ CommRingCat.ofHom (algebraMap k₂ Ω) ∧
      Spec.map (CommRingCat.ofHom (algebraMap k₁ Ω)) ≫ s₁ =
        Spec.map (CommRingCat.ofHom (algebraMap k₂ Ω)) ≫ s₂ := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_exists_isAlgClosed_factor_residueField_of_range_subset_singleton.solution
