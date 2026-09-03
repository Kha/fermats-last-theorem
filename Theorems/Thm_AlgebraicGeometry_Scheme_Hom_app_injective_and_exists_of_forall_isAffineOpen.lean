import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_Hom_app_injective_and_exists_of_forall_isAffineOpen

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.Scheme.Hom.app_injective_and_exists_of_forall_isAffineOpen
    {X Y₁ Y₂ : Scheme.{u}} (i₁ : Y₁ ⟶ X) (i₂ : Y₂ ⟶ X) (U : X.Opens)
    (h : ∀ (V : X.Opens), IsAffineOpen V → V ≤ U →
      Function.Injective (fun f : Γ(X, V) => ((i₁.app V) f, (i₂.app V) f)) ∧
        ∀ (g₁ : Γ(Y₁, i₁ ⁻¹ᵁ V)) (g₂ : Γ(Y₂, i₂ ⁻¹ᵁ V)),
          (pullback i₁ i₂).presheaf.map
              (eqToHom (show (pullback.snd i₁ i₂) ⁻¹ᵁ (i₂ ⁻¹ᵁ V) = (pullback.fst i₁ i₂) ⁻¹ᵁ (i₁ ⁻¹ᵁ V) by
                rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, pullback.condition])).op
            ((pullback.fst i₁ i₂).app (i₁ ⁻¹ᵁ V) g₁) =
            (pullback.snd i₁ i₂).app (i₂ ⁻¹ᵁ V) g₂ →
          ∃ f : Γ(X, V), (i₁.app V) f = g₁ ∧ (i₂.app V) f = g₂) :
    Function.Injective (fun f : Γ(X, U) => ((i₁.app U) f, (i₂.app U) f)) ∧
      ∀ (g₁ : Γ(Y₁, i₁ ⁻¹ᵁ U)) (g₂ : Γ(Y₂, i₂ ⁻¹ᵁ U)),
        (pullback i₁ i₂).presheaf.map
            (eqToHom (show (pullback.snd i₁ i₂) ⁻¹ᵁ (i₂ ⁻¹ᵁ U) = (pullback.fst i₁ i₂) ⁻¹ᵁ (i₁ ⁻¹ᵁ U) by
              rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, pullback.condition])).op
          ((pullback.fst i₁ i₂).app (i₁ ⁻¹ᵁ U) g₁) =
          (pullback.snd i₁ i₂).app (i₂ ⁻¹ᵁ U) g₂ →
        ∃ f : Γ(X, U), (i₁.app U) f = g₁ ∧ (i₂.app U) f = g₂ := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Hom_app_injective_and_exists_of_forall_isAffineOpen.solution
