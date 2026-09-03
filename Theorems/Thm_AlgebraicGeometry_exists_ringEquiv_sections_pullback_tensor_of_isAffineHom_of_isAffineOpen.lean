import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_exists_ringEquiv_sections_pullback_tensor_of_isAffineHom_of_isAffineOpen

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct

universe u

theorem AlgebraicGeometry.exists_ringEquiv_sections_pullback_tensor_of_isAffineHom_of_isAffineOpen
    {X Y Z : Scheme.{u}} (a : X ⟶ Z) (b : Y ⟶ Z) [IsAffineHom a] [IsAffineHom b]
    (U : Z.Opens) (hU : IsAffineOpen U)
    (hle₂ : (pullback.fst a b) ⁻¹ᵁ (a ⁻¹ᵁ U) ≤ (pullback.snd a b) ⁻¹ᵁ (b ⁻¹ᵁ U)) :
    letI : Algebra Γ(Z, U) Γ(X, a ⁻¹ᵁ U) := (a.app U).hom.toAlgebra
    letI : Algebra Γ(Z, U) Γ(Y, b ⁻¹ᵁ U) := (b.app U).hom.toAlgebra
    IsAffineOpen ((pullback.fst a b) ⁻¹ᵁ (a ⁻¹ᵁ U)) ∧
    ∃ τ : Γ(pullback a b, (pullback.fst a b) ⁻¹ᵁ (a ⁻¹ᵁ U)) ≃+* Γ(X, a ⁻¹ᵁ U) ⊗[Γ(Z, U)] Γ(Y, b ⁻¹ᵁ U),
      (∀ s : Γ(X, a ⁻¹ᵁ U), τ (((pullback.fst a b).app (a ⁻¹ᵁ U)).hom s) = s ⊗ₜ 1) ∧
      (∀ s' : Γ(Y, b ⁻¹ᵁ U),
        τ (((pullback.snd a b).appLE (b ⁻¹ᵁ U) ((pullback.fst a b) ⁻¹ᵁ (a ⁻¹ᵁ U)) hle₂).hom s') = 1 ⊗ₜ s') := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_exists_ringEquiv_sections_pullback_tensor_of_isAffineHom_of_isAffineOpen.solution
