import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_exists_ringAut_galois_sections_of_free_of_quotient

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open scoped TensorProduct

theorem AlgebraicGeometry.Scheme.exists_ringAut_galois_sections_of_free_of_quotient
    {X Y : Scheme.{u}} {G : Type v} [Group G] [Finite G] (ρ : G →* Aut X)
    (hadm : ∀ x : X, ∃ U : X.Opens, IsAffineOpen U ∧ x ∈ U ∧ ∀ g : G, (ρ g).hom ⁻¹ᵁ U = U)
    (π : X ⟶ Y) (hπ : ∀ g : G, (ρ g).hom ≫ π = π)
    (haff : IsAffineHom π) (hsurj : Function.Surjective π.base)
    (hfib : ∀ x x' : X, π.base x = π.base x' ↔ ∃ g : G, (ρ g).hom.base x = x')
    (hinj : ∀ V : Y.Opens, Function.Injective (π.app V))
    (hrange : ∀ V : Y.Opens, Set.range (π.app V) =
      {s | ∀ g : G, (ρ g).hom.appLE (π ⁻¹ᵁ V) (π ⁻¹ᵁ V) (by rw [← Scheme.Hom.comp_preimage, hπ g]) s = s})
    (hfree : ∀ (K : Type u) [Field K] (x : Spec (CommRingCat.of K) ⟶ X) (g : G), x ≫ (ρ g).hom = x → g = 1)
    (V : Y.Opens) (hV : IsAffineOpen V) :
    IsAffineOpen (π ⁻¹ᵁ V) ∧
    letI : Algebra Γ(Y, V) Γ(X, π ⁻¹ᵁ V) := (π.app V).hom.toAlgebra
    ∃ σ : G →* (Γ(X, π ⁻¹ᵁ V) ≃+* Γ(X, π ⁻¹ᵁ V)),
      (∀ (g : G) (a : Γ(X, π ⁻¹ᵁ V)),
        σ g a = (ρ g⁻¹).hom.appLE (π ⁻¹ᵁ V) (π ⁻¹ᵁ V) (by rw [← Scheme.Hom.comp_preimage, hπ g⁻¹]) a) ∧
      (∀ (g : G) (r : Γ(Y, V)), σ g (algebraMap Γ(Y, V) Γ(X, π ⁻¹ᵁ V) r) = algebraMap Γ(Y, V) Γ(X, π ⁻¹ᵁ V) r) ∧
      Function.Injective (algebraMap Γ(Y, V) Γ(X, π ⁻¹ᵁ V)) ∧
      (∀ a : Γ(X, π ⁻¹ᵁ V), (∀ g : G, σ g a = a) → a ∈ Set.range (algebraMap Γ(Y, V) Γ(X, π ⁻¹ᵁ V))) ∧
      (∀ P : Ideal Γ(X, π ⁻¹ᵁ V), P.IsPrime → ∀ g : G, g ≠ 1 → ∃ a : Γ(X, π ⁻¹ᵁ V), a - σ g a ∉ P) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_exists_ringAut_galois_sections_of_free_of_quotient.solution
