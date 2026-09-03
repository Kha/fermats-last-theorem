import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_existsUnique_section_of_forall_away

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open scoped TensorProduct

universe u

theorem AlgebraicGeometry.Scheme.existsUnique_section_of_forall_away
    {S : Type u} [CommRing S] {k : ℕ} (r : Fin k → S) (hr : Ideal.span (Set.range r) = ⊤)
    (B : Fin k → Type u) [∀ i, CommRing (B i)] [∀ i, Algebra S (B i)] [∀ i, IsLocalization.Away (r i) (B i)]
    {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of S))
    (σ : ∀ i, Spec (CommRingCat.of (B i)) ⟶ A)
    (hσ : ∀ i, σ i ≫ f = Spec.map (CommRingCat.ofHom (algebraMap S (B i))))
    (hagree : ∀ (i j : Fin k) (C : Type u) [CommRing C] [Algebra S C] [IsLocalization.Away (r i * r j) C]
      (ρ₁ : B i →ₐ[S] C) (ρ₂ : B j →ₐ[S] C),
      Spec.map (CommRingCat.ofHom ρ₁.toRingHom) ≫ σ i = Spec.map (CommRingCat.ofHom ρ₂.toRingHom) ≫ σ j) :
    ∃ σ₀ : Spec (CommRingCat.of S) ⟶ A, σ₀ ≫ f = 𝟙 _ ∧
      (∀ i, Spec.map (CommRingCat.ofHom (algebraMap S (B i))) ≫ σ₀ = σ i) ∧
      ∀ σ₁ : Spec (CommRingCat.of S) ⟶ A, (∀ i, Spec.map (CommRingCat.ofHom (algebraMap S (B i))) ≫ σ₁ = σ i) → σ₁ = σ₀ := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_existsUnique_section_of_forall_away.solution
