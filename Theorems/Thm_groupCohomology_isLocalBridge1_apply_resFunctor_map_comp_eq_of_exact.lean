import Mathlib
import Definitions.Def_GroupCohomology_LocalBridge
import P2M.Util
import P2M.Sol.S_groupCohomology_isLocalBridge1_apply_resFunctor_map_comp_eq_of_exact

set_option autoImplicit false
open CategoryTheory groupCohomology

theorem groupCohomology.isLocalBridge1_apply_resFunctor_map_comp_eq_of_exact
    {H : Type} [Group H] (r : H →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    {D D' : Type} [Group D] [Group D'] (π : H →* D) (π' : H →* D') (ψ : D' →* D)
    (hψ : ∀ h : H, ψ (π' h) = π h)

    {R P B : Rep ℤ D} (f : R ⟶ P) (g : P ⟶ B) (hg : Function.Surjective g.hom)
    (hfg : Function.Exact f.hom g.hom)
    {R' P' : Rep ℤ D'} (f' : R' ⟶ P') (g' : P' ⟶ Rep.res ψ B) (hg' : Function.Surjective g'.hom)
    (ρR : R' ⟶ Rep.res ψ R) (ρP : P' ⟶ Rep.res ψ P)
    (hsqf : ρR ≫ (Rep.resFunctor ψ).map f = f' ≫ ρP)
    (hsqg : ρP ≫ (Rep.resFunctor ψ).map g = g')

    {X : Rep ℤ D} {X' : Rep ℤ D'} {A : Rep ℤ H} (ι : X →+ A) (ι' : X' →+ A)
    (jX : Rep.res ψ X ⟶ X') (hj : ∀ x : X, ι' (jX.hom x) = ι x)
    (hιeq : ∀ (h : H) (x : X), ι (X.ρ (π h) x) = A.ρ h (ι x))

    {p : ℕ} {M : Rep (ZMod p) H} (κ : B →+ M →+ A)
    (hκ : ∀ c : B →+ A, ∃! m : M, ∀ b, κ b m = c b)
    (hκeq : ∀ (h : H) (b : B) (m : M), κ (B.ρ (π h) b) (M.ρ h m) = A.ρ h (κ b m))

    (hdiv : ∀ φ : R ⟶ X, ∃ χ : (ihom (Rep.res π P)).obj A,
      (∀ x : R, LinearMap.toAddMonoidHom χ (f.hom x) = ι (φ.hom x)) ∧
      ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
        ∀ s : H, r s ∈ F.fixingSubgroup → ∀ x : P, A.ρ s (LinearMap.toAddMonoidHom χ x) = LinearMap.toAddMonoidHom χ x)
    {Λ : (R ⟶ X) →+ H1 M} (hΛ : IsLocalBridge₁ π f g ι κ Λ)
    {Λ' : (R' ⟶ X') →+ H1 M} (hΛ' : IsLocalBridge₁ π' f' g' ι' κ Λ') :
    ∀ φ : R ⟶ X, Λ' (ρR ≫ (Rep.resFunctor ψ).map φ ≫ jX) = Λ φ := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_isLocalBridge1_apply_resFunctor_map_comp_eq_of_exact.solution
