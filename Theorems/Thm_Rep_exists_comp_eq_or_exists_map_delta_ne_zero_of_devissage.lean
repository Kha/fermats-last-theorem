import Mathlib
import P2M.Util
import P2M.Sol.S_Rep_exists_comp_eq_or_exists_map_delta_ne_zero_of_devissage

set_option autoImplicit false
open CategoryTheory

theorem Rep.exists_comp_eq_or_exists_map_delta_ne_zero_of_devissage
    {G : Type} [Group G] [Fintype G] (C : Rep ℤ G)
    (p : ℕ) [Fact p.Prime]
    {SB : ShortComplex (Rep ℤ G)} (hSB : SB.ShortExact) (hB₁ : ∀ b : SB.X₃, p • b = 0)

    {R_B P_B : Rep ℤ G} (f_B : R_B ⟶ P_B) (g_B : P_B ⟶ SB.X₁) (w_B : f_B ≫ g_B = 0)
    (hT_B : (ShortComplex.mk f_B g_B w_B).ShortExact)
    {R_I P_I : Rep ℤ G} (f_I : R_I ⟶ P_I) (g_I : P_I ⟶ SB.X₂) (w_I : f_I ≫ g_I = 0)
    (hT_I : (ShortComplex.mk f_I g_I w_I).ShortExact)
    {R₁ P₁ : Rep ℤ G} (f₁ : R₁ ⟶ P₁) (g₁ : P₁ ⟶ SB.X₃) (w₁ : f₁ ≫ g₁ = 0)
    (hT₁ : (ShortComplex.mk f₁ g₁ w₁).ShortExact)

    (ιR : R_B ⟶ R_I) (ιP : P_B ⟶ P_I) (sq₁ : f_B ≫ ιP = ιR ≫ f_I) (sq₂ : g_B ≫ SB.f = ιP ≫ g_I)
    (ρR : R_I ⟶ R₁) (ρP : P_I ⟶ P₁) (sq₃ : f_I ≫ ρP = ρR ≫ f₁) (sq₄ : g_I ≫ SB.g = ρP ≫ g₁)

    (hker : ∀ φ : R_B ⟶ C,
      (∀ y : groupCohomology SB.X₁ 1,
        (groupCohomology.map (MonoidHom.id G) φ 2).hom ((groupCohomology.δ hT_B 1 2 rfl).hom y) = 0) →
      ∃ (ψ : R_I ⟶ C) (χ : P_B ⟶ C), φ = ιR ≫ ψ + f_B ≫ χ)

    (hmid : ∀ ψ : R_I ⟶ C,
      (∃ χ : P_I ⟶ C, ψ = f_I ≫ χ) ∨
      (∃ y : groupCohomology SB.X₂ 1,
        (groupCohomology.map (MonoidHom.id G) ψ 2).hom ((groupCohomology.δ hT_I 1 2 rfl).hom y) ≠ 0))

    (hsurj : ∀ θ : groupCohomology SB.X₃ 1 →+ groupCohomology C 2,
      ∃ ϑ : R₁ ⟶ C, ∀ y : groupCohomology SB.X₃ 1,
        (groupCohomology.map (MonoidHom.id G) ϑ 2).hom ((groupCohomology.δ hT₁ 1 2 rfl).hom y) = θ y)
    (φ : R_B ⟶ C) :
    (∃ χ : P_B ⟶ C, φ = f_B ≫ χ) ∨
    (∃ y : groupCohomology SB.X₁ 1,
      (groupCohomology.map (MonoidHom.id G) φ 2).hom ((groupCohomology.δ hT_B 1 2 rfl).hom y) ≠ 0) := by p2m_exact_reverting @_root_.P2MW.S_Rep_exists_comp_eq_or_exists_map_delta_ne_zero_of_devissage.solution
