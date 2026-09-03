import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_exists_hom_restrict_eq_of_isOpenImmersion

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.exists_hom_restrict_eq_of_isOpenImmersion
    {X Y₀ Y₁ Y₀₁ : Scheme.{u}} (f₀ : Y₀ ⟶ X) (f₁ : Y₁ ⟶ X) [IsOpenImmersion f₀] [IsOpenImmersion f₁]
    (g₀ : Y₀₁ ⟶ Y₀) (g₁ : Y₀₁ ⟶ Y₁) [IsOpenImmersion g₀] [IsOpenImmersion g₁]
    (hg : g₀ ≫ f₀ = g₁ ≫ f₁) (hcov : f₀.opensRange ⊔ f₁.opensRange = ⊤)
    (hov : f₀.opensRange ⊓ f₁.opensRange ≤ (g₀ ≫ f₀).opensRange)
    {M N : X.Modules} (ψ₀ : M.restrict f₀ ⟶ N.restrict f₀) (ψ₁ : M.restrict f₁ ⟶ N.restrict f₁)
    (hψ : (Scheme.Modules.restrictFunctorComp g₀ f₀).hom.app M ≫ (Scheme.Modules.restrictFunctor g₀).map ψ₀ ≫
            (Scheme.Modules.restrictFunctorComp g₀ f₀).inv.app N =
          (Scheme.Modules.restrictFunctorCongr hg).hom.app M ≫
            (Scheme.Modules.restrictFunctorComp g₁ f₁).hom.app M ≫ (Scheme.Modules.restrictFunctor g₁).map ψ₁ ≫
            (Scheme.Modules.restrictFunctorComp g₁ f₁).inv.app N ≫ (Scheme.Modules.restrictFunctorCongr hg).inv.app N) :
    ∃ φ : M ⟶ N, (Scheme.Modules.restrictFunctor f₀).map φ = ψ₀ ∧ (Scheme.Modules.restrictFunctor f₁).map φ = ψ₁ := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_hom_restrict_eq_of_isOpenImmersion.solution
