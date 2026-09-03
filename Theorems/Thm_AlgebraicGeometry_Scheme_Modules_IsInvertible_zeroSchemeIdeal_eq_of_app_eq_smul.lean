import Definitions.Def_AlgebraicGeometry_ModulesSectionZeroScheme
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_zeroSchemeIdeal_eq_of_app_eq_smul

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.IsInvertible.zeroSchemeIdeal_eq_of_app_eq_smul
    {X : Scheme.{u}} {M : X.Modules} (hM : Scheme.Modules.IsInvertible M)
    (s₁ s₂ : 𝟙_ X.Modules ⟶ M) (u : Γ(X, ⊤)) (hu : IsUnit u)
    (h : s₂.app ⊤ (Scheme.Modules.toUnitSection ⊤ 1) = u • s₁.app ⊤ (Scheme.Modules.toUnitSection ⊤ 1)) :
    Scheme.Modules.zeroSchemeIdeal s₁ = Scheme.Modules.zeroSchemeIdeal s₂ := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_zeroSchemeIdeal_eq_of_app_eq_smul.solution
