import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules
import Definitions.Def_AlgebraicGeometry_ModulesPullbackLocalSection
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_exists_pullbackLocalSection_eq_of_iso_hom_comp_eq

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.exists_pullbackLocalSection_eq_of_iso_hom_comp_eq
    {X P X₀ : Scheme.{u}} (p : P ⟶ X) (e : X₀ ≅ P) (g : X₀ ⟶ X) (hge : e.hom ≫ p = g) (M : X.Modules)
    (h : ∀ y : Γ((Scheme.Modules.pullback p).obj M, p ⁻¹ᵁ ⊤),
      ∃ σ : Γ(M, ⊤), Scheme.Modules.pullbackLocalSection p σ = y)
    (s₀ : Γ((Scheme.Modules.pullback g).obj M, g ⁻¹ᵁ ⊤)) :
    ∃ σ : Γ(M, ⊤), Scheme.Modules.pullbackLocalSection g σ = s₀ := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_pullbackLocalSection_eq_of_iso_hom_comp_eq.solution
