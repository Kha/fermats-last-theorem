import Mathlib
import Definitions.Def_AlgebraicGeometry_ModulesSectionZeroScheme
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_exists_hom_tensorUnit_app_eq_smul

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry Opposite

theorem AlgebraicGeometry.Scheme.Modules.exists_hom_tensorUnit_app_eq_smul
    {X : Scheme.{u}} (r : Γ(X, ⊤)) :
    ∃ t : 𝟙_ X.Modules ⟶ 𝟙_ X.Modules,
      (∀ (U : X.Opens) (m : Γ(𝟙_ X.Modules, U)),
        t.app U m = X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op r • m) ∧
      t.app ⊤ (Scheme.Modules.toUnitSection ⊤ 1) = r • Scheme.Modules.toUnitSection ⊤ 1 := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_hom_tensorUnit_app_eq_smul.solution
