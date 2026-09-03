import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_SheafOfModules_MonoidalV2
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_unitHom_app_eq_mul

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.unitHom_app_eq_mul
    {X : Scheme.{u}} (c : 𝟙_ X.Modules ⟶ 𝟙_ X.Modules) (U : X.Opens) (m : Γ(𝟙_ X.Modules, U)) :
    (show Γ(X, U) from c.app U m) =
      X.presheaf.map (homOfLE (le_top (a := U))).op (show Γ(X, ⊤) from c.app ⊤ (1 : Γ(X, ⊤))) *
        (show Γ(X, U) from m) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_unitHom_app_eq_mul.solution
