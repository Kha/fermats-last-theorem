import Mathlib
import Definitions.Def_PresheafOfModules_InternalHom
import Theorems.Thm_PresheafOfModules_isMonoidal_inverseImage_W_toPresheaf
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_ModulesTensorPow
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_tensorHom_app_tensorSections
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_whiskerRight_app_tensorSections

universe u

p2m_open "CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry"

set_option autoImplicit false

open AlgebraicGeometry AlgebraicGeometry.Scheme.Modules in

theorem solution
    {X : AlgebraicGeometry.Scheme.{u}} {L L' : X.Modules} (φ : L ⟶ L') (M : X.Modules) {U : X.Opens}
    (s : Γ(L, U)) (t : Γ(M, U)) :
    (φ ▷ M).app U (AlgebraicGeometry.Scheme.Modules.tensorSections s t) =
      AlgebraicGeometry.Scheme.Modules.tensorSections (φ.app U s) t := by
  rw [← MonoidalCategory.tensorHom_id, AlgebraicGeometry.Scheme.Modules.tensorHom_app_tensorSections]
  all_goals rfl
