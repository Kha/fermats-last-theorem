import Mathlib
import Definitions.Def_PresheafOfModules_InternalHom
import Theorems.Thm_PresheafOfModules_isMonoidal_inverseImage_W_toPresheaf
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_ModulesTensorPow
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_tensorHom_app_tensorSections
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_whiskerLeft_app_tensorSections

universe u

p2m_open "CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry"

set_option autoImplicit false

open AlgebraicGeometry AlgebraicGeometry.Scheme.Modules in

theorem solution
    {X : AlgebraicGeometry.Scheme.{u}} (L : X.Modules) {M M' : X.Modules} (ψ : M ⟶ M') {U : X.Opens}
    (s : Γ(L, U)) (t : Γ(M, U)) :
    (L ◁ ψ).app U (AlgebraicGeometry.Scheme.Modules.tensorSections s t) =
      AlgebraicGeometry.Scheme.Modules.tensorSections s (ψ.app U t) := by
  rw [← MonoidalCategory.id_tensorHom, AlgebraicGeometry.Scheme.Modules.tensorHom_app_tensorSections]
  all_goals rfl
