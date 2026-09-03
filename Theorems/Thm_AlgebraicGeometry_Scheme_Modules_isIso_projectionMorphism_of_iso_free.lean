import Mathlib
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidal
import Definitions.Def_AlgebraicGeometry_ModulesProjectionMorphism
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_isIso_projectionMorphism_of_iso_free

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.isIso_projectionMorphism_of_iso_free
    {Z X : Scheme.{u}} (i : Z ⟶ X) {n : ℕ} (F : X.Modules)
    (e : F ≅ SheafOfModules.free.{u} (ULift.{u} (Fin n))) :
    IsIso (Scheme.Modules.projectionMorphism i F) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_isIso_projectionMorphism_of_iso_free.solution
