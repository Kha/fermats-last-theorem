import Mathlib
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidal
import Definitions.Def_AlgebraicGeometry_ModulesProjectionMorphism
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_pullback_map_projectionMorphism_comp_counit

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry"

theorem solution
    {Z X : Scheme.{u}} (i : Z ⟶ X) (F : X.Modules) :
    (Scheme.Modules.pullback i).map (Scheme.Modules.projectionMorphism i F) ≫
        (Scheme.Modules.pullbackPushforwardAdjunction i).counit.app ((Scheme.Modules.pullback i).obj F) =
      Scheme.Modules.projectionMorphismMate i F := by
  have h := Adjunction.homEquiv_counit (adj := Scheme.Modules.pullbackPushforwardAdjunction i)
    (g := Scheme.Modules.projectionMorphism i F)
  rw [Scheme.Modules.projectionMorphism_def, Equiv.symm_apply_apply] at h
  rw [Scheme.Modules.projectionMorphism_def]
  exact h.symm
