import Mathlib
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_ModulesRigidify
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RigidifiedLineBundleOfInvertible
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_nonempty_iso_pullback_pullback_of_rigidify_iso_unit
set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry"

theorem solution
    {T P : Scheme.{u}} (σ : T ⟶ P) (q : P ⟶ T) {L : P.Modules} (hL : Scheme.Modules.IsInvertible L)
    (e : Nonempty (Scheme.Modules.rigidify σ q L ≅ SheafOfModules.unit P.ringCatSheaf)) :
    Nonempty (L ≅ (Scheme.Modules.pullback q).obj ((Scheme.Modules.pullback σ).obj L)) := by

  obtain ⟨e⟩ := e
  obtain ⟨d⟩ := (hL.pullback σ).dual.2
  exact ⟨Scheme.Modules.isoOfTensorIsoUnit
    ((Scheme.Modules.pullback q).obj (Scheme.Modules.dual ((Scheme.Modules.pullback σ).obj L)))
    L ((Scheme.Modules.pullback q).obj ((Scheme.Modules.pullback σ).obj L))
    (β_ _ _ ≪≫ e)
    (β_ _ _ ≪≫ (Scheme.Modules.pullbackTensorObjIso q _ _).symm ≪≫ (Scheme.Modules.pullback q).mapIso d ≪≫
      Scheme.Modules.pullbackTensorUnitObjIso q)⟩
