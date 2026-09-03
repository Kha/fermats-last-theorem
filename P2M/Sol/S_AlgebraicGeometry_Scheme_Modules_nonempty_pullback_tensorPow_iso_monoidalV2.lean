import Mathlib
import Definitions.Def_SheafOfModules_MonoidalV2
import Definitions.Def_AlgebraicGeometry_ModulesTensorPowV2
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidalV2
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_nonempty_pullback_tensorPow_iso_monoidalV2

set_option autoImplicit false

universe u

p2m_open "CategoryTheory AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_Modules_nonempty_pullback_tensorPow_iso_monoidalV2.AlgebraicGeometry CategoryTheory.MonoidalCategory"

namespace AlgebraicGeometry p2m_export "AlgebraicGeometry" "Scheme.Modules.pullback Scheme Scheme.Modules Scheme.Modules.pullbackTensorObjIso Scheme.Modules.pullbackTensorUnitObjIso" namespace Scheme p2m_export "AlgebraicGeometry.Scheme" "Modules.pullback Modules Modules.pullbackTensorObjIso Modules.pullbackTensorUnitObjIso" namespace Modules p2m_export "AlgebraicGeometry.Scheme.Modules" "pullback tensorPow pullbackTensorObjIso pullbackTensorUnitObjIso" end AlgebraicGeometry.Scheme.Modules
p2m_open_scoped "AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Modules" in

noncomputable def AlgebraicGeometry.Scheme.Modules.pullbackTensorPowIsoV2
    {X Y : Scheme.{u}} (f : X ⟶ Y) (L : Y.Modules) :
    ∀ n : ℕ, (Scheme.Modules.pullback f).obj (L.tensorPow n) ≅ ((Scheme.Modules.pullback f).obj L).tensorPow n
  | 0 => Scheme.Modules.pullbackTensorUnitObjIso f
  | n + 1 => Scheme.Modules.pullbackTensorObjIso f (L.tensorPow n) L ≪≫
      whiskerRightIso (AlgebraicGeometry.Scheme.Modules.pullbackTensorPowIsoV2 f L n) _

theorem solution
    {X Y : Scheme.{u}} (f : X ⟶ Y) (L : Y.Modules) (n : ℕ) :
    Nonempty ((Scheme.Modules.pullback f).obj (L.tensorPow n) ≅ ((Scheme.Modules.pullback f).obj L).tensorPow n) := by
  exact ⟨AlgebraicGeometry.Scheme.Modules.pullbackTensorPowIsoV2 f L n⟩
