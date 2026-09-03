import Mathlib
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_nonempty_pullback_obj_unit_iso_unit

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

universe u

namespace H2a2B1

theorem final_opensMap {X Y : Scheme.{u}} (f : X ⟶ Y) : (TopologicalSpace.Opens.map f.base).Final :=
  Functor.final_of_exists_of_isFiltered _ (fun U => ⟨⊤, ⟨homOfLE le_top⟩⟩)
    (fun {U} {V} s s' => ⟨V, 𝟙 V, by rw [Subsingleton.elim s s']⟩)

theorem main {X Y : Scheme.{u}} (g : X ⟶ Y) :
    Nonempty ((Scheme.Modules.pullback g).obj (SheafOfModules.unit Y.ringCatSheaf) ≅ SheafOfModules.unit X.ringCatSheaf) := by
  haveI := final_opensMap g
  have hiso : IsIso (SheafOfModules.pullbackObjUnitToUnit g.toRingCatSheafHom) := inferInstance
  exact ⟨@asIso _ _ _ _ (SheafOfModules.pullbackObjUnitToUnit g.toRingCatSheafHom) hiso⟩

end H2a2B1

theorem solution
    {X Y : Scheme.{u}} (g : X ⟶ Y) :
    Nonempty ((Scheme.Modules.pullback g).obj (SheafOfModules.unit Y.ringCatSheaf) ≅ SheafOfModules.unit X.ringCatSheaf) :=
  H2a2B1.main g
