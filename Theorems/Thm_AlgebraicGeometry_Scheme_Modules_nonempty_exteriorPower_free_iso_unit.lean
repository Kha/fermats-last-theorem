import Mathlib
import Definitions.Def_AlgebraicGeometry_ModulesDet
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_nonempty_exteriorPower_free_iso_unit

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry
theorem AlgebraicGeometry.Scheme.Modules.nonempty_exteriorPower_free_iso_unit (X : Scheme.{u}) (n : ℕ) :
    Nonempty ((Scheme.Modules.exteriorPower X n).obj (SheafOfModules.free.{u} (ULift.{u} (Fin n))) ≅
      SheafOfModules.unit X.ringCatSheaf) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_nonempty_exteriorPower_free_iso_unit.solution
