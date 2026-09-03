import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_nonempty_pullback_obj_unit_iso_unit

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.Scheme.Modules.nonempty_pullback_obj_unit_iso_unit
    {X Y : Scheme.{u}} (g : X ⟶ Y) :
    Nonempty ((Scheme.Modules.pullback g).obj (SheafOfModules.unit Y.ringCatSheaf) ≅ SheafOfModules.unit X.ringCatSheaf) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_nonempty_pullback_obj_unit_iso_unit.solution
