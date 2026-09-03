import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_nonempty_pullback_preimage_iso_unit_of_pullback_iso_unit

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.nonempty_pullback_preimage_iso_unit_of_pullback_iso_unit
    {X Y : Scheme.{u}} (g : Y ⟶ X) {L : X.Modules} {U : X.Opens}
    (e : (Scheme.Modules.pullback U.ι).obj L ≅ SheafOfModules.unit U.toScheme.ringCatSheaf) :
    Nonempty ((Scheme.Modules.pullback (g ⁻¹ᵁ U).ι).obj ((Scheme.Modules.pullback g).obj L) ≅
      SheafOfModules.unit (g ⁻¹ᵁ U).toScheme.ringCatSheaf) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_nonempty_pullback_preimage_iso_unit_of_pullback_iso_unit.solution
