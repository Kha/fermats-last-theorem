import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_nonempty_pullback_preimage_iso_unit_of_pullback_iso_unit

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

set_option maxHeartbeats 3200000 in
theorem solution
    {X Y : Scheme.{u}} (g : Y ⟶ X) {L : X.Modules} {U : X.Opens}
    (e : (Scheme.Modules.pullback U.ι).obj L ≅ SheafOfModules.unit U.toScheme.ringCatSheaf) :
    Nonempty ((Scheme.Modules.pullback (g ⁻¹ᵁ U).ι).obj ((Scheme.Modules.pullback g).obj L) ≅
      SheafOfModules.unit (g ⁻¹ᵁ U).toScheme.ringCatSheaf) := by
  have hfact : (g ⁻¹ᵁ U).ι ≫ g = (g ∣_ U) ≫ U.ι := (morphismRestrict_ι g U).symm
  exact ⟨(Scheme.Modules.pullbackComp _ _).app L ≪≫
    (Scheme.Modules.pullbackCongr hfact).app L ≪≫
    ((Scheme.Modules.pullbackComp _ _).app L).symm ≪≫
    (Scheme.Modules.pullback (g ∣_ U)).mapIso e ≪≫
    Scheme.Modules.pullbackUnitIso (g ∣_ U)⟩
