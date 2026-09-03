import Definitions.Def_CohCarrier_Level
import Theorems.Thm_CohCarrier_coresAdd_comp_subtype
import P2M.Util
namespace P2MW.S_CohCarrier_jDeg_comp_iDegP_self

set_option autoImplicit false

open CohCarrier

theorem jDiagPushCharRestrict {M M' d : ℕ} {H : Subgroup (ZMod M)ˣ} {H' : Subgroup (ZMod M')ˣ}
    {A : Type*} [AddCommGroup A] [NeZero d] (h : LevelLE M M' H H' d) (φ : H1 M H A) :
    pushChar M M' H H' d A h (iDeg' M M' H H' d A h φ)
      = φ.comp (Subgroup.subtype (iotaDeg M M' H H' d h).range).toAdditive := by
  ext x
  show φ (Additive.ofMul ((iotaDeg M M' H H' d h)
      (((iotaDeg M M' H H' d h).ofInjective (iotaDeg_injective M M' H H' d h)).symm
        (Additive.toMul x))))
    = φ (Additive.ofMul ((Subgroup.subtype (iotaDeg M M' H H' d h).range) (Additive.toMul x)))
  congr 2
  have hsymm := ((iotaDeg M M' H H' d h).ofInjective
    (iotaDeg_injective M M' H H' d h)).apply_symm_apply (Additive.toMul x)
  exact congrArg Subtype.val hsymm

theorem solution {M M' d : ℕ} {H : Subgroup (ZMod M)ˣ} {H' : Subgroup (ZMod M')ˣ}
    {A : Type*} [AddCommGroup A] [NeZero M'] [NeZero d]
    (h : LevelLE M M' H H' d) (φ : H1 M H A) :
    jDeg M M' H H' d A h (iDeg' M M' H H' d A h φ)
      = (iotaDeg M M' H H' d h).range.index • φ := by
  show coresAdd _ (pushChar M M' H H' d A h (iDeg' M M' H H' d A h φ)) = _
  rw [jDiagPushCharRestrict h φ, coresAdd_comp_subtype]

#print axioms solution
