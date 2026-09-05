module

public import Mathlib
public import Definitions.Def_ModularCurve_SpecializeModuli
public import Definitions.Def_AlgebraicCurve_RatFuncPlaceInfty
public import Theorems.Thm_AlgebraicCurve_RationalFunctionField_eq_placeInfty_of_ord_X_neg
import P2M.Util

@[expose] public section
namespace P2MW.S_ModularCurve_eq_charLGeomPlaceEquiv_placeInfty_of_ord_neg

p2m_open "AlgebraicCurve ModularCurve P2MW.S_ModularCurve_eq_charLGeomPlaceEquiv_placeInfty_of_ord_neg.ModularCurve"

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "ratFuncEquivCharLOneC charLGeomPlaceEquiv jqModC modularFunctionFieldC jqModC_mem transcendental_jqModC"
p2m_open "ModularCurve"

variable (k : Type*) [Field k]

private theorem ratFuncEquivCharLOneC_X :
    ratFuncEquivCharLOneC k RatFunc.X = ⟨jqModC k, jqModC_mem k 1⟩ := by
  apply Subtype.ext
  simp only [ratFuncEquivCharLOneC, AlgEquiv.trans_apply]
  exact RatFunc.algEquivOfTranscendental_X (f := jqModC k) (h := transcendental_jqModC k)

private theorem ord_charLGeomPlaceEquiv (v₀ : Place k (RatFunc k)) (f : RatFunc k) :
    (charLGeomPlaceEquiv k v₀).ord (ratFuncEquivCharLOneC k f) = v₀.ord f :=
  Place.ord_congrRingEquiv (ratFuncEquivCharLOneC k).toRingEquiv
    (fun a => (ratFuncEquivCharLOneC k).commutes a) v₀ f

end ModularCurve

end

theorem solution
    {k : Type*} [Field k] [DecidableEq (RatFunc k)] {v : Place k ↥(modularFunctionFieldC k 1)}
    (h : v.ord ((⟨jqModC k, jqModC_mem k 1⟩ : modularFunctionFieldC k 1)) < 0) :
    v = charLGeomPlaceEquiv k (RationalFunctionField.placeInfty k) := by
  obtain ⟨v₀, rfl⟩ := (charLGeomPlaceEquiv k).surjective v
  rw [← ModularCurve.ratFuncEquivCharLOneC_X, ModularCurve.ord_charLGeomPlaceEquiv] at h
  rw [RationalFunctionField.eq_placeInfty_of_ord_X_neg v₀ h]
