import Mathlib
import Definitions.Def_CuspForm_HeckeOperatorFormsGammaH
import Definitions.Def_ModularForm_AtkinLehnerDatum
import P2M.Util
import P2M.Sol.S_CuspForm_alSlash_coe_heckeTLinH_eq_coe_heckeTLinH
attribute [-instance] CuspForm.instModuleTwoCuspForms CuspForm.instIsScalarTowerTwoCuspForms CuspForm.instAddCommGroupTwoCuspForms CuspForm.instIsScalarTowerSelfTwoCuspForms CuspForm.instModuleQuotientTwoCuspForms WeierstrassCurve.Affine.Point.instFinite
attribute [-simp] CuspForm.heckeGenH_T CuspForm.coe_twoCuspEnd_apply CuspForm.twoCuspEndMod_reduce CuspForm.heckeGenH_U CuspForm.heckeGenH_dia

set_option autoImplicit false

theorem CuspForm.alSlash_coe_heckeTLinH_eq_coe_heckeTLinH
    (M : ℕ) [NeZero M] (p : ℕ) [Fact p.Prime] (hpM : p ∣ M) (H : Subgroup (ZMod M)ˣ)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (W : ModularForm.AtkinLehnerDatum M p) (k : ℤ) {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M)
    (f X : CuspForm (CohCarrier.GammaH M H) k) (hX : ⇑X = ModularForm.alSlash W k ⇑f) :
    ModularForm.alSlash W k ⇑(CuspForm.heckeTLinH k hℓ hℓM f) = ⇑(CuspForm.heckeTLinH k hℓ hℓM X) := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_alSlash_coe_heckeTLinH_eq_coe_heckeTLinH.solution
