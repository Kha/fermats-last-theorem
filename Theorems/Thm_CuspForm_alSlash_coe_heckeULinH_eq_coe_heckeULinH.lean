import Mathlib
import Definitions.Def_CuspForm_HeckeOperatorFormsGammaH
import Definitions.Def_ModularForm_AtkinLehnerDatum
import P2M.Util
import P2M.Sol.S_CuspForm_alSlash_coe_heckeULinH_eq_coe_heckeULinH
attribute [-instance] WeierstrassCurve.Affine.Point.instFinite

set_option autoImplicit false

open scoped MatrixGroups ModularForm

theorem CuspForm.alSlash_coe_heckeULinH_eq_coe_heckeULinH
    (M : ℕ) [NeZero M] (p : ℕ) [Fact p.Prime] (hpM : p ∣ M) (H : Subgroup (ZMod M)ˣ)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (W : ModularForm.AtkinLehnerDatum M p) (k : ℤ) {q : ℕ} (hq : q.Prime) (hqM : q ∣ M) (hqp : q ≠ p)
    (f X : CuspForm (CohCarrier.GammaH M H) k) (hX : ⇑X = ModularForm.alSlash W k ⇑f) :
    ModularForm.alSlash W k ⇑(CuspForm.heckeULinH k q f) = ⇑(CuspForm.heckeULinH k q X) := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_alSlash_coe_heckeULinH_eq_coe_heckeULinH.solution
