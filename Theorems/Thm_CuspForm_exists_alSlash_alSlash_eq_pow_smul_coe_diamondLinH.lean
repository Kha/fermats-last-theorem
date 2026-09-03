import Mathlib
import Definitions.Def_CuspForm_HeckeOperatorFormsGammaH
import Definitions.Def_ModularForm_AtkinLehnerDatum
import P2M.Util
import P2M.Sol.S_CuspForm_exists_alSlash_alSlash_eq_pow_smul_coe_diamondLinH

set_option autoImplicit false

open scoped MatrixGroups ModularForm

theorem CuspForm.exists_alSlash_alSlash_eq_pow_smul_coe_diamondLinH
    (M : ℕ) [NeZero M] (p : ℕ) [Fact p.Prime] (hpM : p ∣ M) (H : Subgroup (ZMod M)ˣ)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (W W' : ModularForm.AtkinLehnerDatum M p) (k : ℤ) (f : CuspForm (CohCarrier.GammaH M H) k) :
    ∃ δ : (ZMod M)ˣ, ModularForm.alSlash W k (ModularForm.alSlash W' k ⇑f) =
      ((p : ℂ) ^ (k - 2)) • (⇑(CuspForm.diamondLinH k δ f) : UpperHalfPlane → ℂ) := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_exists_alSlash_alSlash_eq_pow_smul_coe_diamondLinH.solution
