import Mathlib
import Definitions.Def_ModularForm_AtkinLehnerDatum
import P2M.Util
import P2M.Sol.S_CuspForm_exists_gamma1_coe_eq_alSlash

set_option autoImplicit false

open scoped MatrixGroups

theorem CuspForm.exists_gamma1_coe_eq_alSlash
    (M q : ℕ) [NeZero M] (W : ModularForm.AtkinLehnerDatum M q) {k : ℤ}
    (f : CuspForm (CongruenceSubgroup.Gamma1 M) k) :
    ∃ g : CuspForm (CongruenceSubgroup.Gamma1 M) k, (⇑g : UpperHalfPlane → ℂ) = ModularForm.alSlash W k ⇑f := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_exists_gamma1_coe_eq_alSlash.solution
