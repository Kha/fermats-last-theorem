import Definitions.Def_ModularForm_AtkinLehnerDatum
import Definitions.Def_ModularForm_HeckeOperator
import P2M.Util
import P2M.Sol.S_CuspForm_exists_coe_eq_add_smul_heckeU_alSlash
set_option autoImplicit false

theorem CuspForm.exists_coe_eq_add_smul_heckeU_alSlash (q : ℕ) (hq : q.Prime) {M : ℕ} [NeZero M] (A : ModularForm.AtkinLehnerDatum M q)
    (k : ℤ) (F : CuspForm (CongruenceSubgroup.Gamma0 M) k) :
    ∃ G : CuspForm (CongruenceSubgroup.Gamma0 A.R) k,
      ⇑G = ⇑F + (q : ℂ) ^ (2 - k) • ModularForm.heckeU k q (ModularForm.alSlash A k ⇑F) := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_exists_coe_eq_add_smul_heckeU_alSlash.solution
