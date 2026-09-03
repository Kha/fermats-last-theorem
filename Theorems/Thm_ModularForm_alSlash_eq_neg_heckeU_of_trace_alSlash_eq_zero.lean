import Definitions.Def_ModularForm_AtkinLehnerDatum
import Definitions.Def_ModularForm_HeckeOperator
import P2M.Util
import P2M.Sol.S_ModularForm_alSlash_eq_neg_heckeU_of_trace_alSlash_eq_zero
set_option autoImplicit false

theorem ModularForm.alSlash_eq_neg_heckeU_of_trace_alSlash_eq_zero (q : ℕ) {M : ℕ} [NeZero M]
    (A : ModularForm.AtkinLehnerDatum M q) (k : ℤ) (F : CuspForm (CongruenceSubgroup.Gamma0 M) k)
    (hTrW : ModularForm.alSlash A k ⇑F +
      (q : ℂ) ^ (2 - k) • ModularForm.heckeU k q (ModularForm.alSlash A k (ModularForm.alSlash A k ⇑F)) = 0) :
    ModularForm.alSlash A k ⇑F = - ModularForm.heckeU k q ⇑F := by p2m_exact_reverting @_root_.P2MW.S_ModularForm_alSlash_eq_neg_heckeU_of_trace_alSlash_eq_zero.solution
