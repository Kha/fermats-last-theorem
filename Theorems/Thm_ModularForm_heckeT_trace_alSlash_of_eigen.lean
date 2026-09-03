import Definitions.Def_ModularForm_AtkinLehnerDatum
import Definitions.Def_ModularForm_HeckeOperatorForms
import P2M.Util
import P2M.Sol.S_ModularForm_heckeT_trace_alSlash_of_eigen
set_option autoImplicit false

theorem ModularForm.heckeT_trace_alSlash_of_eigen (q : ℕ) {M : ℕ} [NeZero M]
    (A : ModularForm.AtkinLehnerDatum M q) (k : ℤ) {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M)
    (F : CuspForm (CongruenceSubgroup.Gamma0 M) k) (lam : ℂ) (hF : CuspForm.heckeTLin k hℓ hℓM F = lam • F) :
    ModularForm.heckeT k ℓ (ModularForm.alSlash A k ⇑F +
        (q : ℂ) ^ (2 - k) • ModularForm.heckeU k q (ModularForm.alSlash A k (ModularForm.alSlash A k ⇑F))) =
      lam • (ModularForm.alSlash A k ⇑F +
        (q : ℂ) ^ (2 - k) • ModularForm.heckeU k q (ModularForm.alSlash A k (ModularForm.alSlash A k ⇑F))) := by p2m_exact_reverting @_root_.P2MW.S_ModularForm_heckeT_trace_alSlash_of_eigen.solution
