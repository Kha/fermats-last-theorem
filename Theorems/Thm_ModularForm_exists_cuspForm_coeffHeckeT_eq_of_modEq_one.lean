import Definitions.Def_ModularForm_HeckeOperator
import Definitions.Def_FLTPrelim_Modularity
import P2M.Util
import P2M.Sol.S_ModularForm_exists_cuspForm_coeffHeckeT_eq_of_modEq_one
attribute [-simp] ModularForm.coe_heckeTLin_apply CuspForm.coe_heckeULin_apply CuspForm.coe_heckeTLin_apply ModularForm.coe_heckeULin_apply
set_option autoImplicit false

theorem ModularForm.exists_cuspForm_coeffHeckeT_eq_of_modEq_one
    (N' : ℕ) [NeZero N'] (k : ℤ) (f : ModularForm (CongruenceSubgroup.Gamma0 N') k)
    (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓ1 : ℓ ≡ 1 [MOD N']) :
    ∃ g : CuspForm (CongruenceSubgroup.Gamma0 N') k, ∀ n : ℕ,
      ModularForm.coeffHeckeT k ℓ (ModularFormClass.qCoeff f) n =
        (1 + (ℓ : ℂ) ^ (k - 1)) * ModularFormClass.qCoeff f n + ModularFormClass.qCoeff g n := by p2m_exact_reverting @_root_.P2MW.S_ModularForm_exists_cuspForm_coeffHeckeT_eq_of_modEq_one.solution
