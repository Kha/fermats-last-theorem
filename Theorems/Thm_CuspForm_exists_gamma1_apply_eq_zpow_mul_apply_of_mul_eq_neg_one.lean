import Mathlib
import Definitions.Def_FLTPrelim_Modularity
import P2M.Util
import P2M.Sol.S_CuspForm_exists_gamma1_apply_eq_zpow_mul_apply_of_mul_eq_neg_one

set_option autoImplicit false

open CongruenceSubgroup
open scoped MatrixGroups

theorem CuspForm.exists_gamma1_apply_eq_zpow_mul_apply_of_mul_eq_neg_one
    (M : ℕ) [NeZero M] (k : ℤ) (g : CuspForm (Gamma1 M) k) :
    ∃ h : CuspForm (Gamma1 M) k,
      ∀ τ τ' : UpperHalfPlane, (τ' : ℂ) * ((M : ℂ) * (τ : ℂ)) = -1 →
        g τ' = (τ : ℂ) ^ k * h τ := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_exists_gamma1_apply_eq_zpow_mul_apply_of_mul_eq_neg_one.solution
