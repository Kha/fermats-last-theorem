import Mathlib
import Definitions.Def_FLTPrelim_Modularity
import P2M.Util
import P2M.Sol.S_CuspForm_exists_gamma1_apply_eq_conj_and_qCoeff_eq_conj

set_option autoImplicit false

open CongruenceSubgroup
open scoped MatrixGroups

theorem CuspForm.exists_gamma1_apply_eq_conj_and_qCoeff_eq_conj
    (M : ℕ) (k : ℤ) (g : CuspForm (Gamma1 M) k) :
    ∃ g' : CuspForm (Gamma1 M) k,
      (∀ τ τ' : UpperHalfPlane, (τ' : ℂ) = -(starRingEnd ℂ (τ : ℂ)) →
        g' τ = starRingEnd ℂ (g τ')) ∧
      ∀ n : ℕ, ModularFormClass.qCoeff g' n = starRingEnd ℂ (ModularFormClass.qCoeff g n) := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_exists_gamma1_apply_eq_conj_and_qCoeff_eq_conj.solution
