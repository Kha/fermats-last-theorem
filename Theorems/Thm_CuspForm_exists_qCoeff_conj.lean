import Mathlib
import Definitions.Def_FLTPrelim_Modularity
import P2M.Util
import P2M.Sol.S_CuspForm_exists_qCoeff_conj

theorem CuspForm.exists_qCoeff_conj (N : ℕ) [NeZero N] (k : ℤ) :
    ∃ ρ : CuspForm (CongruenceSubgroup.Gamma0 N) k → CuspForm (CongruenceSubgroup.Gamma0 N) k,
      ∀ (f : CuspForm (CongruenceSubgroup.Gamma0 N) k) (n : ℕ),
        ModularFormClass.qCoeff (ρ f) n = (starRingEnd ℂ) (ModularFormClass.qCoeff f n) := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_exists_qCoeff_conj.solution
