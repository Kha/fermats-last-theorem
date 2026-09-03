import Definitions.Def_CuspForm_HeckeAlgebra
import Definitions.Def_CuspForm_IntegralStructure
import P2M.Util
import P2M.Sol.S_CuspForm_HasIntegralStructure_exists_ne_zero_forall_apply_eq_smul

theorem CuspForm.HasIntegralStructure.exists_ne_zero_forall_apply_eq_smul {N : ℕ} [NeZero N] {k : ℤ} (hN : CuspForm.HasIntegralStructure N k) (hk : 1 ≤ k) {S : Set ℕ} (χ : CuspForm.heckeAlgebra N k S →+* ℂ) : ∃ f : CuspForm (CongruenceSubgroup.Gamma0 N) k, f ≠ 0 ∧ ∀ t : CuspForm.heckeAlgebra N k S, (t : Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) k)) f = χ t • f := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_HasIntegralStructure_exists_ne_zero_forall_apply_eq_smul.solution
