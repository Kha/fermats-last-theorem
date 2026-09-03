import Definitions.Def_FLTPrelim_Modularity
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_apOfModel_ne_succ_and_ne_neg_succ

set_option autoImplicit false
theorem WeierstrassCurve.apOfModel_ne_succ_and_ne_neg_succ (W : WeierstrassCurve ℤ) {q : ℕ} (hq : q.Prime) :
    W.apOfModel q ≠ (q : ℤ) + 1 ∧ W.apOfModel q ≠ -((q : ℤ) + 1) := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_apOfModel_ne_succ_and_ne_neg_succ.solution
