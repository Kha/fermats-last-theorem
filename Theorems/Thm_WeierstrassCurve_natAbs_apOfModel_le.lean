import Definitions.Def_FLTPrelim_Modularity
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_natAbs_apOfModel_le

set_option autoImplicit false

theorem WeierstrassCurve.natAbs_apOfModel_le
    (W : WeierstrassCurve ℤ) (p : ℕ) [Fact p.Prime] :
    (W.apOfModel p).natAbs ≤ p := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_natAbs_apOfModel_le.solution
