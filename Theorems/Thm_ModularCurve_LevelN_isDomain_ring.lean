import Mathlib
import Definitions.Def_ModularCurve_LevelNFunctionField
import P2M.Util
import P2M.Sol.S_ModularCurve_LevelN_isDomain_ring

set_option autoImplicit false

theorem ModularCurve.LevelN.isDomain_ring (M : ℕ) [NeZero M] : IsDomain (ModularCurve.LevelN.ring M) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_LevelN_isDomain_ring.solution
