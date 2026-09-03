import Definitions.Def_ModularCurve_GenusNumerics
import P2M.Util
import P2M.Sol.S_ModularCurve_cuspCount_prime

open ModularCurve
theorem ModularCurve.cuspCount_prime {p : ℕ} (hp : p.Prime) : cuspCount p = 2 := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_cuspCount_prime.solution
