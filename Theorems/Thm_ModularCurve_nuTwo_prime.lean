import Definitions.Def_ModularCurve_GenusNumerics
import P2M.Util
import P2M.Sol.S_ModularCurve_nuTwo_prime

open ModularCurve
theorem ModularCurve.nuTwo_prime {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : nuTwo p = if p % 4 = 1 then 2 else 0 := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_nuTwo_prime.solution
