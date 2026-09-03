import Definitions.Def_ModularCurve_GenusNumerics
import P2M.Util
import P2M.Sol.S_ModularCurve_nuThree_prime

open ModularCurve
theorem ModularCurve.nuThree_prime {p : ℕ} (hp : p.Prime) (hp3 : p ≠ 3) : nuThree p = if p % 3 = 1 then 2 else 0 := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_nuThree_prime.solution
