import Definitions.Def_NumberTheory_DedekindSum
import P2M.Util
import P2M.Sol.S_rademacher_phi_step

theorem rademacher_phi_step (c r : ℕ) (hc : 0 < c) (hr : 0 < r) (a b d q : ℤ) (hrd : (r : ℤ) = q * c - d) (hdet : a * d - b * c = 1) : ((a + d : ℤ) : ℚ) / c - 12 * dedekindSum d c = ((q * a - b + c : ℤ) : ℚ) / r - 12 * dedekindSum c r + q - 3 := by p2m_exact_reverting @_root_.P2MW.S_rademacher_phi_step.solution
