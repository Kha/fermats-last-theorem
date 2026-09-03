import Definitions.Def_NumberTheory_DedekindSum
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import P2M.Util
import P2M.Sol.S_dedekindSum_jacobiSym_mod_eight

theorem dedekindSum_jacobiSym_mod_eight (h k : ℕ) (hk : Odd k) (hhk : Nat.Coprime h k) : ∃ t : ℤ, 12 * (k : ℚ) * dedekindSum h k = (k : ℚ) + 1 - 2 * ((jacobiSym h k : ℤ) : ℚ) + 8 * t := by p2m_exact_reverting @_root_.P2MW.S_dedekindSum_jacobiSym_mod_eight.solution
