import Definitions.Def_NumberTheory_DedekindSum
import Mathlib.Data.Int.ModEq
import P2M.Util
import P2M.Sol.S_dedekindSum_of_mul_modEq_one

theorem dedekindSum_of_mul_modEq_one (h h' k : ℕ) (hinv : Nat.ModEq k (h * h') 1) : dedekindSum h' k = dedekindSum h k := by p2m_exact_reverting @_root_.P2MW.S_dedekindSum_of_mul_modEq_one.solution
