import Mathlib.Data.ZMod.Basic
import P2M.Util
import P2M.Sol.S_FrobeniusEndo_exists_prime_gt_and_quadratic_root

theorem FrobeniusEndo.exists_prime_gt_and_quadratic_root (a q : ℤ) (hq : 1 ≤ q) (N : ℕ) : ∃ r : ℕ, N < r ∧ r.Prime ∧ ∃ c : ZMod r, c ^ 2 - (a : ZMod r) * c + (q : ZMod r) = 0 := by p2m_exact_reverting @_root_.P2MW.S_FrobeniusEndo_exists_prime_gt_and_quadratic_root.solution
