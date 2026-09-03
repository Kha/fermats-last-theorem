import Mathlib.Tactic
import Definitions.Def_ModularForm_EisensteinChiNegThree
import P2M.Util
namespace P2MW.S_EisensteinWeightOne_chiNegThree_mul

open EisensteinWeightOne

theorem solution (m n : ℕ) :
    chiNegThree (m * n) = chiNegThree m * chiNegThree n := by
  simp only [chiNegThree]
  rw [Nat.mul_mod]
  have hm : m % 3 = 0 ∨ m % 3 = 1 ∨ m % 3 = 2 := by omega
  have hn : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
  rcases hm with h | h | h <;> rcases hn with h' | h' | h' <;> rw [h, h'] <;> decide
