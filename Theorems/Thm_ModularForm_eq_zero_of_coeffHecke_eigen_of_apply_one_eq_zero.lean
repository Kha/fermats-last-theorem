import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Complex.Basic
import Definitions.Def_ModularForm_HeckeOperator
import P2M.Util
import P2M.Sol.S_ModularForm_eq_zero_of_coeffHecke_eigen_of_apply_one_eq_zero

theorem ModularForm.eq_zero_of_coeffHecke_eigen_of_apply_one_eq_zero (k : ℤ) (N : ℕ) (a c : ℕ → ℂ)
    (hT : ∀ p : ℕ, p.Prime → ¬ p ∣ N → ∀ n : ℕ, ModularForm.coeffHeckeT k p a n = c p * a n)
    (hU : ∀ p : ℕ, p.Prime → p ∣ N → ∀ n : ℕ, ModularForm.coeffHeckeU p a n = c p * a n)
    (h1 : a 1 = 0) : ∀ n : ℕ, n ≠ 0 → a n = 0 := by p2m_exact_reverting @_root_.P2MW.S_ModularForm_eq_zero_of_coeffHecke_eigen_of_apply_one_eq_zero.solution
