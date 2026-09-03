import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Complex.Basic
import Definitions.Def_ModularForm_HeckeOperator
import P2M.Util
import P2M.Sol.S_ModularForm_coeffHecke_eigenvalue_eq_apply_of_apply_one_eq_one

theorem ModularForm.coeffHecke_eigenvalue_eq_apply_of_apply_one_eq_one (k : ℤ) (N : ℕ) (a c : ℕ → ℂ)
    (hT : ∀ p : ℕ, p.Prime → ¬ p ∣ N → ∀ n : ℕ, ModularForm.coeffHeckeT k p a n = c p * a n)
    (hU : ∀ p : ℕ, p.Prime → p ∣ N → ∀ n : ℕ, ModularForm.coeffHeckeU p a n = c p * a n)
    (h1 : a 1 = 1) : ∀ p : ℕ, p.Prime → c p = a p := by p2m_exact_reverting @_root_.P2MW.S_ModularForm_coeffHecke_eigenvalue_eq_apply_of_apply_one_eq_one.solution
