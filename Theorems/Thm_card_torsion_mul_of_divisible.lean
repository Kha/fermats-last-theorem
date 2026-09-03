import Mathlib
import P2M.Util
import P2M.Sol.S_card_torsion_mul_of_divisible

open Function
theorem card_torsion_mul_of_divisible
    {A : Type*} [AddCommGroup A]
    (hdiv : ∀ m : ℕ, m ≠ 0 → ∀ x : A, ∃ y : A, m • y = x)
    (a b : ℕ) (ha : a ≠ 0)
    (hfa : Finite {x : A // a • x = 0}) (hfb : Finite {x : A // b • x = 0}) :
    Finite {x : A // (a * b) • x = 0} ∧
      Nat.card {x : A // (a * b) • x = 0} =
        Nat.card {x : A // a • x = 0} * Nat.card {x : A // b • x = 0} := by p2m_exact_reverting @_root_.P2MW.S_card_torsion_mul_of_divisible.solution
