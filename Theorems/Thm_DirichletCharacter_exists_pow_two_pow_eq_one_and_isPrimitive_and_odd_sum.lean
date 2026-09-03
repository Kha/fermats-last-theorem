import Mathlib
import P2M.Util
import P2M.Sol.S_DirichletCharacter_exists_pow_two_pow_eq_one_and_isPrimitive_and_odd_sum

set_option autoImplicit false

theorem DirichletCharacter.exists_pow_two_pow_eq_one_and_isPrimitive_and_odd_sum
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : ℓ ≠ 2) :
    ∃ (n : ℕ) (χ : DirichletCharacter ℂ ℓ), 0 < n ∧
      (∀ j : ℕ, (χ ^ (2 * j + 1)).IsPrimitive ∧ (χ ^ (2 * j + 1)).Odd) ∧
      (∀ d : ZMod ℓ, χ d ^ (2 * n) = 1 ∨ χ d = 0) ∧
      _root_.Odd (∑ a ∈ Finset.range ℓ,
        (a : ℤ) * (if χ (a : ZMod ℓ) = 1 then 1 else if χ (a : ZMod ℓ) = -1 then -1 else 0)) := by p2m_exact_reverting @_root_.P2MW.S_DirichletCharacter_exists_pow_two_pow_eq_one_and_isPrimitive_and_odd_sum.solution
