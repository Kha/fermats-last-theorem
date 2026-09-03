import Mathlib
import P2M.Util
import P2M.Sol.S_exists_idempotent_mul_eq_and_pow_mul_sub_mem_of_moduleFinite_padicInt

set_option autoImplicit false

open scoped Padic

universe u

theorem exists_idempotent_mul_eq_and_pow_mul_sub_mem_of_moduleFinite_padicInt
    (p : ℕ) [Fact p.Prime] (A : Type u) [CommRing A] [Algebra ℤ_[p] A] [Module.Finite ℤ_[p] A] (a : A) :
    ∃ e : A, IsIdempotentElem e ∧ e ∈ Algebra.adjoin ℤ_[p] ({a} : Set A) ∧
      (∃ b ∈ Algebra.adjoin ℤ_[p] ({a} : Set A), a * b = e) ∧
      ∃ N : ℕ, a ^ N * (1 - e) ∈ Ideal.span {(p : A)} := by p2m_exact_reverting @_root_.P2MW.S_exists_idempotent_mul_eq_and_pow_mul_sub_mem_of_moduleFinite_padicInt.solution
