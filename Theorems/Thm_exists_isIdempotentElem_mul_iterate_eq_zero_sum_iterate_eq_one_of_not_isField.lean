import Mathlib
import P2M.Util
import P2M.Sol.S_exists_isIdempotentElem_mul_iterate_eq_zero_sum_iterate_eq_one_of_not_isField

set_option autoImplicit false

theorem exists_isIdempotentElem_mul_iterate_eq_zero_sum_iterate_eq_one_of_not_isField
    (F A : Type) [Field F] [CommRing A] [Algebra F A] [Module.Finite F A] [IsReduced A]
    (s : A →+* A) (n : ℕ) (hn : n.Prime) (hsn : (⇑s)^[n] = id)
    (hfix : ∀ a : A, s a = a → a ∈ Set.range (algebraMap F A))
    (hA : ¬ IsField A) :
    ∃ e : A, IsIdempotentElem e ∧ (∀ i, 0 < i → i < n → e * (⇑s)^[i] e = 0) ∧
      (∑ i ∈ Finset.range n, (⇑s)^[i] e) = 1 := by p2m_exact_reverting @_root_.P2MW.S_exists_isIdempotentElem_mul_iterate_eq_zero_sum_iterate_eq_one_of_not_isField.solution
