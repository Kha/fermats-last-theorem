import Mathlib
import P2M.Util
import P2M.Sol.S_Algebra_le_of_etale_of_forall_exists_pow_expChar_pow_sub_isNilpotent

set_option autoImplicit false

universe u v

theorem Algebra.le_of_etale_of_forall_exists_pow_expChar_pow_sub_isNilpotent
    (K : Type u) [Field K] (C : Type v) [CommRing C] [Algebra K C]
    (D : Subalgebra K C) (hD : Algebra.Etale K D)
    (hrad : ∀ x : C, ∃ (n : ℕ) (y : C), y ∈ D ∧ IsNilpotent (x ^ ringExpChar K ^ n - y))
    (S : Subalgebra K C) (hS : Algebra.Etale K S) : S ≤ D := by p2m_exact_reverting @_root_.P2MW.S_Algebra_le_of_etale_of_forall_exists_pow_expChar_pow_sub_isNilpotent.solution
