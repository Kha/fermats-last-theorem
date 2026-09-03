import Mathlib
import P2M.Util
import P2M.Sol.S_Algebra_exists_subalgebra_etale_forall_le_forall_exists_pow_expChar_pow_sub_isNilpotent

set_option autoImplicit false

universe u v

theorem Algebra.exists_subalgebra_etale_forall_le_forall_exists_pow_expChar_pow_sub_isNilpotent
    (k : Type u) [Field k] (A : Type v) [CommRing A] [Algebra k A] [Module.Finite k A] :
    ∃ P : Subalgebra k A,
      Algebra.Etale k P ∧
      (∀ S : Subalgebra k A, Algebra.Etale k S → S ≤ P) ∧
      (∀ x : A, ∃ (n : ℕ) (y : A), y ∈ P ∧ IsNilpotent (x ^ ringExpChar k ^ n - y)) := by p2m_exact_reverting @_root_.P2MW.S_Algebra_exists_subalgebra_etale_forall_le_forall_exists_pow_expChar_pow_sub_isNilpotent.solution
