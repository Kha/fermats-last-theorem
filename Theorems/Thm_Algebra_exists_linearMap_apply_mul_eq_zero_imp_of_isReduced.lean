import Mathlib
import P2M.Util
import P2M.Sol.S_Algebra_exists_linearMap_apply_mul_eq_zero_imp_of_isReduced

theorem Algebra.exists_linearMap_apply_mul_eq_zero_imp_of_isReduced
    (K A : Type*) [Field K] [CommRing A] [Algebra K A] [FiniteDimensional K A] [IsReduced A] :
    ∃ l : A →ₗ[K] K, ∀ x : A, (∀ y : A, l (x * y) = 0) → x = 0 := by p2m_exact_reverting @_root_.P2MW.S_Algebra_exists_linearMap_apply_mul_eq_zero_imp_of_isReduced.solution
