import Mathlib
import P2M.Util
import P2M.Sol.S_IsPrimitiveRoot_exists_isUnit_one_sub_eq_mul_of_pow_sub_one_eq_mul

set_option autoImplicit false

open IsLocalRing

theorem IsPrimitiveRoot.exists_isUnit_one_sub_eq_mul_of_pow_sub_one_eq_mul
    (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (q : ℕ) [Fact q.Prime] (ζ : A) (hζ : IsPrimitiveRoot ζ q)
    (ϖ : A) (hϖ : maximalIdeal A = Ideal.span {ϖ}) (ε : A) (hε : IsUnit ε)
    (hϖq : ϖ ^ (q - 1) = ε * (q : A)) :
    ∃ u : A, IsUnit u ∧ 1 - ζ = u * ϖ := by p2m_exact_reverting @_root_.P2MW.S_IsPrimitiveRoot_exists_isUnit_one_sub_eq_mul_of_pow_sub_one_eq_mul.solution
