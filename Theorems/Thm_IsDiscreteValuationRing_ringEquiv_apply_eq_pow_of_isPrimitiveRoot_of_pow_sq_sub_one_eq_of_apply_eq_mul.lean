import Mathlib
import P2M.Util
import P2M.Sol.S_IsDiscreteValuationRing_ringEquiv_apply_eq_pow_of_isPrimitiveRoot_of_pow_sq_sub_one_eq_of_apply_eq_mul

set_option autoImplicit false

open IsLocalRing

theorem IsDiscreteValuationRing.ringEquiv_apply_eq_pow_of_isPrimitiveRoot_of_pow_sq_sub_one_eq_of_apply_eq_mul
    {A : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (q : ℕ) [Fact q.Prime] (hAq : (q : A) ∈ IsLocalRing.maximalIdeal A)
    (ζ : A) (hζ : IsPrimitiveRoot ζ q)
    (π : A) (hπ : π ^ (q ^ 2 - 1) = (q : A))
    (σ : A ≃+* A) (hσ : ∀ a : A, σ a - a ∈ IsLocalRing.maximalIdeal A)
    (α : A) (hσπ : σ π = α * π)
    (d : ℕ) (hd : α ^ (q + 1) - (d : A) ∈ IsLocalRing.maximalIdeal A) :
    σ ζ = ζ ^ d := by p2m_exact_reverting @_root_.P2MW.S_IsDiscreteValuationRing_ringEquiv_apply_eq_pow_of_isPrimitiveRoot_of_pow_sq_sub_one_eq_of_apply_eq_mul.solution
