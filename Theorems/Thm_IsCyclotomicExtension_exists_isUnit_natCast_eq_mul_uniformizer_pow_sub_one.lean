import Mathlib
import P2M.Util
import P2M.Sol.S_IsCyclotomicExtension_exists_isUnit_natCast_eq_mul_uniformizer_pow_sub_one

set_option autoImplicit false

theorem IsCyclotomicExtension.exists_isUnit_natCast_eq_mul_uniformizer_pow_sub_one
    (p : ℕ) [Fact p.Prime] (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p)
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ z : A, algebraMap A L z = ζ)
    (ϖ : A) (hϖ : IsLocalRing.maximalIdeal A = Ideal.span {ϖ}) :
    ∃ u : Aˣ, (p : A) = ↑u * ϖ ^ (p - 1) := by p2m_exact_reverting @_root_.P2MW.S_IsCyclotomicExtension_exists_isUnit_natCast_eq_mul_uniformizer_pow_sub_one.solution
