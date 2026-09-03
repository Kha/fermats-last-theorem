import Mathlib
import P2M.Util
import P2M.Sol.S_IsPrimitiveRoot_exists_isPrimitiveRoot_mul_pow_eq_and_mem_and_ringHom_apply_eq_exp_of_henselian

set_option autoImplicit false

theorem IsPrimitiveRoot.exists_isPrimitiveRoot_mul_pow_eq_and_mem_and_ringHom_apply_eq_exp_of_henselian
    (q ℓ : ℕ) [Fact q.Prime] [Fact ℓ.Prime] (hℓq : ℓ ≠ q)
    (L : Type) [Field L] [CharZero L]
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    [HenselianLocalRing A] [IsAlgClosed (IsLocalRing.ResidueField A)]
    (hAq : (q : A) ∈ IsLocalRing.maximalIdeal A)
    (ζ : L) (hζ : IsPrimitiveRoot ζ q) (hζA : ∃ x : A, algebraMap A L x = ζ)
    (hι : ∃ ι : L →+* ℂ, ι ζ = Complex.exp (2 * Real.pi * Complex.I / q)) :
    ∃ ξ : L, IsPrimitiveRoot ξ (q * ℓ) ∧ ξ ^ ℓ = ζ ∧ (∃ x : A, algebraMap A L x = ξ) ∧
      ∃ ι : L →+* ℂ, ι ξ = Complex.exp (2 * Real.pi * Complex.I / (q * ℓ)) := by p2m_exact_reverting @_root_.P2MW.S_IsPrimitiveRoot_exists_isPrimitiveRoot_mul_pow_eq_and_mem_and_ringHom_apply_eq_exp_of_henselian.solution
