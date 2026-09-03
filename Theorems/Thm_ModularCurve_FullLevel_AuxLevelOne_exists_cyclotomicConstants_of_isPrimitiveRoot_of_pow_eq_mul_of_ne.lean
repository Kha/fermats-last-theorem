import Mathlib
import P2M.Util
import P2M.Sol.S_ModularCurve_FullLevel_AuxLevelOne_exists_cyclotomicConstants_of_isPrimitiveRoot_of_pow_eq_mul_of_ne

set_option autoImplicit false

open IsLocalRing

theorem ModularCurve.FullLevel.AuxLevelOne.exists_cyclotomicConstants_of_isPrimitiveRoot_of_pow_eq_mul_of_ne
    (q : ℕ) [Fact q.Prime] (ℓ : ℕ) [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ) (hℓq : ℓ ≠ q)
    (L : Type) [Field L] [CharZero L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ q)
    (ξ : L) (hξ : IsPrimitiveRoot ξ (q * ℓ))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAq : (q : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ x : A, algebraMap A L x = ζ)
    (t : A) (ht : ∃ w : A, IsUnit w ∧ t ^ (q - 1) = (q : A) * w) :
    ∃ (L₀ : Type) (_ : Field L₀) (_ : CharZero L₀) (_ : Algebra ℚ L₀) (_ : IsCyclotomicExtension {q * ℓ} ℚ L₀)
      (i : L₀ →+* L) (ζ₀ ξ₀ : L₀) (_ : IsPrimitiveRoot ζ₀ q) (_ : IsPrimitiveRoot ξ₀ (q * ℓ))
      (_ : i ζ₀ = ζ) (_ : i ξ₀ = ξ)
      (A₀ : Type) (_ : CommRing A₀) (_ : IsDomain A₀) (_ : IsDiscreteValuationRing A₀) (_ : Algebra A₀ L₀)
      (_ : IsFractionRing A₀ L₀) (_ : Algebra A₀ A) (_ : IsLocalHom (algebraMap A₀ A)),
      Function.Injective (algebraMap A₀ A) ∧
      (∀ a : A₀, algebraMap A L (algebraMap A₀ A a) = i (algebraMap A₀ L₀ a)) ∧

      (∀ x : L₀, (∃ a : A₀, algebraMap A₀ L₀ a = x) ↔ ∃ a : A, algebraMap A L a = i x) ∧
      ((q : A₀) ∈ IsLocalRing.maximalIdeal A₀) ∧ (∃ x : A₀, algebraMap A₀ L₀ x = ζ₀) ∧

      (∀ ϖ₀ : A₀, IsLocalRing.maximalIdeal A₀ = Ideal.span {ϖ₀} →
        ∃ w : A, IsUnit w ∧ algebraMap A₀ A ϖ₀ = t * w) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_FullLevel_AuxLevelOne_exists_cyclotomicConstants_of_isPrimitiveRoot_of_pow_eq_mul_of_ne.solution
