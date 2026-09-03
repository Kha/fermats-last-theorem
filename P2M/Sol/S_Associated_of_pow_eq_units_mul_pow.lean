import Mathlib
import P2M.Util
namespace P2MW.S_Associated_of_pow_eq_units_mul_pow

set_option autoImplicit false

theorem solution
    {R : Type*} [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]
    (a b : R) (n : ℕ) (hn : n ≠ 0) (u : Rˣ) (h : a ^ n = (u : R) * b ^ n) :
    Associated a b := by
  classical
  letI : StrongNormalizationMonoid R := UniqueFactorizationMonoid.normalizationMonoid

  have hassoc : Associated (a ^ n) (b ^ n) := ⟨u⁻¹, by
    rw [h, mul_comm ((u : R)) (b ^ n), mul_assoc, Units.mul_inv, mul_one]⟩
  by_cases ha : a = 0
  · subst ha
    have hb : b ^ n = 0 := by
      have := hassoc.symm
      rw [zero_pow hn] at this
      exact associated_zero_iff_eq_zero _ |>.mp this
    rw [pow_eq_zero_iff hn] at hb
    rw [hb]
  by_cases hb : b = 0
  · subst hb
    have : a ^ n = 0 := by
      rw [zero_pow hn] at hassoc
      exact associated_zero_iff_eq_zero _ |>.mp hassoc
    exact absurd ((pow_eq_zero_iff hn).mp this) ha
  have key := hassoc.normalizedFactors_eq
  rw [UniqueFactorizationMonoid.normalizedFactors_pow, UniqueFactorizationMonoid.normalizedFactors_pow,
    nsmul_right_inj hn] at key
  exact (UniqueFactorizationMonoid.associated_iff_normalizedFactors_eq_normalizedFactors ha hb).mpr key
