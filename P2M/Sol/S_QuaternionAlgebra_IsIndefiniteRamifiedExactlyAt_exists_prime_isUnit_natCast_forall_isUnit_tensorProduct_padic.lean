import Mathlib
import Definitions.Def_CerednikDrinfeld_ShimuraCurve
import Theorems.Thm_IsLocalRing_isUnit_natCast_or_isUnit_natCast_of_coprime
import Theorems.Thm_QuaternionAlgebra_IsIndefiniteRamifiedExactlyAt_forall_isUnit_tensorProduct_padic_iff
import P2M.Util
namespace P2MW.S_QuaternionAlgebra_IsIndefiniteRamifiedExactlyAt_exists_prime_isUnit_natCast_forall_isUnit_tensorProduct_padic

set_option autoImplicit false

open scoped Quaternion TensorProduct

theorem solution
    {a b : ℚ} {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hne : q ≠ q')
    (hB : QuaternionAlgebra.IsIndefiniteRamifiedExactlyAt a b q q')
    (R : Type*) [CommRing R] [IsLocalRing R] :
    ∃ (ℓ : ℕ) (_ : Fact ℓ.Prime), (ℓ = q ∨ ℓ = q') ∧ IsUnit (ℓ : R) ∧
      ∀ x : ℍ[ℚ, a, b] ⊗[ℚ] ℚ_[ℓ], x ≠ 0 → IsUnit x := by
  have hq : q.Prime := Fact.out
  have hq' : q'.Prime := Fact.out
  rcases IsLocalRing.isUnit_natCast_or_isUnit_natCast_of_coprime (R := R)
      ((Nat.coprime_primes hq hq').2 hne) with h | h
  · exact ⟨q, inferInstance, Or.inl rfl, h,
      (QuaternionAlgebra.IsIndefiniteRamifiedExactlyAt.forall_isUnit_tensorProduct_padic_iff hB q).2
        (Or.inl dvd_rfl)⟩
  · exact ⟨q', inferInstance, Or.inr rfl, h,
      (QuaternionAlgebra.IsIndefiniteRamifiedExactlyAt.forall_isUnit_tensorProduct_padic_iff hB q').2
        (Or.inr dvd_rfl)⟩
