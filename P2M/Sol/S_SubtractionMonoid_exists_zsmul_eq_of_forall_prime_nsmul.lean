import Mathlib
import Theorems.Thm_SubtractionMonoid_exists_zsmul_eq_of_forall_prime
import P2M.Util
namespace P2MW.S_SubtractionMonoid_exists_zsmul_eq_of_forall_prime_nsmul

set_option Elab.async false

theorem solution {A : Type*} [SubtractionMonoid A]
    (h : ∀ p : ℕ, p.Prime → ∀ x : A, ∃ y : A, p • y = x) :
    ∀ n : ℤ, n ≠ 0 → ∀ x : A, ∃ y : A, n • y = x :=
  SubtractionMonoid.exists_zsmul_eq_of_forall_prime (fun p hp x =>
    (h p hp x).imp fun y hy => by rw [natCast_zsmul]; exact hy)

#print axioms solution
