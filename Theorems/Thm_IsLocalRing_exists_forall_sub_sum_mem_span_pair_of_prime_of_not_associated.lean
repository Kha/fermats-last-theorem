import Mathlib
import P2M.Util
import P2M.Sol.S_IsLocalRing_exists_forall_sub_sum_mem_span_pair_of_prime_of_not_associated

set_option autoImplicit false

open IsLocalRing

theorem IsLocalRing.exists_forall_sub_sum_mem_span_pair_of_prime_of_not_associated
    {A : Type*} [CommRing A] [IsLocalRing A]
    (ϖ : A) (hϖ : maximalIdeal A = Ideal.span {ϖ})
    {S : Type*} [CommRing S] [IsLocalRing S] [IsNoetherianRing S]
    (φ : Polynomial A →+* S)
    (hm : maximalIdeal S = Ideal.span {φ (Polynomial.C ϖ), φ Polynomial.X})
    (hprime : Prime (φ (Polynomial.C ϖ)))
    (χ₀ : S →+* ResidueField A) (hχ₀ : RingHom.ker χ₀ = maximalIdeal S)
    (hχ₀C : ∀ a : A, χ₀ (φ (Polynomial.C a)) = IsLocalRing.residue A a)
    (p : S) (hp : Prime p) (hpϖ : ¬ Associated p (φ (Polynomial.C ϖ))) :
    ∃ n : ℕ, ∀ x : S, ∃ c : Fin n → A,
      x - ∑ i, φ (Polynomial.C (c i)) * φ Polynomial.X ^ (i : ℕ) ∈
        Ideal.span {p, φ (Polynomial.C ϖ)} := by p2m_exact_reverting @_root_.P2MW.S_IsLocalRing_exists_forall_sub_sum_mem_span_pair_of_prime_of_not_associated.solution
