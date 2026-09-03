import Mathlib
import P2M.Util
import P2M.Sol.S_Ideal_isSeparable_quotient_of_forall_prime_not_dvd_card_inertia

set_option autoImplicit false

open scoped Pointwise

theorem Ideal.isSeparable_quotient_of_forall_prime_not_dvd_card_inertia
    {R S : Type*} [CommRing R] [IsDedekindDomain R] [CommRing S] [IsDedekindDomain S]
    [Algebra R S] [Module.Finite R S] [Module.IsTorsionFree R S]
    {G : Type*} [Group G] [Finite G] [MulSemiringAction G S] [IsGaloisGroup G R S]
    (p : Ideal R) [p.IsMaximal] (hp : p ≠ ⊥) (P : Ideal S) [P.IsMaximal] [P.LiesOver p]
    (hI : ∀ ℓ : ℕ, ℓ.Prime → (ℓ : R ⧸ p) = 0 → ¬ ℓ ∣ Nat.card ↥(P.inertia G)) :
    Algebra.IsSeparable (R ⧸ p) (S ⧸ P) := by p2m_exact_reverting @_root_.P2MW.S_Ideal_isSeparable_quotient_of_forall_prime_not_dvd_card_inertia.solution
