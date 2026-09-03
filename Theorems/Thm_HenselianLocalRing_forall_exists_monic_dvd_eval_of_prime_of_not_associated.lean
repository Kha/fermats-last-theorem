import Mathlib
import P2M.Util
import P2M.Sol.S_HenselianLocalRing_forall_exists_monic_dvd_eval_of_prime_of_not_associated

set_option autoImplicit false

open IsLocalRing

theorem HenselianLocalRing.forall_exists_monic_dvd_eval_of_prime_of_not_associated
    {A : Type*} [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [HenselianLocalRing A]
    (ϖ : A) (hϖ : maximalIdeal A = Ideal.span {ϖ})
    {S : Type*} [CommRing S] [IsLocalRing S] [IsNoetherianRing S]
    (φ : Polynomial A →+* S) (hφf : φ.EssFiniteType)
    (hm : maximalIdeal S = Ideal.span {φ (Polynomial.C ϖ), φ Polynomial.X})
    (hprime : Prime (φ (Polynomial.C ϖ)))
    (χ₀ : S →+* ResidueField A) (hχ₀ : RingHom.ker χ₀ = maximalIdeal S)
    (hχ₀C : ∀ a : A, χ₀ (φ (Polynomial.C a)) = IsLocalRing.residue A a) :
    ∀ p : S, Prime p → ¬ Associated p (φ (Polynomial.C ϖ)) →
      ∀ x : S, ∃ r : Polynomial A, r.Monic ∧ p ∣ (r.map (φ.comp Polynomial.C)).eval x := by p2m_exact_reverting @_root_.P2MW.S_HenselianLocalRing_forall_exists_monic_dvd_eval_of_prime_of_not_associated.solution
