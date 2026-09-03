import Definitions.Def_GaloisRep_Adic
import P2M.Util
import P2M.Sol.S_GaloisRepAdic_exists_pow_prime_pow_eq_one_of_wild

set_option autoImplicit false
open Polynomial

theorem GaloisRepAdic.exists_pow_prime_pow_eq_one_of_wild
    {A : Type} [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (ρ : GaloisRepAdic A)
    {p : ℕ} (hp : p.Prime) (hpA : (p : A) ∈ IsLocalRing.maximalIdeal A) {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime q)
    {σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ}
    (hwild : ∀ z : AlgebraicClosure ℚ, z ≠ 0 → σ z * z⁻¹ - 1 ∈ P.nonunits) :
    ∃ k : ℕ, ρ.ρ σ ^ q ^ k = 1 := by p2m_exact_reverting @_root_.P2MW.S_GaloisRepAdic_exists_pow_prime_pow_eq_one_of_wild.solution
