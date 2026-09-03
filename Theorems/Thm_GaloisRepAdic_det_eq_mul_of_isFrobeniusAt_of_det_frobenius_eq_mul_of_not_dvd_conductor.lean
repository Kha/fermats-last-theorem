import Mathlib
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Definitions.Def_GaloisRep_Adic
import P2M.Util
import P2M.Sol.S_GaloisRepAdic_det_eq_mul_of_isFrobeniusAt_of_det_frobenius_eq_mul_of_not_dvd_conductor
attribute [-instance] FrobeniusDensity.isMaximal_ratPrimeIdeal FrobeniusDensity.liesOver_ratBelow AlgebraicClosure.Rat.isGalois
attribute [-simp] TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec

set_option autoImplicit false

theorem GaloisRepAdic.det_eq_mul_of_isFrobeniusAt_of_det_frobenius_eq_mul_of_not_dvd_conductor
    {O : Type} [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
    (p : ℕ) [Fact p.Prime] [Algebra ℤ_[p] O] (hp : (p : O) ∈ IsLocalRing.maximalIdeal O)
    (M₀ q : ℕ) (hq : q.Prime) (hqM₀ : ¬ q ∣ M₀) (hqp : q ≠ p)
    (ε : DirichletCharacter ℂ (M₀ * q)) (hqε : ¬ q ∣ ε.conductor) (S : Finset ℕ)
    (R : Type) [CommRing R] (toC : R →+* ℂ) (htoC : Function.Injective toC) (φ : R →+* O)
    (e : ℕ → R)
    (he : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ M₀ * q → ℓ ∉ S → toC (e ℓ) = ε (ℓ : ZMod (M₀ * q)))
    (ρ : GaloisRepAdic O)
    (hdet : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ M₀ * q → ℓ ∉ S → ℓ ≠ p →
      ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
        ∀ τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt τ ℓ →
          LinearMap.det (ρ.ρ τ) = φ (e ℓ) * (ℓ : O))
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime q)
    (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hτ : P.IsFrobeniusAt τ q)
    (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M₀ * q) (hℓS : ℓ ∉ S) (hℓq : ℓ ≡ q [MOD M₀]) :
    LinearMap.det (ρ.ρ τ) = φ (e ℓ) * (q : O) := by p2m_exact_reverting @_root_.P2MW.S_GaloisRepAdic_det_eq_mul_of_isFrobeniusAt_of_det_frobenius_eq_mul_of_not_dvd_conductor.solution
