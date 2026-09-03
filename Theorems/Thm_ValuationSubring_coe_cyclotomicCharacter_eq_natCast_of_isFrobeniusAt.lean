import Mathlib.NumberTheory.Cyclotomic.CyclotomicCharacter
import Definitions.Def_EllipticCurve_FrobeniusTrace
import P2M.Util
import P2M.Sol.S_ValuationSubring_coe_cyclotomicCharacter_eq_natCast_of_isFrobeniusAt

set_option autoImplicit false

theorem ValuationSubring.coe_cyclotomicCharacter_eq_natCast_of_isFrobeniusAt
    {p : ℕ} [Fact p.Prime] {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓp : ℓ ≠ p)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime ℓ)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσ : A.IsFrobeniusAt σ ℓ) :
    ((cyclotomicCharacter (AlgebraicClosure ℚ) p σ.toRingEquiv : ℤ_[p]ˣ) : ℤ_[p]) = ℓ := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_coe_cyclotomicCharacter_eq_natCast_of_isFrobeniusAt.solution
