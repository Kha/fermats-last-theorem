import Mathlib
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Theorems.Thm_ValuationSubring_exists_isFrobeniusAt_of_liesOverPrime
import P2M.Util
namespace P2MW.S_ValuationSubring_exists_isFrobeniusAt_of_liesOverPrime_algebraicClosure_rat

set_option autoImplicit false

theorem solution
    {p : ℕ} (hp : p.Prime) {A : ValuationSubring (AlgebraicClosure ℚ)}
    (hA : A.LiesOverPrime p) :
    ∃ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt σ p :=
  ValuationSubring.exists_isFrobeniusAt_of_liesOverPrime hp A hA
