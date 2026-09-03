import Mathlib
import Definitions.Def_FLTPrelim_Ramification
import P2M.Util
import P2M.Sol.S_ValuationSubring_eq_bot_of_isPrime_of_ne_maximalIdeal_of_liesOverPrime

set_option autoImplicit false

theorem ValuationSubring.eq_bot_of_isPrime_of_ne_maximalIdeal_of_liesOverPrime
    {p : ℕ} (hp : p.Prime) (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (𝔮 : Ideal ↥A) [𝔮.IsPrime] (h𝔮 : 𝔮 ≠ IsLocalRing.maximalIdeal ↥A) : 𝔮 = ⊥ := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_eq_bot_of_isPrime_of_ne_maximalIdeal_of_liesOverPrime.solution
