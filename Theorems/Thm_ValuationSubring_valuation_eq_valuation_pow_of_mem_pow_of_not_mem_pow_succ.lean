import Mathlib
import Definitions.Def_FLTPrelim_Ramification
import P2M.Util
import P2M.Sol.S_ValuationSubring_valuation_eq_valuation_pow_of_mem_pow_of_not_mem_pow_succ

set_option autoImplicit false

open NumberField

theorem ValuationSubring.valuation_eq_valuation_pow_of_mem_pow_of_not_mem_pow_succ
    (P : ValuationSubring (AlgebraicClosure ℚ))
    (M : Type) [Field M] [NumberField M] [Algebra M (AlgebraicClosure ℚ)]
    (Q : Ideal (𝓞 M)) [Q.IsMaximal]
    (hQle : ∀ x : 𝓞 M, P.valuation (algebraMap M (AlgebraicClosure ℚ) x) ≤ 1)
    (hQlt : ∀ x : 𝓞 M, x ∈ Q ↔ P.valuation (algebraMap M (AlgebraicClosure ℚ) x) < 1)
    (π : 𝓞 M) (hπ : π ∈ Q) (hπ2 : π ∉ Q ^ 2)
    (n : ℕ) (x : 𝓞 M) (hx : x ∈ Q ^ n) (hx' : x ∉ Q ^ (n + 1)) :
    P.valuation (algebraMap M (AlgebraicClosure ℚ) x) = P.valuation (algebraMap M (AlgebraicClosure ℚ) π) ^ n := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_valuation_eq_valuation_pow_of_mem_pow_of_not_mem_pow_succ.solution
