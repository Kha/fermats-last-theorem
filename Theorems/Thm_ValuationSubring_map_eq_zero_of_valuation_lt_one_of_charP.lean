module

public import Mathlib
public import Definitions.Def_FLTPrelim_Ramification
import P2M.Util
import P2M.Sol.S_ValuationSubring_map_eq_zero_of_valuation_lt_one_of_charP

@[expose] public section

theorem ValuationSubring.map_eq_zero_of_valuation_lt_one_of_charP
    (A : ValuationSubring (AlgebraicClosure ℚ)) (ℓ : ℕ) [Fact ℓ.Prime] (hA : A.LiesOverPrime ℓ)
    {k : Type*} [Field k] [CharP k ℓ] (red : ↥A →+* k)
    (τ : ↥A) (hτ : A.valuation (τ : AlgebraicClosure ℚ) < 1) :
    red τ = 0 := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_map_eq_zero_of_valuation_lt_one_of_charP.solution
