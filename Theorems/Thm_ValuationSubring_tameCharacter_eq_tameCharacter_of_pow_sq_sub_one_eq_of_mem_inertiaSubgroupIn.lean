import Mathlib
import Definitions.Def_GaloisRep_TameCharacter
import Definitions.Def_FLTPrelim_Ramification
import P2M.Util
import P2M.Sol.S_ValuationSubring_tameCharacter_eq_tameCharacter_of_pow_sq_sub_one_eq_of_mem_inertiaSubgroupIn

set_option autoImplicit false

theorem ValuationSubring.tameCharacter_eq_tameCharacter_of_pow_sq_sub_one_eq_of_mem_inertiaSubgroupIn
    (q : ℕ) [Fact q.Prime] (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime q)
    (π π' : AlgebraicClosure ℚ) (hπ : π ^ (q ^ 2 - 1) = (q : AlgebraicClosure ℚ))
    (hπ' : π' ^ (q ^ 2 - 1) = (q : AlgebraicClosure ℚ))
    (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hτ : τ ∈ P.inertiaSubgroupIn ℚ) :
    P.tameCharacter π τ = P.tameCharacter π' τ := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_tameCharacter_eq_tameCharacter_of_pow_sq_sub_one_eq_of_mem_inertiaSubgroupIn.solution
