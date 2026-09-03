import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_GaloisRep_TameCharacter
import P2M.Util
import P2M.Sol.S_ValuationSubring_tameCharacter_pow_sq_sub_one_eq_one_of_mem_inertiaSubgroupIn

set_option autoImplicit false
theorem ValuationSubring.tameCharacter_pow_sq_sub_one_eq_one_of_mem_inertiaSubgroupIn (p : ℕ) [Fact p.Prime]
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime p)
    (π : AlgebraicClosure ℚ) (hπ : π ^ (p ^ 2 - 1) = (p : AlgebraicClosure ℚ))
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσ : σ ∈ P.inertiaSubgroupIn ℚ) :
    P.tameCharacter π σ ^ (p ^ 2 - 1) = 1 := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_tameCharacter_pow_sq_sub_one_eq_one_of_mem_inertiaSubgroupIn.solution
