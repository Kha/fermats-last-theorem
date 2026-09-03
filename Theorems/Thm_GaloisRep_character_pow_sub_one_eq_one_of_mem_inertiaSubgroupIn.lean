import Mathlib
import Definitions.Def_GaloisRep_Residual
import Definitions.Def_FLTPrelim_Ramification
import P2M.Util
import P2M.Sol.S_GaloisRep_character_pow_sub_one_eq_one_of_mem_inertiaSubgroupIn

set_option autoImplicit false

theorem GaloisRep.character_pow_sub_one_eq_one_of_mem_inertiaSubgroupIn
    {K : Type} [Field K] (p : ℕ) [Fact p.Prime] [CharP K p]
    (χ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Kˣ)
    (hχ : GaloisFactorsThroughFiniteLevel χ)
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime p)
    {τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ} (hτ : τ ∈ P.inertiaSubgroupIn ℚ) :
    χ τ ^ (p - 1) = 1 := by p2m_exact_reverting @_root_.P2MW.S_GaloisRep_character_pow_sub_one_eq_one_of_mem_inertiaSubgroupIn.solution
