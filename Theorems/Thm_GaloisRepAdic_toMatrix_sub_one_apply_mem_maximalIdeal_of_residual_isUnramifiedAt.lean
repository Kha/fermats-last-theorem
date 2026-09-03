import Mathlib
import Definitions.Def_GaloisRep_Adic
import Definitions.Def_GaloisRep_LocalConditions
import P2M.Util
import P2M.Sol.S_GaloisRepAdic_toMatrix_sub_one_apply_mem_maximalIdeal_of_residual_isUnramifiedAt

set_option autoImplicit false
open IsLocalRing
theorem GaloisRepAdic.toMatrix_sub_one_apply_mem_maximalIdeal_of_residual_isUnramifiedAt
    {A : Type} [CommRing A] [IsLocalRing A] (ρ : GaloisRepAdic A) {q : ℕ} (hunr : ρ.residual.IsUnramifiedAt q)
    (b : Module.Basis (Fin 2) A ρ.V) (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime q)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσ : σ ∈ P.inertiaSubgroupIn ℚ) (i j : Fin 2) :
    LinearMap.toMatrix b b (ρ.ρ σ) i j - (1 : Matrix (Fin 2) (Fin 2) A) i j ∈ IsLocalRing.maximalIdeal A := by p2m_exact_reverting @_root_.P2MW.S_GaloisRepAdic_toMatrix_sub_one_apply_mem_maximalIdeal_of_residual_isUnramifiedAt.solution
