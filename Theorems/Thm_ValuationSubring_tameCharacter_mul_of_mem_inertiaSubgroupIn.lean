import Definitions.Def_GaloisRep_TameCharacter
import Definitions.Def_FLTPrelim_Ramification
import P2M.Util
import P2M.Sol.S_ValuationSubring_tameCharacter_mul_of_mem_inertiaSubgroupIn
attribute [-instance] WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy
attribute [-simp] WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply

theorem ValuationSubring.tameCharacter_mul_of_mem_inertiaSubgroupIn
    (P : ValuationSubring (AlgebraicClosure ℚ)) (π : AlgebraicClosure ℚ) (hπ : π ≠ 0)
    {σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ} (hσ : σ ∈ P.inertiaSubgroupIn ℚ)
    (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    P.tameCharacter π (σ * τ) = P.tameCharacter π σ * P.tameCharacter π τ := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_tameCharacter_mul_of_mem_inertiaSubgroupIn.solution
