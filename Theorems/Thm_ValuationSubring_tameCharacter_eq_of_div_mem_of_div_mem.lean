import Definitions.Def_GaloisRep_TameCharacter
import Definitions.Def_FLTPrelim_Ramification
import P2M.Util
import P2M.Sol.S_ValuationSubring_tameCharacter_eq_of_div_mem_of_div_mem
attribute [-instance] WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy
attribute [-simp] WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply

theorem ValuationSubring.tameCharacter_eq_of_div_mem_of_div_mem
    (P : ValuationSubring (AlgebraicClosure ℚ)) (π π' : AlgebraicClosure ℚ) (hπ : π ≠ 0) (hπ' : π' ≠ 0)
    (hu : π' / π ∈ P) (hu' : π / π' ∈ P) {σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ}
    (hσ : σ ∈ P.inertiaSubgroupIn ℚ) :
    P.tameCharacter π' σ = P.tameCharacter π σ := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_tameCharacter_eq_of_div_mem_of_div_mem.solution
