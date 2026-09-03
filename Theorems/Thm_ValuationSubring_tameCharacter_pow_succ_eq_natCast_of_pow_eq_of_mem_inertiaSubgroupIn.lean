import Definitions.Def_GaloisRep_TameCharacter
import Definitions.Def_FLTPrelim_Ramification
import P2M.Util
import P2M.Sol.S_ValuationSubring_tameCharacter_pow_succ_eq_natCast_of_pow_eq_of_mem_inertiaSubgroupIn
attribute [-instance] WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy
attribute [-simp] WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply

theorem ValuationSubring.tameCharacter_pow_succ_eq_natCast_of_pow_eq_of_mem_inertiaSubgroupIn
    (P : ValuationSubring (AlgebraicClosure ℚ)) (p : ℕ) [Fact p.Prime] (hP : P.LiesOverPrime p)
    (π : AlgebraicClosure ℚ) (hπ : π ^ (p ^ 2 - 1) = (p : AlgebraicClosure ℚ))
    {σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ} (hσ : σ ∈ P.inertiaSubgroupIn ℚ)
    {ζ : AlgebraicClosure ℚ} (hζp : ζ ^ p = 1) (hζ1 : ζ ≠ 1) {a : ℕ} (hσζ : σ ζ = ζ ^ a) :
    P.tameCharacter π σ ^ (p + 1) = (a : IsLocalRing.ResidueField P) := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_tameCharacter_pow_succ_eq_natCast_of_pow_eq_of_mem_inertiaSubgroupIn.solution
