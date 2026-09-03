import Definitions.Def_GaloisRep_TameCharacter
import Definitions.Def_FLTPrelim_Ramification
import P2M.Util
import P2M.Sol.S_ValuationSubring_apply_eq_self_of_pow_eq_one_of_tameCharacter_eq_one
attribute [-instance] WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy
attribute [-simp] WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply

set_option autoImplicit false

theorem ValuationSubring.apply_eq_self_of_pow_eq_one_of_tameCharacter_eq_one
    (q : ℕ) [Fact q.Prime] (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime q)
    (π : AlgebraicClosure ℚ) (hπ : π ^ (q ^ 2 - 1) = (q : AlgebraicClosure ℚ))
    {τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ} (hτ : τ ∈ P.inertiaSubgroupIn ℚ)
    (hτπ : P.tameCharacter π τ = 1) {ζ : AlgebraicClosure ℚ} (hζ : ζ ^ q = 1) :
    τ ζ = ζ := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_apply_eq_self_of_pow_eq_one_of_tameCharacter_eq_one.solution
