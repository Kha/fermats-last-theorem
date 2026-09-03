import Definitions.Def_GaloisRep_TameCharacter
import P2M.Util
import P2M.Sol.S_ValuationSubring_tameCharacter_pow_left
attribute [-instance] instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy
attribute [-simp] FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply

theorem ValuationSubring.tameCharacter_pow_left
    (P : ValuationSubring (AlgebraicClosure ℚ)) (π : AlgebraicClosure ℚ)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (m : ℕ) : P.tameCharacter (π ^ m) σ = P.tameCharacter π σ ^ m := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_tameCharacter_pow_left.solution
