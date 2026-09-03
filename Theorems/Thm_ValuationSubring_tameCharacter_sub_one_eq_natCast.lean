import Definitions.Def_GaloisRep_TameCharacter
import P2M.Util
import P2M.Sol.S_ValuationSubring_tameCharacter_sub_one_eq_natCast
attribute [-instance] instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy
attribute [-simp] FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply

theorem ValuationSubring.tameCharacter_sub_one_eq_natCast
    (P : ValuationSubring (AlgebraicClosure ℚ)) {ζ : AlgebraicClosure ℚ} (hζP : ζ ∈ P)
    (hres : IsLocalRing.residue P ⟨ζ, hζP⟩ = 1) (hζ1 : ζ ≠ 1)
    {σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ} {a : ℕ} (hσζ : σ ζ = ζ ^ a) :
    P.tameCharacter (ζ - 1) σ = a := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_tameCharacter_sub_one_eq_natCast.solution
