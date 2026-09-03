import Mathlib
import Definitions.Def_FLTPrelim_Ramification
import P2M.Util
import P2M.Sol.S_ValuationSubring_nonempty_residueField_algEquiv_algebraicClosure_galoisField
attribute [-instance] ValuationSubring.instIsAlgClosedResidueField WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy
attribute [-simp] ValuationSubring.reduceAt_coe ValuationSubring.reduceAt_one ValuationSubring.reduceAt_natCast ValuationSubring.reduceAt_intCast ValuationSubring.reduceAt_zero WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply

set_option autoImplicit false

theorem ValuationSubring.nonempty_residueField_algEquiv_algebraicClosure_galoisField
    (q : ℕ) [Fact q.Prime] (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime q)
    (ι : GaloisField q 2 →+* IsLocalRing.ResidueField P) :
    letI : Algebra (GaloisField q 2) (IsLocalRing.ResidueField P) := ι.toAlgebra
    Nonempty (IsLocalRing.ResidueField P ≃ₐ[GaloisField q 2] AlgebraicClosure (GaloisField q 2)) := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_nonempty_residueField_algEquiv_algebraicClosure_galoisField.solution
