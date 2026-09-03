import Mathlib
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_ModularCurve_ArithmeticGalois
import P2M.Util
import P2M.Sol.S_ModularCurve_inertiaField_comap_isDVR_and_residue_surjective_and_place_fixed
attribute [-instance] AlgebraicClosure.Rat.isGalois ValuationSubring.instIsAlgClosedResidueField WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy
attribute [-simp] ValuationSubring.reduceAt_coe ValuationSubring.reduceAt_one ValuationSubring.reduceAt_natCast ValuationSubring.reduceAt_intCast ValuationSubring.reduceAt_zero WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply
set_option autoImplicit false
open AlgebraicCurve ModularCurve

set_option maxHeartbeats 400000 in

theorem ModularCurve.inertiaField_comap_isDVR_and_residue_surjective_and_place_fixed
    (p : ℕ) [Fact p.Prime] (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (M : ℕ) [NeZero M] :

    IsDiscreteValuationRing ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))) ∧
    IsLocalRing.maximalIdeal ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))) = Ideal.span {((p : ℕ) : ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))))} ∧

    Function.Surjective (fun x : ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))) =>
      IsLocalRing.residue ↥A ⟨((x : ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ))) : AlgebraicClosure ℚ), x.2⟩) ∧

    (∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M),
      (∀ σ ∈ A.inertiaSubgroupIn ℚ, arithmeticGalois (modularFunctionFieldFull M) σ • V = V) →
      ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
        (∀ a : ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)), σ (a : AlgebraicClosure ℚ) = a) →
        arithmeticGalois (modularFunctionFieldFull M) σ • V = V) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_inertiaField_comap_isDVR_and_residue_surjective_and_place_fixed.solution
