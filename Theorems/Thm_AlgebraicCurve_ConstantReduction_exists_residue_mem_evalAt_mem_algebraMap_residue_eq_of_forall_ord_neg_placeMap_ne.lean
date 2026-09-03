import Mathlib
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_ConstantReduction_exists_residue_mem_evalAt_mem_algebraMap_residue_eq_of_forall_ord_neg_placeMap_ne
attribute [-instance] instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy
attribute [-simp] ModularCurve.FinitePlaceLift.traceHom_coe ModularCurve.FinitePlaceLift.mk.injEq ModularCurve.FinitePlaceLift.mk.sizeOf_spec WeierstrassCurve.reducePoint_zero FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRep_apply WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply

set_option autoImplicit false

open AlgebraicCurve IsLocalRing

theorem AlgebraicCurve.ConstantReduction.exists_residue_mem_evalAt_mem_algebraMap_residue_eq_of_forall_ord_neg_placeMap_ne
    {L : Type} [Field L] {A : ValuationSubring L}
    {F : Type} [Field F] [Algebra L F] [HasPrincipalDivisors L F]
    {Fbar : Type} [Field Fbar] [Algebra (ResidueField ↥A) Fbar]
    (R : ConstantReduction A F Fbar)
    (P : Place L F) (hP : P.IsRational)
    (f : F) (hf : f ∈ R.integers) (hfP : f ∈ P.toValuationSubring)
    (hpole : ∀ P' : Place L F, P'.ord f < 0 → R.placeMap P' ≠ R.placeMap P) :
    ∃ (hm : R.residue ⟨f, hf⟩ ∈ (R.placeMap P).toValuationSubring) (h : P.evalAt f ∈ A),
      algebraMap (ResidueField ↥A) (R.placeMap P).ResidueField (IsLocalRing.residue ↥A ⟨P.evalAt f, h⟩) =
        IsLocalRing.residue ↥(R.placeMap P).toValuationSubring ⟨R.residue ⟨f, hf⟩, hm⟩ := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_ConstantReduction_exists_residue_mem_evalAt_mem_algebraMap_residue_eq_of_forall_ord_neg_placeMap_ne.solution
