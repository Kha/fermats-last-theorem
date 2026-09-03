import Definitions.Def_CuspForm_AdelicLiftGamma1
import Definitions.Def_CuspForm_AdelicLift
import Definitions.Def_AutomorphicForm_BoundedGenuineCuspRealization
import P2M.Util
import P2M.Sol.S_CuspForm_IsAdelicLiftOf_isBoundedGenuineFn_productionPinsGeneral_stdAddChar
attribute [-instance] WeierstrassCurve.Affine.Point.instFinite instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv
attribute [-simp] AutomorphicForm.CuspidalConstituent.rightRegular_apply AutomorphicForm.IsStableLinearOn.coe_toEnd_apply AutomorphicForm.ArchRepAt.mk.sizeOf_spec AutomorphicForm.IsIsotypicCuspFormAt.toRealization_toFun AutomorphicForm.ArchTypeFamily.mk.sizeOf_spec AutomorphicForm.charRep_apply AutomorphicForm.ArchRepAt.mk.injEq AutomorphicForm.ArchTypeFamily.mk.injEq M4aHerbrand.IdeleGaloisDescent.mk.sizeOf_spec M4aHerbrand.IdeleGaloisDescent.mk.injEq FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq

set_option autoImplicit false

open NumberField open AutomorphicForm hiding whittakerCoefficientIntegrable_and_summable_of_isKfSmooth_of_contDiff

theorem CuspForm.IsAdelicLiftOf.isBoundedGenuineFn_productionPinsGeneral_stdAddChar
    {M : ℕ} [NeZero M] {g : CuspForm (CongruenceSubgroup.Gamma0 M) 2}
    (Φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (hΦ : CuspForm.IsAdelicLiftOf g Φ) :
    IsBoundedGenuineFn ℚ (productionPinsGeneral ℚ) (NumberField.StandardAddChar.stdAddChar ℚ) Φ := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_IsAdelicLiftOf_isBoundedGenuineFn_productionPinsGeneral_stdAddChar.solution
