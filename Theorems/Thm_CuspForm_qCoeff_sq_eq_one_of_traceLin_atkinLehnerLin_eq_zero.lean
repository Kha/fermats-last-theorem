import Mathlib
import Definitions.Def_CuspForm_AtkinLehnerOperator
import Definitions.Def_CuspForm_LevelLoweringTrace
import Definitions.Def_ModularForm_HeckeOperatorForms
import Definitions.Def_FLTPrelim_Modularity
import P2M.Util
import P2M.Sol.S_CuspForm_qCoeff_sq_eq_one_of_traceLin_atkinLehnerLin_eq_zero
attribute [-instance] instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv
attribute [-simp] FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq

theorem CuspForm.qCoeff_sq_eq_one_of_traceLin_atkinLehnerLin_eq_zero {N q : ℕ} [NeZero N]
    (W : ModularForm.AtkinLehnerDatum N q) (hq : q.Prime)
    {f : CuspForm (CongruenceSubgroup.Gamma0 N) 2} (hf : f.IsNormalizedEigenform)
    (h : CuspForm.traceLin W hq (CuspForm.atkinLehnerLin W 2 f) = 0) :
    ModularFormClass.qCoeff f q ^ 2 = 1 := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_qCoeff_sq_eq_one_of_traceLin_atkinLehnerLin_eq_zero.solution
