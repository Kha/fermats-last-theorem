import Mathlib
import Definitions.Def_CuspForm_AtkinLehnerOperator
import Definitions.Def_ModularForm_HeckeOperatorForms
import P2M.Util
import P2M.Sol.S_CuspForm_heckeULin_eq_neg_atkinLehnerLin_of_prime_level
attribute [-instance] instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv
attribute [-simp] CuspForm.coe_traceLin_apply FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq

theorem CuspForm.heckeULin_eq_neg_atkinLehnerLin_of_prime_level {ℓ : ℕ} [NeZero ℓ] (hℓ : ℓ.Prime)
    (A : ModularForm.AtkinLehnerDatum ℓ ℓ) (f : CuspForm (CongruenceSubgroup.Gamma0 ℓ) 2) :
    CuspForm.heckeULin 2 (dvd_refl ℓ) f = -CuspForm.atkinLehnerLin A 2 f := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_heckeULin_eq_neg_atkinLehnerLin_of_prime_level.solution
