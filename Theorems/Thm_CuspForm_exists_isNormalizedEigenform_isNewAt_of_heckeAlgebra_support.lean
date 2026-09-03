import Mathlib
import Definitions.Def_CuspForm_HeckeAlgebra
import Definitions.Def_ModularForm_AtkinLehnerDatum
import Definitions.Def_CuspForm_LevelLoweringTrace
import Definitions.Def_CuspForm_AtkinLehnerOperator
import Definitions.Def_FLTPrelim_Modularity
import P2M.Util
import P2M.Sol.S_CuspForm_exists_isNormalizedEigenform_isNewAt_of_heckeAlgebra_support
attribute [-instance] instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv
attribute [-simp] PowerSeries.coeff_heckeV PowerSeries.coeff_heckeU FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq

set_option autoImplicit false
open CongruenceSubgroup
theorem CuspForm.exists_isNormalizedEigenform_isNewAt_of_heckeAlgebra_support
    {M q : ℕ} [NeZero M] (A : ModularForm.AtkinLehnerDatum M q) (hq : q.Prime)
    (𝔭 : Ideal (CuspForm.heckeAlgebra M 2 {ℓ | ℓ ∣ M})) (h𝔭 : 𝔭.IsPrime)
    (hsupp : ∀ T : CuspForm.heckeAlgebra M 2 {ℓ | ℓ ∣ M},
        (∀ g ∈ LinearMap.ker (CuspForm.traceLin A hq)
              ⊓ LinearMap.ker ((CuspForm.traceLin A hq) ∘ₗ (CuspForm.atkinLehnerLin A 2)),
          (T : Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0 M) 2)) g = 0)
          → T ∈ 𝔭) :
    ∃ (f : CuspForm (CongruenceSubgroup.Gamma0 M) 2) (hf : f.IsNormalizedEigenform)
      (χ : CuspForm.heckeAlgebra M 2 {ℓ | ℓ ∣ M} →+* integralClosure ℤ ℂ),
      (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M),
        (χ (CuspForm.heckeAlgebra.T hℓ hℓM hℓM) : ℂ) = ModularFormClass.qCoeff f ℓ) ∧
      RingHom.ker χ ≤ 𝔭 ∧
      ModularFormClass.qCoeff f q ^ 2 = 1 := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_exists_isNormalizedEigenform_isNewAt_of_heckeAlgebra_support.solution
