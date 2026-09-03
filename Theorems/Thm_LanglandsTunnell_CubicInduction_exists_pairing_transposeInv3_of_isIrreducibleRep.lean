import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_RepTheory_SmoothAdmissibleSchurCommutant
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep
attribute [-instance] instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instFinite
attribute [-simp] ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq

set_option autoImplicit false

open IsDedekindDomain NumberField FLT.SmoothAdmissibleSchurCommutant

theorem LanglandsTunnell.CubicInduction.exists_pairing_transposeInv3_of_isIrreducibleRep
    (v : HeightOneSpectrum (𝓞 ℚ)) (V : Type) [AddCommGroup V] [Module ℂ V]
    (π : LocalGL3 v →* Module.End ℂ V)
    (_hirr : IsIrreducibleRep π) (_hsm : IsSmoothRep π) (_hadm : IsAdmissibleRep π) :
    ∃ P : V →ₗ[ℂ] V →ₗ[ℂ] ℂ,
      (∀ (g : LocalGL3 v) (x y : V), P (π g x) (π (transposeInv3 g) y) = P x y) ∧
      (∀ y : V, (∀ x : V, P x y = 0) → y = 0) ∧
      (∀ L : V →ₗ[ℂ] ℂ,
        (∃ U : Subgroup (LocalGL3 v), IsOpen (U : Set (LocalGL3 v)) ∧ ∀ u ∈ U, ∀ x : V, L (π u x) = L x) →
        ∃ y : V, ∀ x : V, L x = P x y) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.solution
