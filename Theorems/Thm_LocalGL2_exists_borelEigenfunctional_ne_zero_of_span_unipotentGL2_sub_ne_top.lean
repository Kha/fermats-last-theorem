import Mathlib
import Definitions.Def_RepTheory_SmoothAdmissibleSchurCommutant
import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_AdelicDock_LocalEmbedding
import P2M.Util
import P2M.Sol.S_LocalGL2_exists_borelEigenfunctional_ne_zero_of_span_unipotentGL2_sub_ne_top
attribute [-instance] instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions HeckePair.instSMulCommClassSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instAlgebraSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instOneSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instIsScalarTowerSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instRingSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instMulSubtypeForallMemSubmoduleHeckeAlgebra FixedPoints.instMulActionElemFixedPointsOfSMulCommClass_definitions FixedPoints.module FixedPoints.instSMulElemFixedPointsOfSMulCommClass_definitions FixedPoints.instAddCommMonoidElemFixedPoints_definitions
attribute [-simp] LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one HeckePair.convTerm_mk HeckePair.coe_apply_add HeckePair.coe_apply_smul FixedPoints.coe_zero FixedPoints.coe_smul FixedPoints.coe_add LocalGL2.swapUnit_val

set_option autoImplicit false

open IsDedekindDomain NumberField
open FLT.SmoothAdmissibleSchurCommutant

theorem LocalGL2.exists_borelEigenfunctional_ne_zero_of_span_unipotentGL2_sub_ne_top
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : GL (Fin 2) (v.adicCompletion K) →* Module.End ℂ V)
    (hsm : IsSmoothRep π) (hadm : IsAdmissibleRep π) (hirr : IsIrreducibleRep π)
    (hN : Submodule.span ℂ {y : V | ∃ (t : v.adicCompletion K) (z : V),
      y = π (AutomorphicForm.unipotentGL2 t) z - z} ≠ ⊤) :
    ∃ (χ ω : (v.adicCompletion K)ˣ →* ℂˣ) (ℓ : V →ₗ[ℂ] ℂ), ℓ ≠ 0 ∧
      (∀ (x : v.adicCompletion K) (w : V), ℓ (π (AutomorphicForm.unipotentGL2 x) w) = ℓ w) ∧
      (∀ (a : (v.adicCompletion K)ˣ) (w : V), ℓ (π (AdelicLevel.diagOne a) w) = χ a * ℓ w) ∧
      (∀ (a : (v.adicCompletion K)ˣ) (w : V),
        ℓ (π (Matrix.GeneralLinearGroup.scalar (Fin 2) a) w) = ω a * ℓ w) := by p2m_exact_reverting @_root_.P2MW.S_LocalGL2_exists_borelEigenfunctional_ne_zero_of_span_unipotentGL2_sub_ne_top.solution
