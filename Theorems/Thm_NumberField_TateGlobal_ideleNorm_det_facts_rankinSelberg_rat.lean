import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_LanglandsTunnell_RankinSelbergEuler
import Definitions.Def_LanglandsTunnell_RS22GlobalIntegral
import Definitions.Def_AutomorphicForm_GodementSection
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_RSCarrierSplit
import Definitions.Def_LanglandsTunnell_DeltaLift
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_AutomorphicForm_SiegelCoordinates
import Definitions.Def_AutomorphicForm_RowIsometryInvariance
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Mathlib.MeasureTheory.Group.FundamentalDomain
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_AutomorphicForm_ArchWeightCharTransport
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_WhittakerModelLocal
import Definitions.Def_LanglandsTunnell_ConverseData
import Mathlib.Analysis.MellinTransform
import Definitions.Def_AutomorphicForm_RightConvolution
import Definitions.Def_AutomorphicForm_BoundedGenuineCuspRealization
import P2M.Util
import P2M.Sol.S_NumberField_TateGlobal_ideleNorm_det_facts_rankinSelberg_rat
attribute [-instance] instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions

set_option autoImplicit false

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicFourier IsDedekindDomain
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering AutomorphicForm.SiegelCoordinates
open LanglandsTunnell LanglandsTunnell.RankinSelberg RSCarrier UnramifiedWhittaker

theorem NumberField.TateGlobal.ideleNorm_det_facts_rankinSelberg_rat
    (ϖ : ∀ v : HeightOneSpectrum (𝓞 ℚ), v.adicCompletionIntegers ℚ)
    (hϖ : ∀ v : HeightOneSpectrum (𝓞 ℚ),
      Valued.v (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) (ϖ v)) = WithZero.exp (-1 : ℤ))
    (hπall : ∀ v : HeightOneSpectrum (𝓞 ℚ),
      algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) (ϖ v) ≠ 0) :
    (∀ g : AdelicGL2 (𝓞 ℚ) ℚ, TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det g) =
      |((Matrix.GeneralLinearGroup.det (ratArchGL2 g) : ℝˣ) : ℝ)| *
        TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det (finFactor g : AdelicGL2 (𝓞 ℚ) ℚ))) ∧
    (∀ (v : HeightOneSpectrum (𝓞 ℚ)) (k : GL (Fin 2) (v.adicCompletion ℚ)),
      k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤ → TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det (placeEmbed ℚ v k)) = 1) ∧
    (∀ (v : HeightOneSpectrum (𝓞 ℚ)) (β : v.adicCompletion ℚ),
      TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det (placeEmbed ℚ v (repSome (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) (ϖ v)) (hπall v) β))) =
        (((Ideal.absNorm v.asIdeal : ℕ) : ℝ))⁻¹) ∧
    (∀ v : HeightOneSpectrum (𝓞 ℚ),
      TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det (placeEmbed ℚ v (repInf (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) (ϖ v)) (hπall v)))) =
        (((Ideal.absNorm v.asIdeal : ℕ) : ℝ))⁻¹) ∧
    (∀ v : HeightOneSpectrum (𝓞 ℚ),
      TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det (placeEmbed ℚ v (scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) (ϖ v)) (hπall v)))) =
        ((((Ideal.absNorm v.asIdeal : ℕ) : ℝ))⁻¹) ^ 2) ∧
    (∀ γ : GL (Fin 2) ℚ, TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det (globalPoints (𝓞 ℚ) ℚ γ)) = 1) ∧
    (∀ z : (AdeleRing (𝓞 ℚ) ℚ)ˣ, TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 ℚ) ℚ z)) = TateGlobal.ideleNorm ℚ z ^ 2) ∧
    Continuous (fun g : AdelicGL2 (𝓞 ℚ) ℚ => TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det g)) ∧
    (∀ (v : HeightOneSpectrum (𝓞 ℚ)) (m : GL (Fin 2) (v.adicCompletion ℚ)),
      Matrix.GeneralLinearGroup.det m = 1 → Matrix.GeneralLinearGroup.det (placeEmbed ℚ v m) = 1) ∧
    (∀ (v : HeightOneSpectrum (𝓞 ℚ)) (m : GL (Fin 2) (v.adicCompletion ℚ)) (g : AdelicGL2 (𝓞 ℚ) ℚ),
      ratArchGL2 (placeEmbed ℚ v m * g) = ratArchGL2 g ∧ ratArchGL2 (g * placeEmbed ℚ v m) = ratArchGL2 g) ∧
    (∀ (n : RSCarrier.finUnipotent),
      Matrix.GeneralLinearGroup.det (((n : finiteAdelicGL2Subgroup ℚ) : AdelicGL2 (𝓞 ℚ) ℚ)) = 1) := by p2m_exact_reverting @_root_.P2MW.S_NumberField_TateGlobal_ideleNorm_det_facts_rankinSelberg_rat.solution
