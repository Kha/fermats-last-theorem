import Definitions.Def_LanglandsTunnell_CubicInduction_GodementSection
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_AutomorphicForm_ArchDerivCasimir
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_RankinSelberg_map_bigCellWeyl_withDensity_eq_pi_selfDualHaarAt
attribute [-instance] instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory AutomorphicForm LanglandsTunnell.TateLocal LanglandsTunnell.CubicInduction
open scoped ENNReal

theorem LanglandsTunnell.RankinSelberg.map_bigCellWeyl_withDensity_eq_pi_selfDualHaarAt
    (p : HeightOneSpectrum (𝓞 ℚ)) :
    letI : MeasurableSpace (p.adicCompletion ℚ) := localBorel ℚ p
    MeasureTheory.Measure.map (β := Fin 2 → Fin 2 → p.adicCompletion ℚ)
        (fun q : (p.adicCompletion ℚ)ˣ × p.adicCompletion ℚ × (p.adicCompletion ℚ)ˣ × p.adicCompletion ℚ =>
          !![(q.1 : p.adicCompletion ℚ) * q.2.1, (q.1 : p.adicCompletion ℚ) * (q.2.1 * q.2.2.2 + (q.2.2.1 : p.adicCompletion ℚ));
             -(q.1 : p.adicCompletion ℚ), -((q.1 : p.adicCompletion ℚ) * q.2.2.2)])
        (((MeasureTheory.Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))).prod
            ((selfDualHaarAt ℚ p).prod
              ((MeasureTheory.Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))).prod (selfDualHaarAt ℚ p)))).withDensity
          fun q => (modulus (q.1 : p.adicCompletion ℚ) : ℝ≥0∞) ^ 4 * (modulus (q.2.2.1 : p.adicCompletion ℚ) : ℝ≥0∞)) =
      (MeasureTheory.Measure.pi fun _ : Fin 2 => MeasureTheory.Measure.pi fun _ : Fin 2 => selfDualHaarAt ℚ p) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_RankinSelberg_map_bigCellWeyl_withDensity_eq_pi_selfDualHaarAt.solution
