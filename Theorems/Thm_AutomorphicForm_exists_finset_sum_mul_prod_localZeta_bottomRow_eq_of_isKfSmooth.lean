import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_AutomorphicForm_BorelSubgroup
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_TateLocalZeta
import P2M.Util
import P2M.Sol.S_AutomorphicForm_exists_finset_sum_mul_prod_localZeta_bottomRow_eq_of_isKfSmooth
attribute [-instance] instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions
attribute [-simp] LanglandsTunnell.TateLocal.conductorExponentAt_one NumberField.StandardAddChar.ratArchLine_apply NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq AutomorphicForm.whittakerCoefficient_zero NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.TateGlobal
open AutomorphicForm AutomorphicForm.WindowedSiegel IsDedekindDomain
open scoped NNReal

theorem AutomorphicForm.exists_finset_sum_mul_prod_localZeta_bottomRow_eq_of_isKfSmooth
    (F : Type) [Field F] [NumberField F]
    [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletion F)]
    [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletion F)]
    (μf : (v : HeightOneSpectrum (𝓞 F)) → Measure (v.adicCompletion F)) [∀ v, (μf v).IsAddHaarMeasure]
    (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
    (_hμc : Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((μ x : ℂˣ) : ℂ))
    (_hνc : Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((ν x : ℂˣ) : ℂ))
    (n : ℕ) (U : Fin n → AdelicGL2 (𝓞 F) F → ℂ)
    (_hUf : ∀ i, IsKfSmooth F (U i))
    (_hUB : ∀ (i : Fin n) (b : AdelicGL2 (𝓞 F) F) (hb : b ∈ adelicBorel (𝓞 F) F),
        glArch (𝓞 F) F b = 1 → glFin (𝓞 F) F b ∈ finiteIntegralGL2 (𝓞 F) F →
        ∀ g : AdelicGL2 (𝓞 F) F,
          U i (b * g) = ((μ (borelDiagFst (⟨b, hb⟩ : ↥(adelicBorel (𝓞 F) F))) : ℂˣ) : ℂ)
            * ((ν (borelDiagSnd (⟨b, hb⟩ : ↥(adelicBorel (𝓞 F) F))) : ℂˣ) : ℂ) * U i g) :
    ∃ (S : Finset (HeightOneSpectrum (𝓞 F))),
      (∀ v ∉ S, IsUnramifiedCharAt μ v ∧ IsUnramifiedCharAt ν v) ∧
      ∃ (m : Fin n → ℕ)
        (h : (i : Fin n) → Fin (m i) → (Fin 2 → FiniteAdeleRing (𝓞 F) F) → ℂ)
        (Φf : (i : Fin n) → Fin (m i) → (v : HeightOneSpectrum (𝓞 F)) → (Fin 2 → v.adicCompletion F) → ℂ),
        (∀ i j, IsLocallyConstant (h i j)) ∧
        (∀ i j, HasCompactSupport (h i j)) ∧
        (∀ i j (y : Fin 2 → FiniteAdeleRing (𝓞 F) F),
          (∃ v ∉ S, ∃ l, y l v ∉ v.adicCompletionIntegers F) → h i j y = 0) ∧
        (∀ i j (y : Fin 2 → FiniteAdeleRing (𝓞 F) F),
          (∀ v ∉ S, ∀ l, y l v ∈ v.adicCompletionIntegers F) →
            h i j y = ∏ v ∈ S, Φf i j v (fun l => y l v)) ∧
        ∀ (i : Fin n) (z : ℂ) (k : AdelicGL2 (𝓞 F) F),
          k ∈ adelicMaximalCompact F → glArch (𝓞 F) F k = 1 →
            (∑ j, ((μ (Matrix.GeneralLinearGroup.det k) : ℂˣ) : ℂ)
                * ∏ v ∈ S, LanglandsTunnell.TateLocal.localZeta (μf v)
                    (fun t => Φf i j v (fun l => t
                      * (finComponent (𝓞 F) F v (glFin (𝓞 F) F k) :
                          Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 l))
                    (localChar (μ * ν⁻¹) v) z)
              = U i k := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_exists_finset_sum_mul_prod_localZeta_bottomRow_eq_of_isKfSmooth.solution
