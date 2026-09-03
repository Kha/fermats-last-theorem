import Definitions.Def_AutomorphicForm_GodementSection
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_LanglandsTunnell_TateLocalZeta
import P2M.Util
import P2M.Sol.S_AutomorphicForm_exists_pos_godementSection_mul_tprod_eq_mul_prod_localZeta_of_mem_adelicMaximalCompact
attribute [-instance] instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions
attribute [-simp] AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_one AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_one

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicFourier NumberField.AdelicLevel NumberField.TateGlobal
open AutomorphicForm AutomorphicForm.WindowedSiegel IsDedekindDomain
open scoped NNReal

theorem AutomorphicForm.exists_pos_godementSection_mul_tprod_eq_mul_prod_localZeta_of_mem_adelicMaximalCompact
    (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (AdeleRing (𝓞 F) F)ˣ] [BorelSpace (AdeleRing (𝓞 F) F)ˣ]
    (ν₀ : Measure (AdeleRing (𝓞 F) F)ˣ) [ν₀.IsHaarMeasure]
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletion F)]
    [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletion F)]
    (μf : (v : HeightOneSpectrum (𝓞 F)) → Measure (v.adicCompletion F)) [∀ v, (μf v).IsAddHaarMeasure]
    [∀ w : InfinitePlace F, MeasurableSpace w.Completion] [∀ w : InfinitePlace F, BorelSpace w.Completion]
    (μa : (w : InfinitePlace F) → Measure w.Completion) [∀ w, (μa w).IsAddHaarMeasure]
    (ϖ : (v : HeightOneSpectrum (𝓞 F)) → (v.adicCompletion F)ˣ)
    (_hϖ : ∀ v, Valued.v (ϖ v : v.adicCompletion F) = Multiplicative.ofAdd (-1 : ℤ)) :
    let α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    ∀ (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ)),
    ∃ c : ℝ, 0 < c ∧
      ∀ (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
        (_hμ : IsUnitaryChar (𝓞 F) F μ) (_hν : IsUnitaryChar (𝓞 F) F ν)
        (_hμc : Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((μ x : ℂˣ) : ℂ))
        (_hνc : Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((ν x : ℂˣ) : ℂ))
        (_hS : ∀ v ∉ S, IsUnramifiedCharAt (μ * ν⁻¹) v)
        (s : ℂ) (_hs : 0 < s.re),
        Multipliable (fun v : {v // v ∉ S} =>
            1 - ((localChar (μ * ν⁻¹) v.1 (ϖ v.1) : ℂˣ) : ℂ)
              * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(2 * s + 1))) ∧
        (∏' v : {v // v ∉ S},
            (1 - ((localChar (μ * ν⁻¹) v.1 (ϖ v.1) : ℂˣ) : ℂ)
              * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(2 * s + 1)))) ≠ 0 ∧
        ∀ (Φ : (Fin 2 → AdeleRing (𝓞 F) F) → ℂ)
          (Φa : (w : InfinitePlace F) → (Fin 2 → w.Completion) → ℂ)
          (Φf : (v : HeightOneSpectrum (𝓞 F)) → (Fin 2 → v.adicCompletion F) → ℂ)
          (_hΦ0 : ∀ x : Fin 2 → AdeleRing (𝓞 F) F,
            (∃ v ∉ S, ∃ i, (x i).2 v ∉ v.adicCompletionIntegers F) → Φ x = 0)
          (_hΦ1 : ∀ x : Fin 2 → AdeleRing (𝓞 F) F,
            (∀ v ∉ S, ∀ i, (x i).2 v ∈ v.adicCompletionIntegers F) →
              Φ x = (∏ w, Φa w (fun i => (x i).1 w)) * ∏ v ∈ S, Φf v (fun i => (x i).2 v))
          (k : AdelicGL2 (𝓞 F) F) (_hk : k ∈ adelicMaximalCompact F),
          godementSection F ν₀ μ ν α hα Φ s k
              * ∏' v : {v // v ∉ S},
                  (1 - ((localChar (μ * ν⁻¹) v.1 (ϖ v.1) : ℂˣ) : ℂ)
                    * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(2 * s + 1)))
            = c * ((μ (Matrix.GeneralLinearGroup.det k) : ℂˣ) : ℂ)
                * (∏ w, LanglandsTunnell.TateLocal.localZeta (μa w)
                    (fun t => Φa w (fun i => t
                      * (archComponent F w (glArch (𝓞 F) F k) : Matrix (Fin 2) (Fin 2) w.Completion) 1 i))
                    (archLocalChar (μ * ν⁻¹) w) (2 * s + 1))
                * ∏ v ∈ S, LanglandsTunnell.TateLocal.localZeta (μf v)
                    (fun t => Φf v (fun i => t
                      * (finComponent (𝓞 F) F v (glFin (𝓞 F) F k) :
                          Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 i))
                    (localChar (μ * ν⁻¹) v) (2 * s + 1) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_exists_pos_godementSection_mul_tprod_eq_mul_prod_localZeta_of_mem_adelicMaximalCompact.solution
