import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_TateLocalConstantsAt
import P2M.Util
import P2M.Sol.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_restrict_eq
attribute [-instance] instCountableOfNumberField_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions HeckePair.instSMulCommClassSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instAlgebraSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instOneSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instIsScalarTowerSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instRingSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instMulSubtypeForallMemSubmoduleHeckeAlgebra FixedPoints.instMulActionElemFixedPointsOfSMulCommClass_definitions FixedPoints.module FixedPoints.instSMulElemFixedPointsOfSMulCommClass_definitions FixedPoints.instAddCommMonoidElemFixedPoints_definitions
attribute [-simp] AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_one AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_one NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent NumberField.StandardAddChar.ratArchLine_apply NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq AutomorphicForm.whittakerCoefficient_zero NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one HeckePair.convTerm_mk HeckePair.coe_apply_add HeckePair.coe_apply_smul FixedPoints.coe_zero FixedPoints.coe_smul FixedPoints.coe_add LocalGL2.swapUnit_val
set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel
open NumberField.InfinitePlace IsDedekindDomain
open AutomorphicForm hiding bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity open AutomorphicForm.WindowedSiegel
open scoped NNReal

open scoped Classical in

theorem AutomorphicForm.bigCell_eq_sum_pureTensor_of_flat_family_of_restrict_eq
    (F : Type) [Field F] [NumberField F] :
    let α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    ∀ (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ))
      (φ₀ : AdelicGL2 (𝓞 F) F → ℂ),
      ∃ (S : Finset (HeightOneSpectrum (𝓞 F))) (n : ℕ) (c : Fin n → ℂ)
        (kdat : Fin n → {w : InfinitePlace F // w.IsReal} → ℤ)
        (abm : Fin n → {w : InfinitePlace F // w.IsComplex} → ℕ × ℕ × ℕ)
        (m : ℕ) (A B : Fin n → (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F → ℂ),
        (∀ (j : Fin n) (w : {w : InfinitePlace F // w.IsComplex}),
          (abm j w).1 + (abm j w).2.1 ≤ (abm j w).2.2) ∧
        1 ≤ m ∧
        (∀ (j : Fin n), ∀ v ∈ S, ∀ x ∈ v.adicCompletionIntegers F,
          ∀ y ∈ v.adicCompletionIntegers F,
            Valued.v (y - x) ≤ Multiplicative.ofAdd (-(m : ℤ)) → A j v y = A j v x) ∧
        (∀ (j : Fin n), ∀ v ∈ S, ∀ x y : v.adicCompletion F,
          Valued.v (y - x) ≤ Multiplicative.ofAdd (-(m : ℤ)) → B j v y = B j v x) ∧
        ∀ (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
          (φ : ℂ → AdelicGL2 (𝓞 F) F → ℂ)
          (_hφ : ∀ s, IsInducedSection (𝓞 F) F (etaFst μ α hα s) (etaSnd ν α hα s) (φ s))
          (_hφK : ∀ s, IsArchKFinite F (φ s))
          (_hφf : ∀ s, IsKfSmooth F (φ s))
          (_hφc : ∀ s, Continuous (φ s))
          (_hφ₀ : ∀ (s : ℂ) (k : AdelicGL2 (𝓞 F) F),
              glFin (𝓞 F) F k ∈ finiteIntegralGL2 (𝓞 F) F →
              (∀ w : InfinitePlace F, IsRowIsometry (archComponent F w (glArch (𝓞 F) F k))) →
              φ s k = φ₀ k)
          (_hφne : ∃ (s : ℂ) (g : AdelicGL2 (𝓞 F) F), φ s g ≠ 0),
        ∃ (Rr : {w : InfinitePlace F // w.IsReal} → ℝ → ℂ)
          (Rc : {w : InfinitePlace F // w.IsComplex} → ℝ → ℂ),
        (∀ v ∉ S, ∀ u : (v.adicCompletion F)ˣ, Valued.v (u : v.adicCompletion F) = 1 →
          NumberField.TateGlobal.localChar (μ * ν⁻¹) v u = 1) ∧
        (∀ v ∈ S, ∃ cN : ℕ, ∀ u ∈ LanglandsTunnell.TateLocal.higherUnitsAt F v cN,
          NumberField.TateGlobal.localChar (μ * ν⁻¹) v u = 1) ∧
        (∀ (i : {w : InfinitePlace F // w.IsReal}) (u : (i.1.Completion)ˣ),
          0 < Completion.extensionEmbeddingOfIsReal i.2 (u : i.1.Completion) →
          Rr i (Completion.extensionEmbeddingOfIsReal i.2 (u : i.1.Completion))
            = (((μ * ν⁻¹) (NumberField.TateGlobal.archUnitHom i.1 u) : ℂˣ) : ℂ)) ∧
        (∀ (w : {w : InfinitePlace F // w.IsComplex}) (u : (w.1.Completion)ˣ) (r : ℝ), 0 < r →
          Completion.extensionEmbedding w.1 (u : w.1.Completion) = (r : ℂ) →
          Rc w r = (((μ * ν⁻¹) (NumberField.TateGlobal.archUnitHom w.1 u) : ℂˣ) : ℂ)) ∧
        (∀ (j : Fin n) (i : {w : InfinitePlace F // w.IsReal}),
          (-1 : ℂ) ^ (kdat j i)
            = (((μ * ν⁻¹)
                  (NumberField.TateGlobal.archUnitHom i.1 (-1 : (i.1.Completion)ˣ)) : ℂˣ) : ℂ)) ∧
        (∀ (j : Fin n) (w : {w : InfinitePlace F // w.IsComplex}) (u : (w.1.Completion)ˣ),
          ‖Completion.extensionEmbedding w.1 (u : w.1.Completion)‖ = 1 →
          (((μ * ν⁻¹) (NumberField.TateGlobal.archUnitHom w.1 u) : ℂˣ) : ℂ) ≠ 1 →
          ¬ ((abm j w).1 = (abm j w).2.1 ∧ (abm j w).2.2 = 2 * (abm j w).1)) ∧
        ∀ (s : ℂ) (x : AdeleRing (𝓞 F) F),
          φ s ((adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 x)
            = ∑ j : Fin n, c j
                * (∏ i : {w : InfinitePlace F // w.IsReal},
                    Rr i ((1 + Completion.extensionEmbeddingOfIsReal i.2 (x.1 i.1) ^ 2)
                            ^ (-(1 / 2 : ℝ)))
                      * ((((Completion.extensionEmbeddingOfIsReal i.2 (x.1 i.1) : ℝ) : ℂ)
                            - Complex.I)
                          / ((Real.sqrt (1 + Completion.extensionEmbeddingOfIsReal i.2 (x.1 i.1) ^ 2)
                              : ℝ) : ℂ)) ^ (kdat j i)
                      * (((1 + Completion.extensionEmbeddingOfIsReal i.2 (x.1 i.1) ^ 2 : ℝ) : ℂ))
                          ^ (-(s + 1 / 2)))
                * (∏ w : {w : InfinitePlace F // w.IsComplex},
                    Rc w ((1 + ‖Completion.extensionEmbedding w.1 (x.1 w.1)‖ ^ 2)
                            ^ (-(1 / 2 : ℝ)))
                      * Completion.extensionEmbedding w.1 (x.1 w.1) ^ (abm j w).1
                      * (starRingEnd ℂ) (Completion.extensionEmbedding w.1 (x.1 w.1))
                          ^ (abm j w).2.1
                      * (((1 + ‖Completion.extensionEmbedding w.1 (x.1 w.1)‖ ^ 2 : ℝ) : ℂ))
                          ^ (-(2 * s + 1) - ((abm j w).2.2 : ℂ) / 2))
                * (∏ v ∈ S,
                    ((v.adicCompletionIntegers F : Set (v.adicCompletion F)).indicator (A j v) (x.2 v)
                      + (v.adicCompletionIntegers F : Set (v.adicCompletion F))ᶜ.indicator
                          (fun y => LanglandsTunnell.TateLocal.charExt
                              (NumberField.TateGlobal.localChar (μ * ν⁻¹) v)⁻¹ y
                            * ((LanglandsTunnell.TateLocal.modulus y : ℝ) : ℂ) ^ (-(2 * s + 1))
                            * B j v y⁻¹) (x.2 v)))
                * ∏ᶠ v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S},
                    ((v.1.adicCompletionIntegers F : Set (v.1.adicCompletion F)).indicator
                        (fun _ => (1 : ℂ)) (x.2 v.1)
                      + (v.1.adicCompletionIntegers F : Set (v.1.adicCompletion F))ᶜ.indicator
                          (fun y => LanglandsTunnell.TateLocal.charExt
                              (NumberField.TateGlobal.localChar (μ * ν⁻¹) v.1)⁻¹ y
                            * ((LanglandsTunnell.TateLocal.modulus y : ℝ) : ℂ) ^ (-(2 * s + 1)))
                          (x.2 v.1)) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_restrict_eq.solution
