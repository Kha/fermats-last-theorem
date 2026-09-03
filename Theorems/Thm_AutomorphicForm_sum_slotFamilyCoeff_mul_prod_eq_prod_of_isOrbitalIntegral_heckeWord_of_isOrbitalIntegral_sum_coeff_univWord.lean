import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_SatakeCombinationCoeff
import Definitions.Def_LocalLanglands_HeckeCosetSystem
import P2M.Util
import P2M.Sol.S_AutomorphicForm_sum_slotFamilyCoeff_mul_prod_eq_prod_of_isOrbitalIntegral_heckeWord_of_isOrbitalIntegral_sum_coeff_univWord
attribute [-instance] LanglandsTunnell.CubicInduction.countable_GL2 LanglandsTunnell.CubicInduction.countable_mirabolicIndex
attribute [-simp] UnramifiedWhittaker.ProductMeasureData.mk.injEq UnramifiedWhittaker.ProductMeasureData.mk.sizeOf_spec AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed AutomorphicForm.rightTranslationEmbed_smul_apply NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one LocalGL2.swapUnit_val AutomorphicForm.WindingDatum.mk.injEq AutomorphicForm.WindingDatum.mk.sizeOf_spec LanglandsTunnell.CubicInduction.coe_diagUnits2 NumberField.StandardAddChar.ratArchLine_apply NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq AutomorphicForm.whittakerCoefficient_zero NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply LanglandsTunnell.TateLocal.conductorExponentAt_one LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero LanglandsTunnell.signEpsilon_one LanglandsTunnell.RealArchParam.epsilonFactor_principal LanglandsTunnell.RealArchParam.epsilonFactor_discrete LanglandsTunnell.signEpsilon_zero LanglandsTunnell.signShift_zero
attribute [-simp] LanglandsTunnell.RealArchParam.twist_zero LanglandsTunnell.RealArchParam.discrete.sizeOf_spec LanglandsTunnell.RealArchParam.principal.injEq LanglandsTunnell.ComplexArchParam.dual_dual LanglandsTunnell.ComplexArchParam.mk.sizeOf_spec LanglandsTunnell.RealArchParam.dual_dual LanglandsTunnell.RealArchParam.discrete.injEq LanglandsTunnell.ComplexArchParam.twist_zero LanglandsTunnell.RealArchParam.principal.sizeOf_spec LanglandsTunnell.signShift_one LanglandsTunnell.ComplexArchParam.mk.injEq LanglandsTunnell.LDatum.mk.sizeOf_spec LanglandsTunnell.LDatum.badFactor_zero LanglandsTunnell.LDatum.mk.injEq LanglandsTunnell.RankinSelberg.mem_primeFibre LanglandsTunnell.CubicInduction.coe_diagUnitGL2 LanglandsTunnell.CubicInduction.iotaTorusLocal_zero LanglandsTunnell.CubicInduction.upperUnipotent3_zero LanglandsTunnell.CubicInduction.radicalP21_coe LanglandsTunnell.CubicInduction.coe_iotaGL LanglandsTunnell.CubicInduction.radicalP12_coe LanglandsTunnell.CubicInduction.radicalP12_zero LanglandsTunnell.CubicInduction.radicalP21_zero LanglandsTunnell.CubicInduction.upperUnipotent3_coe

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open scoped TensorProduct

theorem AutomorphicForm.sum_slotFamilyCoeff_mul_prod_eq_prod_of_isOrbitalIntegral_heckeWord_of_isOrbitalIntegral_sum_coeff_univWord
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (ws : ∀ v : HeightOneSpectrum (𝓞 K), v.Extension (𝓞 L))
    (T : Finset (HeightOneSpectrum (𝓞 K)))
    (nKs : HeightOneSpectrum (𝓞 K) → ℕ)
    (rKs : ∀ v : HeightOneSpectrum (𝓞 K), Fin (nKs v) → GL (Fin 2) (v.adicCompletion K))
    (zKs : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (v.adicCompletion K))
    (ks js : HeightOneSpectrum (𝓞 K) → ℕ)
    (γ : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (v.adicCompletion K))
    (hγ : ∀ v ∈ T, AutomorphicForm.IsRegularSemisimple (γ v))
    (τ : ∀ v : HeightOneSpectrum (𝓞 K),
      @Measure (AutomorphicForm.localCentralizer K v (γ v)) (AutomorphicForm.localCentralizerBorel K v (γ v)))
    (hτ : ∀ v ∈ T, @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.localCentralizerBorel K v (γ v)) (τ v))
    (hτ1 : ∀ v ∈ T, τ v (Subtype.val ⁻¹' AutomorphicForm.localIntegralSet K v) = 1)
    (IW : ((u : HeightOneSpectrum (𝓞 K)) → u ∈ T → (Fin 2 →₀ ℕ)) → HeightOneSpectrum (𝓞 K) → ℂ)
    (hIW : ∀ m ∈ AutomorphicForm.SatakeCombination.slotIndex K L ws ks js T,
      ∀ (v : HeightOneSpectrum (𝓞 K)) (hv : v ∈ T),
        AutomorphicForm.IsOrbitalIntegral K v (γ v) (τ v) (fun x : GL (Fin 2) (v.adicCompletion K) =>
            ∑ ι : Fin ((m v hv) 0) → Fin (nKs v),
              (AutomorphicForm.localIntegralSet K v).indicator (fun _ => (1 : ℂ))
                (((List.ofFn fun m => rKs v (ι m)).prod * zKs v ^ (m v hv) 1)⁻¹ * x)) (IW m v))
    (IT : HeightOneSpectrum (𝓞 K) → ℂ)
    (hIT : ∀ v ∈ T, AutomorphicForm.IsOrbitalIntegral K v (γ v) (τ v) (fun x : GL (Fin 2) (v.adicCompletion K) =>
        ∑ r ∈ (AutomorphicForm.SatakeCombination.univWord (v.asIdeal.inertiaDeg' (ws v).1.asIdeal - 1) (ks v) (js v)).support,
          (AutomorphicForm.SatakeCombination.univWord (v.asIdeal.inertiaDeg' (ws v).1.asIdeal - 1) (ks v) (js v)).coeff r *
              (Ideal.absNorm v.asIdeal : ℂ) ^ (r 1) / (Ideal.absNorm (ws v).1.asIdeal : ℂ) ^ (js v) *
            ∑ ι : Fin (r 0) → Fin (nKs v),
              (AutomorphicForm.localIntegralSet K v).indicator (fun _ => (1 : ℂ))
                (((List.ofFn fun m => rKs v (ι m)).prod * zKs v ^ (r 1))⁻¹ * x)) (IT v)) :
    ∑ m ∈ AutomorphicForm.SatakeCombination.slotIndex K L ws ks js T,
        AutomorphicForm.SatakeCombination.slotFamilyCoeff K L ws ks js T m * ∏ v ∈ T, IW m v =
      ∏ v ∈ T, IT v := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_sum_slotFamilyCoeff_mul_prod_eq_prod_of_isOrbitalIntegral_heckeWord_of_isOrbitalIntegral_sum_coeff_univWord.solution
