import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_LanglandsTunnell_CubicInduction_GlobalZeta31
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_AdelicDock_LocalEmbedding
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_RankinSelberg_mul_eq_mul_one_and_ideleNorm_det_eq_finprod_of_mem_cut_of_blind
attribute [-instance] instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions
attribute [-simp] AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_one AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_one
set_option autoImplicit false
open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.RankinSelberg MeasureTheory
attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

theorem LanglandsTunnell.RankinSelberg.mul_eq_mul_one_and_ideleNorm_det_eq_finprod_of_mem_cut_of_blind
    (SQ : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (W' F' : AdelicGL2 (𝓞 ℚ) ℚ → ℂ)
    (hblind : ∀ v ∈ SQ, ∀ (x : GL (Fin 2) (v.adicCompletion ℚ)) (g : AdelicGL2 (𝓞 ℚ) ℚ),
      W' (g * UnramifiedWhittaker.placeEmbed ℚ v x) = W' g ∧ F' (g * UnramifiedWhittaker.placeEmbed ℚ v x) = F' g)
    (hN : ∀ (n : RSCarrier.finUnipotent) (g : finiteAdelicGL2Subgroup ℚ),
      W' ((((n : finiteAdelicGL2Subgroup ℚ) * g : finiteAdelicGL2Subgroup ℚ)) : AdelicGL2 (𝓞 ℚ) ℚ) *
          F' ((((n : finiteAdelicGL2Subgroup ℚ) * g : finiteAdelicGL2Subgroup ℚ)) : AdelicGL2 (𝓞 ℚ) ℚ) =
        W' (g : AdelicGL2 (𝓞 ℚ) ℚ) * F' (g : AdelicGL2 (𝓞 ℚ) ℚ))
    (hK : ∀ k : finiteAdelicGL2Subgroup ℚ,
      (∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ SQ →
        localAt ℚ v (k : AdelicGL2 (𝓞 ℚ) ℚ) ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤) →
      (∀ v ∈ SQ, localAt ℚ v (k : AdelicGL2 (𝓞 ℚ) ℚ) = 1) →
      ∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
        W' (g * (k : AdelicGL2 (𝓞 ℚ) ℚ)) = W' g ∧ F' (g * (k : AdelicGL2 (𝓞 ℚ) ℚ)) = F' g)
    (g : finiteAdelicGL2Subgroup ℚ)
    (hg : ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ SQ →
      ∃ n ∈ (AutomorphicForm.unipotentGL2Hom (R := v.adicCompletion ℚ)).range,
        ∃ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤, localAt ℚ v (g : AdelicGL2 (𝓞 ℚ) ℚ) = n * k) :
    W' (g : AdelicGL2 (𝓞 ℚ) ℚ) * F' (g : AdelicGL2 (𝓞 ℚ) ℚ) = W' 1 * F' 1 ∧
      (NumberField.TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det (g : AdelicGL2 (𝓞 ℚ) ℚ)) : ℝ) =
        ∏ v ∈ SQ, (LanglandsTunnell.TateLocal.modulus
          ((Matrix.GeneralLinearGroup.det (localAt ℚ v (g : AdelicGL2 (𝓞 ℚ) ℚ)) : (v.adicCompletion ℚ)ˣ) :
            v.adicCompletion ℚ) : ℝ) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_RankinSelberg_mul_eq_mul_one_and_ideleNorm_det_eq_finprod_of_mem_cut_of_blind.solution
