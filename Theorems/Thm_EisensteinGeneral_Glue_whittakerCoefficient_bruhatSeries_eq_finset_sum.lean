import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_AutomorphicForm_ProductionPins
import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_NumberField_AdelicHaar
import P2M.Util
import P2M.Sol.S_EisensteinGeneral_Glue_whittakerCoefficient_bruhatSeries_eq_finset_sum
attribute [-instance] FLT.SmoothVectors.RightTranslationFn.instAddCommMonoid FLT.SmoothVectors.RightTranslationFn.instMulAction FLT.SmoothVectors.RightTranslationFn.instDistribMulAction instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete instCountableOfNumberField_definitions
attribute [-simp] AutomorphicForm.cpowChar_apply_val FLT.SmoothVectors.RightTranslationFn.toFun_smul FLT.SmoothVectors.RightTranslationFn.mk_toFun FLT.SmoothVectors.RightTranslationFn.toFun_mk FLT.SmoothVectors.mem_smoothVectors_iff LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero

open MeasureTheory NumberField NumberField.AdelicHaar IsDedekindDomain AutomorphicForm
attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
set_option autoImplicit false

theorem EisensteinGeneral.Glue.whittakerCoefficient_bruhatSeries_eq_finset_sum (F : Type) [Field F] [NumberField F]
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (hψc : Continuous ψ) (hψ : ∀ x, ‖ψ x‖ = 1) (n : ℕ) (c : Fin n → ℂ)
    (Ψ : Fin n → AdelicGL2 (𝓞 F) F → ℂ) (Φ : AdelicGL2 (𝓞 F) F → ℂ)
    (hΨ : ∀ i, ∃ χ₁ χ₂ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ, IsInducedSection (𝓞 F) F χ₁ χ₂ (Ψ i))
    (hΦ : ∀ g', Φ g' = ∑ i : Fin n, c i * Ψ i g') (ξ : F) (g : AdelicGL2 (𝓞 F) F)
    (hint : ∀ i, Integrable (fun y => Ψ i (adelicWeyl (𝓞 F) F * unipotentGL2 y * g)) (adelicAddHaar (𝓞 F) F)) :
    whittakerCoefficient F (productionPins F) ψ
        (fun g' => Φ g' + ∑' ξ' : F, Φ (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ') * g'))
        ξ g
      = ∑ i : Fin n, c i * whittakerCoefficient F (productionPins F) ψ
          (fun g' => Ψ i g' + ∑' ξ' : F,
            Ψ i (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ') * g')) ξ g := by p2m_exact_reverting @_root_.P2MW.S_EisensteinGeneral_Glue_whittakerCoefficient_bruhatSeries_eq_finset_sum.solution
