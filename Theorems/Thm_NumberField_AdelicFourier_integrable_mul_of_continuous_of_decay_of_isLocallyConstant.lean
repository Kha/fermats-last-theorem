import Definitions.Def_NumberField_AdelicFourier
import P2M.Util
import P2M.Sol.S_NumberField_AdelicFourier_integrable_mul_of_continuous_of_decay_of_isLocallyConstant
attribute [-instance] NumberField.AdelicHaar.locallyCompactSpace_adeleRing NumberField.AdelicHaar.finite_residueField_adicCompletionIntegers NumberField.AdelicHaar.locallyCompactSpace_gl_adeleRing NumberField.AdelicHaar.locallyCompactSpace_finiteAdeleRing NumberField.AdelicHaar.compactSpace_adicCompletionIntegers NumberField.AdelicHaar.t2Space_finiteAdeleRing NumberField.AdelicHaar.t2Space_matrix_adeleRing NumberField.AdelicHaar.t2Space_adeleRing NumberField.AdelicHaar.fact_isOpen_adicCompletionIntegers NumberField.AdelicHaar.t2Space_gl_adeleRing NumberField.AdelicHaar.locallyCompactSpace_matrix_adeleRing NumberField.AdelicHaar.t2Space_infiniteAdeleRing NumberField.AdelicHaar.properSpace_adicCompletion

set_option autoImplicit false

open NumberField IsDedekindDomain MeasureTheory
open scoped Classical

theorem NumberField.AdelicFourier.integrable_mul_of_continuous_of_decay_of_isLocallyConstant
    (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (AdeleRing (𝓞 F) F)] [BorelSpace (AdeleRing (𝓞 F) F)]
    (μ : Measure (AdeleRing (𝓞 F) F)) [μ.IsAddHaarMeasure]
    (G : mixedEmbedding.mixedSpace F → ℂ) (hG : Continuous G)
    (k : ℕ) (hk : Module.finrank ℝ (mixedEmbedding.mixedSpace F) < k)
    (C : ℝ) (hdecay : ∀ y : mixedEmbedding.mixedSpace F, (1 + ‖y‖) ^ k * ‖G y‖ ≤ C)
    (H : FiniteAdeleRing (𝓞 F) F → ℂ) (hH : IsLocallyConstant H) (hHc : HasCompactSupport H) :
    Integrable (fun x : AdeleRing (𝓞 F) F => G (InfiniteAdeleRing.ringEquiv_mixedSpace F x.1) * H x.2) μ := by p2m_exact_reverting @_root_.P2MW.S_NumberField_AdelicFourier_integrable_mul_of_continuous_of_decay_of_isLocallyConstant.solution
