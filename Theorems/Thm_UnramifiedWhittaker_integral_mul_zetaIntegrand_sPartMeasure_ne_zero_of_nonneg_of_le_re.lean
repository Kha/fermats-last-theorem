import Definitions.Def_AutomorphicForm_RightConvolution
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_BoundedGenuineCuspRealization
import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_NumberField_AdelicFourier
import P2M.Util
import P2M.Sol.S_UnramifiedWhittaker_integral_mul_zetaIntegrand_sPartMeasure_ne_zero_of_nonneg_of_le_re

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar MeasureTheory
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain NumberField.TateGlobal
open UnramifiedWhittaker

theorem UnramifiedWhittaker.integral_mul_zetaIntegrand_sPartMeasure_ne_zero_of_nonneg_of_le_re
    (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (Wg : AdelicGL2 (𝓞 F) F → ℂ) (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (s₁ : ℂ)
    (μ : (AdeleRing (𝓞 F) F)ˣ → ℝ) (hμ0 : ∀ a, 0 ≤ μ a)
    (hint : Integrable (fun a => (μ a : ℂ) * zetaIntegrand Wg χ s₁ a) (NumberField.Idele.sPartMeasure F S))
    (hintμ : Integrable μ (NumberField.Idele.sPartMeasure F S))
    (Ω N : Set (AdeleRing (𝓞 F) F)ˣ) (hΩm : MeasurableSet[NumberField.Idele.ideleBorel F] Ω) (hΩ : NumberField.Idele.sPartMeasure F S Ωᶜ = 0)
    (a₀ : (AdeleRing (𝓞 F) F)ˣ) (hZ₀ : zetaIntegrand Wg χ s₁ a₀ ≠ 0)
    (hN : ∀ a ∈ Ω, a ∈ N →
      ‖zetaIntegrand Wg χ s₁ a₀‖ ^ 2 / 2 ≤ (zetaIntegrand Wg χ s₁ a * star (zetaIntegrand Wg χ s₁ a₀)).re)
    (hsupp : ∀ a ∈ Ω, a ∉ N → μ a = 0)
    (hpos : 0 < ∫ a, μ a ∂(NumberField.Idele.sPartMeasure F S)) :
    (∫ a, (μ a : ℂ) * zetaIntegrand Wg χ s₁ a ∂(NumberField.Idele.sPartMeasure F S)) ≠ 0 := by p2m_exact_reverting @_root_.P2MW.S_UnramifiedWhittaker_integral_mul_zetaIntegrand_sPartMeasure_ne_zero_of_nonneg_of_le_re.solution
