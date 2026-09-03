import Definitions.Def_NumberField_AdelicBox
import P2M.Util
import P2M.Sol.S_NumberField_AdelicBox_setIntegral_adelicBox_tsum_add_algebraMap
attribute [-instance] instCountableOfNumberField_definitions

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicBox IsDedekindDomain
theorem NumberField.AdelicBox.setIntegral_adelicBox_tsum_add_algebraMap (F : Type) [Field F]
    [NumberField F] (Φ : AdeleRing (𝓞 F) F → ℂ) (hΦ : Integrable Φ (adelicAddHaar (𝓞 F) F)) :
    ∫ t in adelicBox F, (∑' ξ : F, Φ (t + algebraMap F (AdeleRing (𝓞 F) F) ξ))
        ∂(adelicAddHaar (𝓞 F) F)
      = ∫ t, Φ t ∂(adelicAddHaar (𝓞 F) F) := by p2m_exact_reverting @_root_.P2MW.S_NumberField_AdelicBox_setIntegral_adelicBox_tsum_add_algebraMap.solution
