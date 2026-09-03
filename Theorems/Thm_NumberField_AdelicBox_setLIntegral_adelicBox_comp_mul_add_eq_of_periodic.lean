import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_NumberField_AdelicBox
import P2M.Util
import P2M.Sol.S_NumberField_AdelicBox_setLIntegral_adelicBox_comp_mul_add_eq_of_periodic

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicBox NumberField.AdelicLevel AutomorphicForm
open scoped ENNReal

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel

theorem NumberField.AdelicBox.setLIntegral_adelicBox_comp_mul_add_eq_of_periodic
    (F : Type) [Field F] [NumberField F]
    (h : AdeleRing (𝓞 F) F → ℝ≥0∞) (hh : Measurable h)
    (hper : ∀ (β : F) (u : AdeleRing (𝓞 F) F), h (algebraMap F (AdeleRing (𝓞 F) F) β + u) = h u)
    (a : Fˣ) (u₀ : AdeleRing (𝓞 F) F) :
    ∫⁻ u in adelicBox F, h (algebraMap F (AdeleRing (𝓞 F) F) a * u + u₀) ∂(adelicAddHaar (𝓞 F) F) =
      ∫⁻ u in adelicBox F, h u ∂(adelicAddHaar (𝓞 F) F) := by p2m_exact_reverting @_root_.P2MW.S_NumberField_AdelicBox_setLIntegral_adelicBox_comp_mul_add_eq_of_periodic.solution
