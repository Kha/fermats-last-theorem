import Definitions.Def_NumberField_AdelicFourier
import Definitions.Def_NumberField_AdelicBox
import P2M.Util
import P2M.Sol.S_NumberField_AdelicFourier_integrableOn_tsum_translate_adelicBox_of_mem_pureTensorSet
attribute [-instance] instCountableOfNumberField_definitions

open NumberField NumberField.AdelicFourier NumberField.AdelicBox NumberField.AdelicHaar

theorem NumberField.AdelicFourier.integrableOn_tsum_translate_adelicBox_of_mem_pureTensorSet (F : Type) [Field F] [NumberField F]
    {Φ : AdeleRing (𝓞 F) F → ℂ} (hΦ : Φ ∈ pureTensorSet F) :
    MeasureTheory.IntegrableOn (fun t => ∑' ξ : F, Φ (t + algebraMap F (AdeleRing (𝓞 F) F) ξ))
      (adelicBox F) (adelicAddHaar (𝓞 F) F) := by p2m_exact_reverting @_root_.P2MW.S_NumberField_AdelicFourier_integrableOn_tsum_translate_adelicBox_of_mem_pureTensorSet.solution
