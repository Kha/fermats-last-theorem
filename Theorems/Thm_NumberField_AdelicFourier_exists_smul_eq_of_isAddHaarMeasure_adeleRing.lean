import Definitions.Def_NumberField_AdelicHaar
import P2M.Util
import P2M.Sol.S_NumberField_AdelicFourier_exists_smul_eq_of_isAddHaarMeasure_adeleRing
attribute [-instance] instCountableOfNumberField_definitions

open NumberField
theorem NumberField.AdelicFourier.exists_smul_eq_of_isAddHaarMeasure_adeleRing (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (AdeleRing (𝓞 F) F)] [BorelSpace (AdeleRing (𝓞 F) F)]
    (μ ν : MeasureTheory.Measure (AdeleRing (𝓞 F) F)) [μ.IsAddHaarMeasure] [ν.IsAddHaarMeasure] :
    ∃ c : NNReal, 0 < c ∧ μ = c • ν := by p2m_exact_reverting @_root_.P2MW.S_NumberField_AdelicFourier_exists_smul_eq_of_isAddHaarMeasure_adeleRing.solution
