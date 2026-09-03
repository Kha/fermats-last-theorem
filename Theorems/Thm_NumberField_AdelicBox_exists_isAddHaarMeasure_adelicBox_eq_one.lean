import Definitions.Def_NumberField_AdelicBox
import P2M.Util
import P2M.Sol.S_NumberField_AdelicBox_exists_isAddHaarMeasure_adelicBox_eq_one

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain

theorem NumberField.AdelicBox.exists_isAddHaarMeasure_adelicBox_eq_one (K : Type) [Field K] [NumberField K]
    [MeasurableSpace (AdeleRing (𝓞 K) K)] [BorelSpace (AdeleRing (𝓞 K) K)] :
    ∃ μK : Measure (AdeleRing (𝓞 K) K), μK.IsAddHaarMeasure ∧ μK (NumberField.AdelicBox.adelicBox K) = 1 := by p2m_exact_reverting @_root_.P2MW.S_NumberField_AdelicBox_exists_isAddHaarMeasure_adelicBox_eq_one.solution
