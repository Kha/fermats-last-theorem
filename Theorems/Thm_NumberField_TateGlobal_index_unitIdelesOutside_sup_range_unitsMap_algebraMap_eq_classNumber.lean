import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_IsDedekindDomain_FiniteUnitIdelesOutside
import P2M.Util
import P2M.Sol.S_NumberField_TateGlobal_index_unitIdelesOutside_sup_range_unitsMap_algebraMap_eq_classNumber

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain

theorem NumberField.TateGlobal.index_unitIdelesOutside_sup_range_unitsMap_algebraMap_eq_classNumber
    (K : Type) [Field K] [NumberField K] :
    (NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K (∅ : Set (HeightOneSpectrum (𝓞 K))) ⊔
      (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range).index =
      NumberField.classNumber K := by p2m_exact_reverting @_root_.P2MW.S_NumberField_TateGlobal_index_unitIdelesOutside_sup_range_unitsMap_algebraMap_eq_classNumber.solution
