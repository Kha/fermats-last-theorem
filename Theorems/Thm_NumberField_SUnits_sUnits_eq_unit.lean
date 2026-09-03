import Mathlib
import Definitions.Def_NumberField_PlaceAbove
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_NumberField_SUnitsModule
import P2M.Util
import P2M.Sol.S_NumberField_SUnits_sUnits_eq_unit

set_option autoImplicit false
theorem NumberField.SUnits.sUnits_eq_unit (E K : Type) [Field E] [Field K] [NumberField K] [Algebra E K]
    (S : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E))) :
    NumberField.SUnits.sUnits E K S = Set.unit (NumberField.SUnits.placesAbove E K S) K := by p2m_exact_reverting @_root_.P2MW.S_NumberField_SUnits_sUnits_eq_unit.solution
