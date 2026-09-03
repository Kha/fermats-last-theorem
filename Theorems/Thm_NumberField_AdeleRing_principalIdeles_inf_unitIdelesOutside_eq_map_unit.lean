import Mathlib
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_IsDedekindDomain_FiniteUnitIdelesOutside
import P2M.Util
import P2M.Sol.S_NumberField_AdeleRing_principalIdeles_inf_unitIdelesOutside_eq_map_unit

set_option autoImplicit false
theorem NumberField.AdeleRing.principalIdeles_inf_unitIdelesOutside_eq_map_unit
    (R : Type*) [CommRing R] [IsDedekindDomain R] (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]
    (S : Set (IsDedekindDomain.HeightOneSpectrum R)) :
    M4aHerbrand.principalIdeles R K ⊓ NumberField.AdeleRing.unitIdelesOutside R K S
      = (S.unit K).map (Units.map (algebraMap K (NumberField.AdeleRing R K) :
          K →* NumberField.AdeleRing R K)) := by p2m_exact_reverting @_root_.P2MW.S_NumberField_AdeleRing_principalIdeles_inf_unitIdelesOutside_eq_map_unit.solution
