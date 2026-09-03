import Mathlib
import P2M.Util
import P2M.Sol.S_Ideal_height_eq_one_of_isDiscreteValuationRing_localization_atPrime

theorem Ideal.height_eq_one_of_isDiscreteValuationRing_localization_atPrime
    {R : Type*} [CommRing R] [IsDomain R] (p : Ideal R) [p.IsPrime]
    (h : IsDiscreteValuationRing (Localization.AtPrime p)) : p.height = 1 := by p2m_exact_reverting @_root_.P2MW.S_Ideal_height_eq_one_of_isDiscreteValuationRing_localization_atPrime.solution
