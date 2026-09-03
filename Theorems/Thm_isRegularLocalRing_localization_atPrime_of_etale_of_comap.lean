import Mathlib
import P2M.Util
import P2M.Sol.S_isRegularLocalRing_localization_atPrime_of_etale_of_comap

set_option autoImplicit false

theorem isRegularLocalRing_localization_atPrime_of_etale_of_comap
    (A B : Type*) [CommRing A] [CommRing B] [Algebra A B] [Algebra.Etale A B]
    (q : Ideal B) [q.IsPrime]
    (hreg : IsRegularLocalRing (Localization.AtPrime (q.comap (algebraMap A B)))) :
    IsRegularLocalRing (Localization.AtPrime q) := by p2m_exact_reverting @_root_.P2MW.S_isRegularLocalRing_localization_atPrime_of_etale_of_comap.solution
