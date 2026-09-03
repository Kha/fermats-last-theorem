import Mathlib
import P2M.Util
import P2M.Sol.S_Ideal_mapCotangent_bijective_of_isLocalization_atPrime_of_isMaximal

set_option autoImplicit false

open IsLocalRing

universe u
theorem Ideal.mapCotangent_bijective_of_isLocalization_atPrime_of_isMaximal
    {A : Type u} [CommRing A] (𝔪 : Ideal A) [𝔪.IsMaximal]
    (B : Type u) [CommRing B] [IsLocalRing B] [Algebra A B] [IsLocalization.AtPrime B 𝔪]
    (h : 𝔪 ≤ (maximalIdeal B).comap (Algebra.ofId A B)) :
    Function.Bijective (Ideal.mapCotangent 𝔪 (maximalIdeal B) (Algebra.ofId A B) h) := by p2m_exact_reverting @_root_.P2MW.S_Ideal_mapCotangent_bijective_of_isLocalization_atPrime_of_isMaximal.solution
