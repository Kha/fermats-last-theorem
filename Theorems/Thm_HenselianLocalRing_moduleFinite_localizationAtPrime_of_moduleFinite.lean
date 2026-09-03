import Mathlib
import P2M.Util
import P2M.Sol.S_HenselianLocalRing_moduleFinite_localizationAtPrime_of_moduleFinite

set_option autoImplicit false

open IsLocalRing

theorem HenselianLocalRing.moduleFinite_localizationAtPrime_of_moduleFinite
    {A : Type*} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
    {B : Type*} [CommRing B] [Algebra A B] [Module.Finite A B]
    (𝔫 : Ideal B) [𝔫.IsMaximal] :
    Module.Finite A (Localization.AtPrime 𝔫) := by p2m_exact_reverting @_root_.P2MW.S_HenselianLocalRing_moduleFinite_localizationAtPrime_of_moduleFinite.solution
