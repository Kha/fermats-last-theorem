import Mathlib
import P2M.Util
import P2M.Sol.S_Module_Flat_isOpen_setOf_flat_localization_atPrime

theorem Module.Flat.isOpen_setOf_flat_localization_atPrime
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] [IsNoetherianRing A]
    [Algebra.FiniteType A B] :
    IsOpen {Q : PrimeSpectrum B | Module.Flat A (Localization.AtPrime Q.asIdeal)} := by p2m_exact_reverting @_root_.P2MW.S_Module_Flat_isOpen_setOf_flat_localization_atPrime.solution
