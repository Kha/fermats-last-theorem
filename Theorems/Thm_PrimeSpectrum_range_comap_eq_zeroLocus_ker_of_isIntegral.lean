import Mathlib
import P2M.Util
import P2M.Sol.S_PrimeSpectrum_range_comap_eq_zeroLocus_ker_of_isIntegral

set_option autoImplicit false

universe u v

open PrimeSpectrum

theorem PrimeSpectrum.range_comap_eq_zeroLocus_ker_of_isIntegral
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] (f : R →+* S) (hf : f.IsIntegral) :
    Set.range (PrimeSpectrum.comap f) = PrimeSpectrum.zeroLocus (RingHom.ker f) := by p2m_exact_reverting @_root_.P2MW.S_PrimeSpectrum_range_comap_eq_zeroLocus_ker_of_isIntegral.solution
