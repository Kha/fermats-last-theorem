import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
import P2M.Util
import P2M.Sol.S_Module_finitePresentation_of_rankAtStalk_eq

set_option autoImplicit false

universe u v

theorem Module.finitePresentation_of_rankAtStalk_eq {R : Type u} [CommRing R]
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Flat R M] (n : ℕ)
    (h : ∀ p : PrimeSpectrum R, Module.rankAtStalk M p = n) : Module.FinitePresentation R M := by p2m_exact_reverting @_root_.P2MW.S_Module_finitePresentation_of_rankAtStalk_eq.solution
