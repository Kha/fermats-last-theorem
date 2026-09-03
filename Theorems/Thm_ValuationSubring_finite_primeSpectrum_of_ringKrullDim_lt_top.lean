import Mathlib
import P2M.Util
import P2M.Sol.S_ValuationSubring_finite_primeSpectrum_of_ringKrullDim_lt_top

theorem ValuationSubring.finite_primeSpectrum_of_ringKrullDim_lt_top
    {L : Type*} [Field L] (A : ValuationSubring L) (h : ringKrullDim A < ⊤) :
    Finite (PrimeSpectrum A) := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_finite_primeSpectrum_of_ringKrullDim_lt_top.solution
