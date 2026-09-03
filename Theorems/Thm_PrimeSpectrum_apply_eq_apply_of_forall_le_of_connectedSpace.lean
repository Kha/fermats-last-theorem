import Mathlib
import P2M.Util
import P2M.Sol.S_PrimeSpectrum_apply_eq_apply_of_forall_le_of_connectedSpace

universe u v
theorem PrimeSpectrum.apply_eq_apply_of_forall_le_of_connectedSpace
    {R : Type u} [CommRing R] [IsNoetherianRing R] [ConnectedSpace (PrimeSpectrum R)]
    {α : Type v} (φ : PrimeSpectrum R → α)
    (h : ∀ p q : PrimeSpectrum R, p ≤ q → φ p = φ q) (p q : PrimeSpectrum R) :
    φ p = φ q := by p2m_exact_reverting @_root_.P2MW.S_PrimeSpectrum_apply_eq_apply_of_forall_le_of_connectedSpace.solution
