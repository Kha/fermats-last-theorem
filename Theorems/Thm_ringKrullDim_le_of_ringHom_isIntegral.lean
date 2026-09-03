import Mathlib
import P2M.Util
import P2M.Sol.S_ringKrullDim_le_of_ringHom_isIntegral

set_option autoImplicit false

universe u v

theorem ringKrullDim_le_of_ringHom_isIntegral
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] (φ : R →+* S) (hφ : φ.IsIntegral) :
    ringKrullDim S ≤ ringKrullDim R := by p2m_exact_reverting @_root_.P2MW.S_ringKrullDim_le_of_ringHom_isIntegral.solution
