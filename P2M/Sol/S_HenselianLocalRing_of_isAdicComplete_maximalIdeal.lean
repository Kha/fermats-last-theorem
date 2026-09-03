import Mathlib
import P2M.Util
namespace P2MW.S_HenselianLocalRing_of_isAdicComplete_maximalIdeal

set_option autoImplicit false

universe u

theorem solution (R : Type u) [CommRing R] [IsLocalRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R] : HenselianLocalRing R := by
  refine { is_henselian := fun f hf a₀ h₁ h₂ => ?_ }
  exact HenselianRing.is_henselian f hf a₀ h₁ (h₂.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R)))
