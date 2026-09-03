import Mathlib
import P2M.Util
import P2M.Sol.S_IsDiscreteValuationRing_natCard_quotient_maximalIdeal_pow

set_option autoImplicit false
theorem IsDiscreteValuationRing.natCard_quotient_maximalIdeal_pow {R : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] (n : ℕ) :
    Nat.card (R ⧸ IsLocalRing.maximalIdeal R ^ n) = Nat.card (IsLocalRing.ResidueField R) ^ n := by p2m_exact_reverting @_root_.P2MW.S_IsDiscreteValuationRing_natCard_quotient_maximalIdeal_pow.solution
