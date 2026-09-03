import Mathlib
import Definitions.Def_GaloisRep_Flat
import P2M.Util
import P2M.Sol.S_GaloisRep_ratLocalizedAt_maximalIdeal_eq_span_natCast

set_option autoImplicit false

theorem GaloisRep.ratLocalizedAt.maximalIdeal_eq_span_natCast (ℓ : ℕ) (hℓ : ℓ.Prime)
    [IsLocalRing (GaloisRep.ratLocalizedAt ℓ)] :
    IsLocalRing.maximalIdeal (GaloisRep.ratLocalizedAt ℓ) =
      Ideal.span {(ℓ : GaloisRep.ratLocalizedAt ℓ)} := by p2m_exact_reverting @_root_.P2MW.S_GaloisRep_ratLocalizedAt_maximalIdeal_eq_span_natCast.solution
