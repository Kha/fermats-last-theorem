import Mathlib
import P2M.Util
import P2M.Sol.S_IsRegularLocalRing_isDomain_and_isIntegrallyClosed_adicCompletion_of_ringKrullDim_eq_two
attribute [-instance] AdicCompletion.instIsLocalRingMaximalIdeal

set_option autoImplicit false

open IsLocalRing

theorem IsRegularLocalRing.isDomain_and_isIntegrallyClosed_adicCompletion_of_ringKrullDim_eq_two (O : Type) [CommRing O] [IsRegularLocalRing O] (hdimO : ringKrullDim O = 2) :
    IsDomain (AdicCompletion (maximalIdeal O) O) ∧ IsIntegrallyClosed (AdicCompletion (maximalIdeal O) O) ∧
      IsNoetherianRing (AdicCompletion (maximalIdeal O) O) ∧ ringKrullDim (AdicCompletion (maximalIdeal O) O) = 2 := by p2m_exact_reverting @_root_.P2MW.S_IsRegularLocalRing_isDomain_and_isIntegrallyClosed_adicCompletion_of_ringKrullDim_eq_two.solution
