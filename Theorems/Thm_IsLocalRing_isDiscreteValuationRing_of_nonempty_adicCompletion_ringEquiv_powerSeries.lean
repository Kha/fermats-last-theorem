import Mathlib
import P2M.Util
import P2M.Sol.S_IsLocalRing_isDiscreteValuationRing_of_nonempty_adicCompletion_ringEquiv_powerSeries
attribute [-instance] AdicCompletion.instIsLocalRingMaximalIdeal

set_option autoImplicit false

universe u v

open IsLocalRing

theorem IsLocalRing.isDiscreteValuationRing_of_nonempty_adicCompletion_ringEquiv_powerSeries
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (k : Type v) [Field k]
    (e : Nonempty (AdicCompletion (maximalIdeal A) A ≃+* PowerSeries k)) :
    ∃ _ : IsDomain A, IsDiscreteValuationRing A := by p2m_exact_reverting @_root_.P2MW.S_IsLocalRing_isDiscreteValuationRing_of_nonempty_adicCompletion_ringEquiv_powerSeries.solution
