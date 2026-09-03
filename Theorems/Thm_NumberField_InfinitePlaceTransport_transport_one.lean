import Mathlib
import Definitions.Def_NumberField_InfinitePlaceTransport
import P2M.Util
import P2M.Sol.S_NumberField_InfinitePlaceTransport_transport_one

set_option autoImplicit false
theorem NumberField.InfinitePlaceTransport.transport_one (E K : Type*) [Field E] [Field K] [Algebra E K]
    (w : NumberField.InfinitePlace K) (h : (1 : K ≃ₐ[E] K) • w = w) :
    NumberField.InfinitePlaceTransport.transport (1 : K ≃ₐ[E] K) h = RingEquiv.refl w.Completion := by p2m_exact_reverting @_root_.P2MW.S_NumberField_InfinitePlaceTransport_transport_one.solution
