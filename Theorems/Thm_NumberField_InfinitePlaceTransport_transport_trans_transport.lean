import Mathlib
import Definitions.Def_NumberField_InfinitePlaceTransport
import P2M.Util
import P2M.Sol.S_NumberField_InfinitePlaceTransport_transport_trans_transport

set_option autoImplicit false
theorem NumberField.InfinitePlaceTransport.transport_trans_transport (E K : Type*) [Field E] [Field K] [Algebra E K]
    (σ τ : K ≃ₐ[E] K) {w w' w'' : NumberField.InfinitePlace K}
    (h₁ : τ • w = w') (h₂ : σ • w' = w'') (h₃ : (σ * τ) • w = w'') :
    (NumberField.InfinitePlaceTransport.transport τ h₁).trans (NumberField.InfinitePlaceTransport.transport σ h₂)
      = NumberField.InfinitePlaceTransport.transport (σ * τ) h₃ := by p2m_exact_reverting @_root_.P2MW.S_NumberField_InfinitePlaceTransport_transport_trans_transport.solution
