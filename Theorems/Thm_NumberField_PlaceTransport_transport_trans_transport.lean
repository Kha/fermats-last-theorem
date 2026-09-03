import Mathlib
import Definitions.Def_NumberField_PlaceTransport
import P2M.Util
import P2M.Sol.S_NumberField_PlaceTransport_transport_trans_transport

set_option autoImplicit false
open scoped NumberField.PlaceTransport
theorem NumberField.PlaceTransport.transport_trans_transport (E K : Type*) [Field E] [Field K] [NumberField K] [Algebra E K]
    (σ τ : K ≃ₐ[E] K) {w w' w'' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)}
    (h₁ : τ • w = w') (h₂ : σ • w' = w'') (h₃ : (σ * τ) • w = w'') :
    (NumberField.PlaceTransport.transport τ h₁).trans (NumberField.PlaceTransport.transport σ h₂)
      = NumberField.PlaceTransport.transport (σ * τ) h₃ := by p2m_exact_reverting @_root_.P2MW.S_NumberField_PlaceTransport_transport_trans_transport.solution
