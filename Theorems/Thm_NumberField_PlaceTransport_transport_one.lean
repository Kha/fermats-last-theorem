import Mathlib
import Definitions.Def_NumberField_PlaceTransport
import P2M.Util
import P2M.Sol.S_NumberField_PlaceTransport_transport_one

set_option autoImplicit false
open scoped NumberField.PlaceTransport
theorem NumberField.PlaceTransport.transport_one (E K : Type*) [Field E] [Field K] [NumberField K] [Algebra E K]
    (w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) (h : (1 : K ≃ₐ[E] K) • w = w) :
    NumberField.PlaceTransport.transport (1 : K ≃ₐ[E] K) h = RingEquiv.refl (w.adicCompletion K) := by p2m_exact_reverting @_root_.P2MW.S_NumberField_PlaceTransport_transport_one.solution
