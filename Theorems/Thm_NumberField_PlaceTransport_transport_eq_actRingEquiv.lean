import Mathlib
import Definitions.Def_NumberField_PlaceTransport
import Definitions.Def_NumberField_PlaceDecompositionAction
import P2M.Util
import P2M.Sol.S_NumberField_PlaceTransport_transport_eq_actRingEquiv

set_option autoImplicit false
open scoped NumberField.PlaceTransport
theorem NumberField.PlaceTransport.transport_eq_actRingEquiv (E K : Type*) [Field E] [Field K] [NumberField K] [Algebra E K]
    (w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) (σ : NumberField.PlaceDecomp.decomp E K w)
    (h : (σ : K ≃ₐ[E] K) • w = w) :
    NumberField.PlaceTransport.transport (σ : K ≃ₐ[E] K) h = NumberField.PlaceDecomp.actRingEquiv σ := by p2m_exact_reverting @_root_.P2MW.S_NumberField_PlaceTransport_transport_eq_actRingEquiv.solution
