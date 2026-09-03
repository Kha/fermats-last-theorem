import Mathlib
import Definitions.Def_NumberField_PlaceTransport
import Definitions.Def_DedekindDomain_Completion_BaseChange
import P2M.Util
import P2M.Sol.S_NumberField_PlaceTransport_transport_adicCompletionSemialgHom

set_option autoImplicit false
open scoped NumberField.PlaceTransport
theorem NumberField.PlaceTransport.transport_adicCompletionSemialgHom (E K : Type*) [Field E] [NumberField E]
    [Field K] [NumberField K] [Algebra E K] (σ : K ≃ₐ[E] K)
    {v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E)}
    (W W' : v.Extension (NumberField.RingOfIntegers K)) (h : σ • W.1 = W'.1) (y : v.adicCompletion E) :
    NumberField.PlaceTransport.transport σ h (W.adicCompletionSemialgHom E K y) = W'.adicCompletionSemialgHom E K y := by p2m_exact_reverting @_root_.P2MW.S_NumberField_PlaceTransport_transport_adicCompletionSemialgHom.solution
