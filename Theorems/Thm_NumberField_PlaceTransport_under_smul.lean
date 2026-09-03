import Mathlib
import Definitions.Def_NumberField_PlaceTransport
import P2M.Util
import P2M.Sol.S_NumberField_PlaceTransport_under_smul

set_option autoImplicit false
open scoped NumberField.PlaceTransport
theorem NumberField.PlaceTransport.under_smul (E K : Type*) [Field E] [Field K] [Algebra E K]
    (σ : K ≃ₐ[E] K) (w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    (σ • w).under (NumberField.RingOfIntegers E) = w.under (NumberField.RingOfIntegers E) := by p2m_exact_reverting @_root_.P2MW.S_NumberField_PlaceTransport_under_smul.solution
