import Mathlib
import Definitions.Def_NumberField_PlaceTransport
import Definitions.Def_NumberField_PlaceDecompositionAction
import P2M.Util
import P2M.Sol.S_NumberField_PlaceTransport_stabilizer_eq_decomp

set_option autoImplicit false
open scoped NumberField.PlaceTransport
theorem NumberField.PlaceTransport.stabilizer_eq_decomp (E K : Type*) [Field E] [Field K] [NumberField K] [Algebra E K]
    (w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    MulAction.stabilizer (K ≃ₐ[E] K) w = NumberField.PlaceDecomp.decomp E K w := by p2m_exact_reverting @_root_.P2MW.S_NumberField_PlaceTransport_stabilizer_eq_decomp.solution
