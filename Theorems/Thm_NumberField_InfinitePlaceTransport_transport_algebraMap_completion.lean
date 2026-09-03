import Mathlib
import Definitions.Def_NumberField_InfinitePlaceTransport
import P2M.Util
import P2M.Sol.S_NumberField_InfinitePlaceTransport_transport_algebraMap_completion

set_option autoImplicit false
open scoped NumberField.LiesOver
theorem NumberField.InfinitePlaceTransport.transport_algebraMap_completion (K L : Type*) [Field K] [Field L] [Algebra K L]
    (σ : L ≃ₐ[K] L) (v : NumberField.InfinitePlace K) {w w' : NumberField.InfinitePlace L}
    [w.1.LiesOver v.1] [w'.1.LiesOver v.1] (h : σ • w = w') (y : v.Completion) :
    NumberField.InfinitePlaceTransport.transport σ h (algebraMap v.Completion w.Completion y)
      = algebraMap v.Completion w'.Completion y := by p2m_exact_reverting @_root_.P2MW.S_NumberField_InfinitePlaceTransport_transport_algebraMap_completion.solution
