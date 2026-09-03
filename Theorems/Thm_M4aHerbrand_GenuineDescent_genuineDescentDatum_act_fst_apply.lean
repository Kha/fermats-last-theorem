import Mathlib
import Definitions.Def_NumberField_InfinitePlaceTransport
import Definitions.Def_M4aHerbrand_GenuineDescent
import P2M.Util
import P2M.Sol.S_M4aHerbrand_GenuineDescent_genuineDescentDatum_act_fst_apply

set_option autoImplicit false
theorem M4aHerbrand.GenuineDescent.genuineDescentDatum_act_fst_apply (K L : Type*) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] (σ : L ≃ₐ[K] L)
    (x : NumberField.AdeleRing (NumberField.RingOfIntegers L) L)
    {w w' : NumberField.InfinitePlace L} (h : σ • w = w') :
    ((M4aHerbrand.GenuineDescent.genuineDescentDatum K L).act σ x).1 w'
      = NumberField.InfinitePlaceTransport.transport σ h (x.1 w) := by p2m_exact_reverting @_root_.P2MW.S_M4aHerbrand_GenuineDescent_genuineDescentDatum_act_fst_apply.solution
