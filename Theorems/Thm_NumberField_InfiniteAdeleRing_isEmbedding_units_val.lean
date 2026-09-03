import Mathlib
import P2M.Util
import P2M.Sol.S_NumberField_InfiniteAdeleRing_isEmbedding_units_val

set_option autoImplicit false

open NumberField

theorem NumberField.InfiniteAdeleRing.isEmbedding_units_val
    (K : Type) [Field K] [NumberField K] :
    Topology.IsEmbedding (Units.val : (InfiniteAdeleRing K)ˣ → InfiniteAdeleRing K) := by p2m_exact_reverting @_root_.P2MW.S_NumberField_InfiniteAdeleRing_isEmbedding_units_val.solution
