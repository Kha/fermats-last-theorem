import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
import P2M.Util
import P2M.Sol.S_NumberField_InfiniteAdeleRing_isHomeomorph_ringEquiv_mixedSpace

set_option autoImplicit false

open NumberField

theorem NumberField.InfiniteAdeleRing.isHomeomorph_ringEquiv_mixedSpace
    (K : Type) [Field K] :
    IsHomeomorph (InfiniteAdeleRing.ringEquiv_mixedSpace K) := by p2m_exact_reverting @_root_.P2MW.S_NumberField_InfiniteAdeleRing_isHomeomorph_ringEquiv_mixedSpace.solution
