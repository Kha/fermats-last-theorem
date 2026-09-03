import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_finite_intermediateField_of_transcendental_mem

set_option autoImplicit false
theorem AlgebraicCurve.finite_intermediateField_of_transcendental_mem
    (K L : Type) [Field K] [Field L] [Algebra K L]
    (E : IntermediateField K L) (t : L) (htE : t ∈ E) (ht : Transcendental K t)
    (hfg : ∃ x : L, Transcendental K x ∧ FiniteDimensional ↥(IntermediateField.adjoin K ({x} : Set L)) L) :
    Module.Finite ↥E L := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_finite_intermediateField_of_transcendental_mem.solution
