import Mathlib
import P2M.Util
import P2M.Sol.S_FixedPart_exists_trace_mul_ne_zero

set_option autoImplicit false

open Submodule

theorem FixedPart.exists_trace_mul_ne_zero
    (R : Type) [CommRing R] [Module.Free ℤ R] [Module.Finite ℤ R] [IsReduced R] (r : R) (hr : r ≠ 0) :
    ∃ s : R, Algebra.trace ℤ R (r * s) ≠ 0 := by p2m_exact_reverting @_root_.P2MW.S_FixedPart_exists_trace_mul_ne_zero.solution
