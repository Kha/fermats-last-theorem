import Mathlib
import P2M.Util
import P2M.Sol.S_Algebra_formallyUnramified_iff_traceForm_nondegenerate_of_finite

set_option autoImplicit false

universe u

theorem Algebra.formallyUnramified_iff_traceForm_nondegenerate_of_finite
    (K : Type u) [Field K] (B : Type u) [CommRing B] [Algebra K B] [Module.Finite K B] :
    Algebra.FormallyUnramified K B ↔ (Algebra.traceForm K B).Nondegenerate := by p2m_exact_reverting @_root_.P2MW.S_Algebra_formallyUnramified_iff_traceForm_nondegenerate_of_finite.solution
