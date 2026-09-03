import Mathlib
import P2M.Util
import P2M.Sol.S_Matrix_exists_ne_zero_forall_mulVec_eq_zero_of_forall_map_mulVec_eq_zero

set_option autoImplicit false

theorem Matrix.exists_ne_zero_forall_mulVec_eq_zero_of_forall_map_mulVec_eq_zero
    {k K : Type*} [Field k] [Field K] [Algebra k K] {ι : Type*} [Fintype ι] [DecidableEq ι]
    {J : Type*} (A : J → Matrix ι ι k) (v : ι → K) (hv : v ≠ 0)
    (hAv : ∀ j, ((A j).map (algebraMap k K)).mulVec v = 0) :
    ∃ w : ι → k, w ≠ 0 ∧ ∀ j, (A j).mulVec w = 0 := by p2m_exact_reverting @_root_.P2MW.S_Matrix_exists_ne_zero_forall_mulVec_eq_zero_of_forall_map_mulVec_eq_zero.solution
