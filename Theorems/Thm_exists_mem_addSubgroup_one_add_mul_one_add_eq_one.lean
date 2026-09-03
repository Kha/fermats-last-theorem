import Mathlib
import P2M.Util
import P2M.Sol.S_exists_mem_addSubgroup_one_add_mul_one_add_eq_one

set_option autoImplicit false
theorem exists_mem_addSubgroup_one_add_mul_one_add_eq_one
    {L : Type*} [NormedField L] [CompleteSpace L]
    (M : AddSubgroup L) (hMclosed : IsClosed (M : Set L)) (hMmul : ∀ x y : L, x ∈ M → y ∈ M → x * y ∈ M)
    (hMnorm : ∀ x ∈ M, ‖x‖ < 1) {x : L} (hx : x ∈ M) :
    ∃ y ∈ M, (1 + x) * (1 + y) = 1 := by p2m_exact_reverting @_root_.P2MW.S_exists_mem_addSubgroup_one_add_mul_one_add_eq_one.solution
