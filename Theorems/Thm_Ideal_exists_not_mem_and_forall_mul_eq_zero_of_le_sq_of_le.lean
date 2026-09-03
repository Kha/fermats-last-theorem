import Mathlib
import P2M.Util
import P2M.Sol.S_Ideal_exists_not_mem_and_forall_mul_eq_zero_of_le_sq_of_le

set_option autoImplicit false

theorem Ideal.exists_not_mem_and_forall_mul_eq_zero_of_le_sq_of_le
    {B : Type} [CommRing B] [IsNoetherianRing B] (I : Ideal B) (hI : I ≤ I ^ 2)
    (P : Ideal B) [P.IsPrime] (hIP : I ≤ P) :
    ∃ f : B, f ∉ P ∧ ∀ a ∈ I, f * a = 0 := by p2m_exact_reverting @_root_.P2MW.S_Ideal_exists_not_mem_and_forall_mul_eq_zero_of_le_sq_of_le.solution
