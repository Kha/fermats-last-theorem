import Mathlib
import P2M.Util
import P2M.Sol.S_Module_End_mem_ideal_of_forall_apply_eq_zero_zmod

set_option autoImplicit false

theorem Module.End.mem_ideal_of_forall_apply_eq_zero_zmod
    {n : ℕ} [NeZero n] {M : Type*} [AddCommGroup M] [Module (ZMod n) M]
    [Module.Free (ZMod n) M] [Module.Finite (ZMod n) M]
    (J : Ideal (Module.End (ZMod n) M)) (b : Module.End (ZMod n) M)
    (hb : ∀ m : M, (∀ j ∈ J, j m = 0) → b m = 0) :
    b ∈ J := by p2m_exact_reverting @_root_.P2MW.S_Module_End_mem_ideal_of_forall_apply_eq_zero_zmod.solution
