import Mathlib
import P2M.Util
import P2M.Sol.S_AddSubgroup_mem_of_forall_pairing_annihilator_eq_one_of_nondegenerate

set_option autoImplicit false

theorem AddSubgroup.mem_of_forall_pairing_annihilator_eq_one_of_nondegenerate
    {G : Type} [AddCommGroup G] [Finite G] {L : Type} [Field L] (n : ℕ) (hn : n ≠ 0)
    (B : G → G → L)
    (hval : ∀ x y : G, B x y ^ n = 1)
    (hadd₁ : ∀ x x' y : G, B (x + x') y = B x y * B x' y)
    (hadd₂ : ∀ x y y' : G, B x (y + y') = B x y * B x y')
    (hleft : ∀ x : G, (∀ y : G, B x y = 1) → x = 0)
    (hright : ∀ y : G, (∀ x : G, B x y = 1) → y = 0)
    (A : AddSubgroup G) (x : G)
    (hx : ∀ y : G, (∀ a ∈ A, B a y = 1) → B x y = 1) :
    x ∈ A := by p2m_exact_reverting @_root_.P2MW.S_AddSubgroup_mem_of_forall_pairing_annihilator_eq_one_of_nondegenerate.solution
