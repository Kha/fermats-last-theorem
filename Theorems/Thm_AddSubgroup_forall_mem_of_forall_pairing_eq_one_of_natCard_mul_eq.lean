import Mathlib
import P2M.Util
import P2M.Sol.S_AddSubgroup_forall_mem_of_forall_pairing_eq_one_of_natCard_mul_eq

set_option autoImplicit false

theorem AddSubgroup.forall_mem_of_forall_pairing_eq_one_of_natCard_mul_eq
    {G : Type} [AddCommGroup G] [Finite G] {L : Type} [Field L] [CharZero L] (n : ℕ) (hn : n ≠ 0)
    (B : G → G → L)
    (hval : ∀ x y : G, B x y ^ n = 1)
    (hadd₁ : ∀ x x' y : G, B (x + x') y = B x y * B x' y)
    (hadd₂ : ∀ x y y' : G, B x (y + y') = B x y * B x y')
    (hleft : ∀ x : G, (∀ y : G, B x y = 1) → x = 0)
    (hright : ∀ y : G, (∀ x : G, B x y = 1) → y = 0)
    (T F : AddSubgroup G) (hiso : ∀ t ∈ T, ∀ f ∈ F, B t f = 1)
    (hcard : Nat.card T * Nat.card F = Nat.card G) :
    (∀ x : G, (∀ f ∈ F, B x f = 1) → x ∈ T) ∧ (∀ y : G, (∀ t ∈ T, B t y = 1) → y ∈ F) := by p2m_exact_reverting @_root_.P2MW.S_AddSubgroup_forall_mem_of_forall_pairing_eq_one_of_natCard_mul_eq.solution
