import Mathlib
import P2M.Util
import P2M.Sol.S_Set_ncard_pairing_annihilator_mul_ncard_eq_ncard_mul_ncard_radical

set_option autoImplicit false

theorem Set.ncard_pairing_annihilator_mul_ncard_eq_ncard_mul_ncard_radical
    {J J' : Type} [AddCommGroup J] [AddCommGroup J'] {L : Type} [Field L] [CharZero L]
    (A : Set J) (X' : Set J') (hA : A.Finite) (hX' : X'.Finite)
    (hA0 : (0 : J) ∈ A) (hAadd : ∀ x ∈ A, ∀ y ∈ A, x + y ∈ A) (hAneg : ∀ x ∈ A, -x ∈ A)
    (hX'0 : (0 : J') ∈ X') (hX'add : ∀ x ∈ X', ∀ y ∈ X', x + y ∈ X') (hX'neg : ∀ x ∈ X', -x ∈ X')
    (B : J → J' → L)
    (hBl : ∀ a ∈ A, ∀ a' ∈ A, ∀ y ∈ X', B (a + a') y = B a y * B a' y)
    (hBr : ∀ a ∈ A, ∀ y ∈ X', ∀ y' ∈ X', B a (y + y') = B a y * B a y') :
    Set.ncard {y : J' | y ∈ X' ∧ ∀ a ∈ A, B a y = 1} * Set.ncard A =
      Set.ncard X' * Set.ncard {a : J | a ∈ A ∧ ∀ y ∈ X', B a y = 1} := by p2m_exact_reverting @_root_.P2MW.S_Set_ncard_pairing_annihilator_mul_ncard_eq_ncard_mul_ncard_radical.solution
