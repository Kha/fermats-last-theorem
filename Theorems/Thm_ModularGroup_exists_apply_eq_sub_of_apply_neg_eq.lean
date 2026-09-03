import Mathlib
import P2M.Util
import P2M.Sol.S_ModularGroup_exists_apply_eq_sub_of_apply_neg_eq

set_option autoImplicit false

open scoped MatrixGroups

theorem ModularGroup.exists_apply_eq_sub_of_apply_neg_eq {A : Type*} [AddCommGroup A]
    (c : SL(2, ℤ) → A) (hc : ∀ g, c (-g) = c g) :
    ∃ a b : SL(2, ℤ) → A, (∀ g, a (ModularGroup.S * g) = a g) ∧
      (∀ g, b (ModularGroup.S * ModularGroup.T * g) = b g) ∧ ∀ g, c g = b g - a g := by p2m_exact_reverting @_root_.P2MW.S_ModularGroup_exists_apply_eq_sub_of_apply_neg_eq.solution
