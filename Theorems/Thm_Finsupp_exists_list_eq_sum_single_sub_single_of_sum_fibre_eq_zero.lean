import Mathlib
import P2M.Util
import P2M.Sol.S_Finsupp_exists_list_eq_sum_single_sub_single_of_sum_fibre_eq_zero

set_option autoImplicit false

theorem Finsupp.exists_list_eq_sum_single_sub_single_of_sum_fibre_eq_zero
    {α β : Type*} [DecidableEq β] (ℓ : α → β) (D : α →₀ ℤ)
    (hD : ∀ b : β, ((D.support.filter fun a => ℓ a = b).sum fun a => D a) = 0) :
    ∃ l : List (α × α), (∀ p ∈ l, ℓ p.1 = ℓ p.2 ∧ p.1 ∈ D.support ∧ p.2 ∈ D.support ∧ p.1 ≠ p.2) ∧
      D = (l.map fun p => (Finsupp.single p.1 1 - Finsupp.single p.2 1 : α →₀ ℤ)).sum := by p2m_exact_reverting @_root_.P2MW.S_Finsupp_exists_list_eq_sum_single_sub_single_of_sum_fibre_eq_zero.solution
