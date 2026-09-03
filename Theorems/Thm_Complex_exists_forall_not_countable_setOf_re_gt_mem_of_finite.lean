import Mathlib.Data.Complex.Basic
import Mathlib.Data.Set.Countable
import Mathlib.Order.Bounds.Basic
import Mathlib.Data.Fintype.Lattice
import P2M.Util
import P2M.Sol.S_Complex_exists_forall_not_countable_setOf_re_gt_mem_of_finite

theorem Complex.exists_forall_not_countable_setOf_re_gt_mem_of_finite
    {ι : Type} [Finite ι] (S : ι → Set ℂ)
    (h : ∀ σ' : ℝ, ¬ Set.Countable {s : ℂ | σ' < s.re ∧ ∃ i, s ∈ S i}) :
    ∃ i, ∀ σ' : ℝ, ¬ Set.Countable {s : ℂ | σ' < s.re ∧ s ∈ S i} := by p2m_exact_reverting @_root_.P2MW.S_Complex_exists_forall_not_countable_setOf_re_gt_mem_of_finite.solution
