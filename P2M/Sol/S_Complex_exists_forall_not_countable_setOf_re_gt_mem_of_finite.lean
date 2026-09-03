import Mathlib.Data.Complex.Basic
import Mathlib.Data.Set.Countable
import Mathlib.Order.Bounds.Basic
import Mathlib.Data.Fintype.Lattice
import Mathlib.Data.Set.Finite.Lattice
import P2M.Util
namespace P2MW.S_Complex_exists_forall_not_countable_setOf_re_gt_mem_of_finite

theorem solution
    {ι : Type} [Finite ι] (S : ι → Set ℂ)
    (h : ∀ σ' : ℝ, ¬ Set.Countable {s : ℂ | σ' < s.re ∧ ∃ i, s ∈ S i}) :
    ∃ i, ∀ σ' : ℝ, ¬ Set.Countable {s : ℂ | σ' < s.re ∧ s ∈ S i} := by
  classical
  by_contra hcon
  push Not at hcon

  choose σ hσ using hcon

  obtain ⟨M, hM⟩ : ∃ M : ℝ, ∀ i, σ i ≤ M := by
    obtain ⟨M, hM⟩ := (Set.range σ).toFinite.bddAbove
    exact ⟨M, fun i => hM (Set.mem_range_self i)⟩
  haveI : Countable ι := Finite.to_countable
  apply h M
  have hsub : {s : ℂ | M < s.re ∧ ∃ i, s ∈ S i} ⊆ ⋃ i, {s : ℂ | σ i < s.re ∧ s ∈ S i} := by
    rintro s ⟨hs, i, hi⟩
    exact Set.mem_iUnion.2 ⟨i, lt_of_le_of_lt (hM i) hs, hi⟩
  exact (Set.countable_iUnion fun i => hσ i).mono hsub
