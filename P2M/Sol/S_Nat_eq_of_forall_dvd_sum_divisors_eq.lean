import Mathlib
import P2M.Util
namespace P2MW.S_Nat_eq_of_forall_dvd_sum_divisors_eq

set_option autoImplicit false
universe u v
open Polynomial Module
open scoped DirectSum

theorem solution {n : ℕ} (hn : 0 < n) (m m' : ℕ → ℕ)
    (h : ∀ e, e ∣ n → ∑ d ∈ e.divisors, m d = ∑ d ∈ e.divisors, m' d) :
    ∀ d, d ∣ n → m d = m' d := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro hd
    have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hd hn
    have key := h d hd
    rw [← Nat.insert_self_properDivisors hdpos.ne', Finset.sum_insert Nat.self_notMem_properDivisors,
      Finset.sum_insert Nat.self_notMem_properDivisors] at key
    have hproper : ∑ i ∈ d.properDivisors, m i = ∑ i ∈ d.properDivisors, m' i := by
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [Nat.mem_properDivisors] at hi
      exact ih i hi.2 (hi.1.trans hd)
    rw [hproper] at key
    exact Nat.add_right_cancel key
