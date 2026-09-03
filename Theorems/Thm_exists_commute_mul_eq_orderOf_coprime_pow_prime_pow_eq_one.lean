import Mathlib
import P2M.Util
import P2M.Sol.S_exists_commute_mul_eq_orderOf_coprime_pow_prime_pow_eq_one

set_option autoImplicit false

open CategoryTheory MonoidalCategory Module
open scoped Classical

theorem exists_commute_mul_eq_orderOf_coprime_pow_prime_pow_eq_one
    (p : ℕ) [Fact p.Prime] {G : Type} [Group G] [Finite G] (g : G) :
    ∃ g' u : G, g' * u = g ∧ Commute g' u ∧ (orderOf g').Coprime p ∧ (∃ a : ℕ, u ^ p ^ a = 1) ∧
      g' ∈ Subgroup.zpowers g ∧ u ∈ Subgroup.zpowers g := by p2m_exact_reverting @_root_.P2MW.S_exists_commute_mul_eq_orderOf_coprime_pow_prime_pow_eq_one.solution
