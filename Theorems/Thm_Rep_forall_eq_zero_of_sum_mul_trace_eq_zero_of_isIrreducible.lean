import Mathlib
import P2M.Util
import P2M.Sol.S_Rep_forall_eq_zero_of_sum_mul_trace_eq_zero_of_isIrreducible

set_option autoImplicit false

open CategoryTheory MonoidalCategory Module
open scoped Classical

theorem Rep.forall_eq_zero_of_sum_mul_trace_eq_zero_of_isIrreducible
    {k : Type} [Field k] [Finite k] {G : Type} [Group G]
    {r : ℕ} (S : Fin r → Rep.{0} k G) [∀ i, FiniteDimensional k (S i)]
    (hS : ∀ i, (S i).ρ.IsIrreducible) (hij : ∀ i j, Nonempty (S i ≅ S j) → i = j)
    (c : Fin r → k) (hc : ∀ g : G, ∑ i, c i * LinearMap.trace k (S i) ((S i).ρ g) = 0) :
    ∀ i, c i = 0 := by p2m_exact_reverting @_root_.P2MW.S_Rep_forall_eq_zero_of_sum_mul_trace_eq_zero_of_isIrreducible.solution
