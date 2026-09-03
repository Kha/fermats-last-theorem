import Mathlib
import P2M.Util
import P2M.Sol.S_Representation_trace_mul_eq_trace_of_commute_of_pow_prime_pow_eq_one

set_option autoImplicit false

open CategoryTheory MonoidalCategory Module
open scoped Classical

theorem Representation.trace_mul_eq_trace_of_commute_of_pow_prime_pow_eq_one
    {p : ℕ} [Fact p.Prime] {k : Type} [Field k] [CharP k p] {G : Type} [Group G]
    {V : Type} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (ρ : Representation k G V) (g u : G) (hgu : Commute g u) (a : ℕ) (hu : u ^ p ^ a = 1) :
    LinearMap.trace k V (ρ (g * u)) = LinearMap.trace k V (ρ g) := by p2m_exact_reverting @_root_.P2MW.S_Representation_trace_mul_eq_trace_of_commute_of_pow_prime_pow_eq_one.solution
