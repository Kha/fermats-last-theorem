import Mathlib
import P2M.Util
import P2M.Sol.S_LinearMap_natCard_setOf_apply_eq_frobeniusSemilinear_eq_pow_finrank_iInf_range_pow

set_option autoImplicit false

theorem LinearMap.natCard_setOf_apply_eq_frobeniusSemilinear_eq_pow_finrank_iInf_range_pow
    {k V : Type*} [Field k] [IsAlgClosed k] (p : ℕ) [Fact p.Prime] [CharP k p]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (S : V →+ V) (hS : ∀ (c : k) (v : V), S (c • v) = c ^ p • S v)
    (hSbij : Function.Bijective S)
    (U : V →ₗ[k] V) (hcomm : ∀ v : V, U (S v) = S (U v)) :
    Nat.card {v : V // U v = S v} =
      p ^ Module.finrank k ↥(⨅ n : ℕ, LinearMap.range (U ^ n)) := by p2m_exact_reverting @_root_.P2MW.S_LinearMap_natCard_setOf_apply_eq_frobeniusSemilinear_eq_pow_finrank_iInf_range_pow.solution
