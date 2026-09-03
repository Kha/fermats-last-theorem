import Mathlib
import Definitions.Def_EllipticCurve_TateModule
import P2M.Util
import P2M.Sol.S_TateModule_forall_rep_eq_self_of_rep_eq_self_of_unipotent_of_forall_eq_pow_mul_pow_mul_pow

set_option autoImplicit false

theorem TateModule.forall_rep_eq_self_of_rep_eq_self_of_unipotent_of_forall_eq_pow_mul_pow_mul_pow
    {G V : Type} [Group G] [AddCommGroup V] [DistribMulAction G V]
    (ℓ : ℕ) [Fact ℓ.Prime] (S : Subgroup G) (γ : G)

    (hU : ∀ x ∈ S, ∀ y ∈ S, ∀ (n : ℕ) (v : V), ((ℓ ^ n : ℕ) : ℤ) • v = 0 → x • (y • v - v) = y • v - v)

    (hT : ∀ (m : ℕ), ∀ τ ∈ S, ∃ (j : ℕ) (x w : G), x ∈ S ∧ w ∈ S ∧ τ = γ ^ j * x ^ (ℓ ^ m) * w ^ (ℓ ^ m))
    (z : TateModule ℓ V) (hz : TateModule.rep ℓ V G γ z = z) :
    ∀ τ ∈ S, TateModule.rep ℓ V G τ z = z := by p2m_exact_reverting @_root_.P2MW.S_TateModule_forall_rep_eq_self_of_rep_eq_self_of_unipotent_of_forall_eq_pow_mul_pow_mul_pow.solution
