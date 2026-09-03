import Mathlib
import Definitions.Def_Mathlib_RingTheory_Valuation_LowerRamificationGroup
import P2M.Util
import P2M.Sol.S_Ideal_inertia_pow_succ_eq_map_lowerRamificationGroup_of_dense

set_option autoImplicit false

theorem Ideal.inertia_pow_succ_eq_map_lowerRamificationGroup_of_dense
    {B : Type*} [CommRing B] {G : Type*} [Group G] [MulSemiringAction G B] (Q : Ideal B)
    {Γ : Type*} [Group Γ] (j : Γ →* G) (hj : ∀ σ : G, (∀ x ∈ Q, σ • x ∈ Q) → σ ∈ j.range)
    {R : Type*} [CommRing R] [IsLocalRing R] [MulSemiringAction Γ R]
    (f : B →+* R) (hf : ∀ (γ : Γ) (x : B), f (j γ • x) = γ • f x)
    (hcomap : ∀ n : ℕ, (IsLocalRing.maximalIdeal R ^ n).comap f = Q ^ n)
    (hdense : ∀ (n : ℕ) (y : R), ∃ x : B, y - f x ∈ IsLocalRing.maximalIdeal R ^ n) (i : ℕ) :
    (Q ^ (i + 1)).inertia G = (IsLocalRing.lowerRamificationGroup R Γ i).map j := by p2m_exact_reverting @_root_.P2MW.S_Ideal_inertia_pow_succ_eq_map_lowerRamificationGroup_of_dense.solution
