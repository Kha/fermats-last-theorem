import Mathlib
import P2M.Util
import P2M.Sol.S_IsLocalRing_exists_maximalIdeal_pow_le_span_natCast_pow_of_module_finite

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
open IsLocalRing

theorem IsLocalRing.exists_maximalIdeal_pow_le_span_natCast_pow_of_module_finite
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] [CharZero 𝒪]
    (p : ℕ) [Fact p.Prime] (hp𝒪 : (p : 𝒪) ∈ maximalIdeal 𝒪)
    {R : Type} [CommRing R] [IsLocalRing R] [Algebra 𝒪 R] [Module.Finite 𝒪 R]
    (hl : IsLocalHom (algebraMap 𝒪 R)) (n : ℕ) :
    ∃ m : ℕ, maximalIdeal R ^ m ≤ Ideal.span {(p : R)} ^ n := by p2m_exact_reverting @_root_.P2MW.S_IsLocalRing_exists_maximalIdeal_pow_le_span_natCast_pow_of_module_finite.solution
