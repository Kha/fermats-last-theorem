import Mathlib
import P2M.Util
import P2M.Sol.S_IsLocalRing_map_ringEquiv_mem_maximalIdeal_pow_iff

set_option autoImplicit false
open IsLocalRing
theorem IsLocalRing.map_ringEquiv_mem_maximalIdeal_pow_iff {R : Type*} [CommRing R] [IsLocalRing R]
    (σ : R ≃+* R) {k : ℕ} {x : R} : σ x ∈ maximalIdeal R ^ k ↔ x ∈ maximalIdeal R ^ k := by p2m_exact_reverting @_root_.P2MW.S_IsLocalRing_map_ringEquiv_mem_maximalIdeal_pow_iff.solution
