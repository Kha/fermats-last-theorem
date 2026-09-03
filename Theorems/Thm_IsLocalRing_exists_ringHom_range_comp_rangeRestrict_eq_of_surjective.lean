import Mathlib
import P2M.Util
import P2M.Sol.S_IsLocalRing_exists_ringHom_range_comp_rangeRestrict_eq_of_surjective

set_option autoImplicit false

theorem IsLocalRing.exists_ringHom_range_comp_rangeRestrict_eq_of_surjective
    {R : Type*} [CommRing R] [IsLocalRing R]
    {k : Type*} [Field k] (π : R →+* k) (hπ : Function.Surjective π)
    {K : Type*} [Field K] (φ : R →+* K) :
    ∃ ρ : φ.range →+* k, ∀ r : R, ρ (φ.rangeRestrict r) = π r := by p2m_exact_reverting @_root_.P2MW.S_IsLocalRing_exists_ringHom_range_comp_rangeRestrict_eq_of_surjective.solution
