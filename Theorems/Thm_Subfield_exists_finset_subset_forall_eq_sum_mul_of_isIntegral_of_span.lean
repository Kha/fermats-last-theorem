import Mathlib
import P2M.Util
import P2M.Sol.S_Subfield_exists_finset_subset_forall_eq_sum_mul_of_isIntegral_of_span
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option autoImplicit false

theorem Subfield.exists_finset_subset_forall_eq_sum_mul_of_isIntegral_of_span
    {Ω : Type*} [Field Ω] [CharZero Ω]
    (R : Subring Ω) (hR : IsNoetherianRing ↥R)
    (F₀ L : Subfield Ω) (hRF : R ≤ F₀.toSubring) (hFL : F₀ ≤ L)
    (hfrac : ∀ x ∈ F₀, ∃ r ∈ R, ∃ d ∈ R, d ≠ 0 ∧ x * d = r)
    (N B : Set Ω) (hN : ∀ x, x ∈ N ↔ x ∈ F₀ ∧ IsIntegral ↥R x) (hB : ∀ x, x ∈ B ↔ x ∈ L ∧ IsIntegral ↥R x)
    (s : Finset Ω) (hs : ∀ x ∈ N, x ∈ Submodule.span ↥R (↑s : Set Ω))
    (u : Finset Ω) (hu : ∀ x ∈ L, x ∈ Submodule.span ↥F₀ (↑u : Set Ω)) :
    ∃ t : Finset Ω, (↑t : Set Ω) ⊆ B ∧
      ∀ x ∈ B, ∃ f : Ω → Ω, (∀ c ∈ t, f c ∈ N) ∧ x = ∑ c ∈ t, f c * c := by p2m_exact_reverting @_root_.P2MW.S_Subfield_exists_finset_subset_forall_eq_sum_mul_of_isIntegral_of_span.solution
