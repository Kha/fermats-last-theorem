import Mathlib
import P2M.Util
import P2M.Sol.S_IsArtinianRing_exists_units_eq_mul_apply_of_prod_iterate_apply_eq_one

set_option autoImplicit false

theorem IsArtinianRing.exists_units_eq_mul_apply_of_prod_iterate_apply_eq_one
    (E : Type) [CommRing E] [IsArtinianRing E] [IsReduced E]
    (θ : E →+* E) (k : ℕ) (hk : 0 < k) (hθ : ∀ x : E, θ^[k] x = x)
    (hfree : ∀ e : E, IsIdempotentElem e → e ≠ 0 → ∀ i : ℕ, 0 < i → i < k →
      ¬ ∀ x : E, θ^[i] (e * x) = e * x)
    (c : Eˣ) (hc : ((List.range k).map fun i => θ^[i] (c : E)).prod = 1) :
    ∃ z : Eˣ, (z : E) = c * θ z := by p2m_exact_reverting @_root_.P2MW.S_IsArtinianRing_exists_units_eq_mul_apply_of_prod_iterate_apply_eq_one.solution
