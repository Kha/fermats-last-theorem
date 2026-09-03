import Mathlib
import P2M.Util
import P2M.Sol.S_RingHom_one_sub_prod_iterate_mul_eq_sum_prod_iterate_mul_iterate_of_apply_eq_mul_add

set_option autoImplicit false

theorem RingHom.one_sub_prod_iterate_mul_eq_sum_prod_iterate_mul_iterate_of_apply_eq_mul_add
    (R : Type*) [CommRing R] (s : R →+* R) (ℓ : ℕ) (hs : ∀ r : R, (⇑s)^[ℓ] r = r)
    (x lam u : R) (h : s x = lam * x + u) :
    (1 - ∏ i ∈ Finset.range ℓ, (⇑s)^[i] lam) * x =
      ∑ j ∈ Finset.range ℓ, (∏ i ∈ Finset.Ico (j + 1) ℓ, (⇑s)^[i] lam) * (⇑s)^[j] u := by p2m_exact_reverting @_root_.P2MW.S_RingHom_one_sub_prod_iterate_mul_eq_sum_prod_iterate_mul_iterate_of_apply_eq_mul_add.solution
