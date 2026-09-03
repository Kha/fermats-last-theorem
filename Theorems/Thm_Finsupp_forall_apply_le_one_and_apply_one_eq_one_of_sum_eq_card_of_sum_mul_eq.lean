import Mathlib
import Definitions.Def_CuspidalType_IsCuspidalOfType
import P2M.Util
import P2M.Sol.S_Finsupp_forall_apply_le_one_and_apply_one_eq_one_of_sum_eq_card_of_sum_mul_eq

set_option autoImplicit false

open Polynomial CuspidalType

theorem Finsupp.forall_apply_le_one_and_apply_one_eq_one_of_sum_eq_card_of_sum_mul_eq {C : Type*} [CommGroup C] [Fintype C] {K : Type*} [Field K] [CharZero K]
    (m : (C →* Kˣ) →₀ ℕ) (f : C → K) (hf : ∀ c, f c = m.sum fun μ n => (n : K) * ((μ c : Kˣ) : K))
    (h1 : ∑ c, f c = Fintype.card C)
    (h2 : ∑ c, f c * f c⁻¹ = (m.sum fun _ n => (n : K)) * Fintype.card C) :
    (∀ μ, m μ ≤ 1) ∧ m 1 = 1 := by p2m_exact_reverting @_root_.P2MW.S_Finsupp_forall_apply_le_one_and_apply_one_eq_one_of_sum_eq_card_of_sum_mul_eq.solution
