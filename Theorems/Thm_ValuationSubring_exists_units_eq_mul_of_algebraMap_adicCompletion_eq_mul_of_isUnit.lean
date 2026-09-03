import Mathlib
import P2M.Util
import P2M.Sol.S_ValuationSubring_exists_units_eq_mul_of_algebraMap_adicCompletion_eq_mul_of_isUnit

set_option autoImplicit false

theorem ValuationSubring.exists_units_eq_mul_of_algebraMap_adicCompletion_eq_mul_of_isUnit
    {L : Type*} [Field L] (A : ValuationSubring L) (I : Ideal ↥A) (hI : I ≠ ⊤)
    (hsep : ∀ x : ↥A, (∀ n : ℕ, x ∈ I ^ n) → x = 0)
    (α β : ↥A) (u : (AdicCompletion I ↥A)ˣ)
    (h : algebraMap (↥A) (AdicCompletion I ↥A) α = algebraMap (↥A) (AdicCompletion I ↥A) β * u) :
    ∃ v : (↥A)ˣ, α = β * v := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_exists_units_eq_mul_of_algebraMap_adicCompletion_eq_mul_of_isUnit.solution
