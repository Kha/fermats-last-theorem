import Mathlib
import Definitions.Def_CohCarrier_Inst
import P2M.Util
import P2M.Sol.S_CohCarrier_exists_squarefree_aeval_heckeTL_eq_zero_of_complex

set_option autoImplicit false

theorem CohCarrier.exists_squarefree_aeval_heckeTL_eq_zero_of_complex
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (ℓ : ℕ) [NeZero ℓ]
    (h : ∃ p : Polynomial ℂ, Squarefree p ∧ Polynomial.aeval (CohCarrier.heckeTL M H ℂ ℓ) p = 0)
    (K : Type) [Field K] [CharZero K] :
    ∃ p : Polynomial K, Squarefree p ∧ Polynomial.aeval (CohCarrier.heckeTL M H K ℓ) p = 0 := by p2m_exact_reverting @_root_.P2MW.S_CohCarrier_exists_squarefree_aeval_heckeTL_eq_zero_of_complex.solution
