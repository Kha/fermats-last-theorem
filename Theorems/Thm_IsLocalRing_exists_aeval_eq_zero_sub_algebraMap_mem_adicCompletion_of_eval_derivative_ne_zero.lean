import Mathlib
import P2M.Util
import P2M.Sol.S_IsLocalRing_exists_aeval_eq_zero_sub_algebraMap_mem_adicCompletion_of_eval_derivative_ne_zero

set_option autoImplicit false

open IsLocalRing Polynomial

theorem IsLocalRing.exists_aeval_eq_zero_sub_algebraMap_mem_adicCompletion_of_eval_derivative_ne_zero
    (A : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (P : Polynomial A) (hP : P.Monic) (r : ResidueField A)
    (hr : (P.map (residue A)).eval r = 0) (hr' : (P.map (residue A)).derivative.eval r ≠ 0) :
    ∃ (t : AdicCompletion (IsLocalRing.maximalIdeal A) A) (a : A), aeval t P = 0 ∧ residue A a = r ∧
      t - algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A) a ∈
        (IsLocalRing.maximalIdeal A).map (algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A)) := by p2m_exact_reverting @_root_.P2MW.S_IsLocalRing_exists_aeval_eq_zero_sub_algebraMap_mem_adicCompletion_of_eval_derivative_ne_zero.solution
