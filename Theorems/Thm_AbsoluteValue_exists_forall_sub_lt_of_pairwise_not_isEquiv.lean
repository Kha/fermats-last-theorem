import Mathlib
import P2M.Util
import P2M.Sol.S_AbsoluteValue_exists_forall_sub_lt_of_pairwise_not_isEquiv

set_option autoImplicit false
theorem AbsoluteValue.exists_forall_sub_lt_of_pairwise_not_isEquiv {K : Type*} [Field K] {ι : Type*} [Finite ι]
    {v : ι → AbsoluteValue K ℝ} (hv : ∀ i, (v i).IsNontrivial) (hne : Pairwise fun i j => ¬(v i).IsEquiv (v j))
    (a : ι → K) {ε : ℝ} (hε : 0 < ε) : ∃ x : K, ∀ i, v i (x - a i) < ε := by p2m_exact_reverting @_root_.P2MW.S_AbsoluteValue_exists_forall_sub_lt_of_pairwise_not_isEquiv.solution
