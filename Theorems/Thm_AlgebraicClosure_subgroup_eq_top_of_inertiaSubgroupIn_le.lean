import Mathlib
import Definitions.Def_FLTPrelim_Ramification
import P2M.Util
import P2M.Sol.S_AlgebraicClosure_subgroup_eq_top_of_inertiaSubgroupIn_le

theorem AlgebraicClosure.subgroup_eq_top_of_inertiaSubgroupIn_le (H : Subgroup ((AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ))) (hopen : IsOpen (H : Set ((AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ)))) (hunr : ∀ q : ℕ, q.Prime → ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime q → A.inertiaSubgroupIn ℚ ≤ H) : H = ⊤ := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicClosure_subgroup_eq_top_of_inertiaSubgroupIn_le.solution
