import Mathlib
import Definitions.Def_FLTPrelim_Ramification
import P2M.Util
import P2M.Sol.S_AlgebraicClosure_monoidHom_eq_one_of_inertiaSubgroupIn_le_ker

theorem AlgebraicClosure.monoidHom_eq_one_of_inertiaSubgroupIn_le_ker {Γ : Type*} [Group Γ]
    (χ : ((AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ)) →* Γ)
    (hopen : IsOpen (χ.ker : Set ((AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ))))
    (hunr : ∀ q : ℕ, q.Prime → ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime q →
      A.inertiaSubgroupIn ℚ ≤ χ.ker) :
    χ = 1 := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicClosure_monoidHom_eq_one_of_inertiaSubgroupIn_le_ker.solution
