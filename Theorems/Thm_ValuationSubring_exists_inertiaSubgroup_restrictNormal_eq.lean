import Mathlib
import P2M.Util
import P2M.Sol.S_ValuationSubring_exists_inertiaSubgroup_restrictNormal_eq

theorem ValuationSubring.exists_inertiaSubgroup_restrictNormal_eq
    (L : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ L] [Normal ℚ L]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (σ : A.inertiaSubgroup ℚ) :
    ∃ τ : (A.comap (algebraMap L (AlgebraicClosure ℚ))).inertiaSubgroup ℚ,
      ((τ : (A.comap (algebraMap L (AlgebraicClosure ℚ))).decompositionSubgroup ℚ) : L ≃ₐ[ℚ] L)
        = AlgEquiv.restrictNormalHom L
            ((σ : A.decompositionSubgroup ℚ) : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ)) := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_exists_inertiaSubgroup_restrictNormal_eq.solution
