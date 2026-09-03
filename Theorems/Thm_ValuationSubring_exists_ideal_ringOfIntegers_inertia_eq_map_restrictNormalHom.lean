import Mathlib
import Definitions.Def_FLTPrelim_Ramification
import P2M.Util
import P2M.Sol.S_ValuationSubring_exists_ideal_ringOfIntegers_inertia_eq_map_restrictNormalHom

set_option autoImplicit false
theorem ValuationSubring.exists_ideal_ringOfIntegers_inertia_eq_map_restrictNormalHom
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ F] [IsGalois ℚ F]
    (P : ValuationSubring (AlgebraicClosure ℚ)) {q : ℕ} (hq : q.Prime) (hP : P.LiesOverPrime q) :
    ∃ Q : Ideal (NumberField.RingOfIntegers F), Q.IsMaximal ∧ Finite (NumberField.RingOfIntegers F ⧸ Q) ∧
      (q : NumberField.RingOfIntegers F) ∈ Q ∧
      (∀ x : NumberField.RingOfIntegers F, P.valuation (algebraMap F (AlgebraicClosure ℚ) x) ≤ 1) ∧
      (∀ x : NumberField.RingOfIntegers F, x ∈ Q ↔ P.valuation (algebraMap F (AlgebraicClosure ℚ) x) < 1) ∧
      (P.inertiaSubgroupIn ℚ).map (AlgEquiv.restrictNormalHom F) = Q.inertia (F ≃ₐ[ℚ] F) ∧
      (∀ τ : F ≃ₐ[ℚ] F, τ ∈ Q.inertia (F ≃ₐ[ℚ] F) →
        (∀ x : NumberField.RingOfIntegers F, τ • x - x ∈ Q ^ 2) → ∃ a : ℕ, orderOf τ = q ^ a) ∧
      (∃ ϖ : NumberField.RingOfIntegers F, ϖ ∈ Q ∧
        (∀ x ∈ Q, ∃ y : NumberField.RingOfIntegers F, x - ϖ * y ∈ Q ^ 2) ∧
        (∀ c : NumberField.RingOfIntegers F, c * ϖ ∈ Q ^ 2 → c ∈ Q)) := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_exists_ideal_ringOfIntegers_inertia_eq_map_restrictNormalHom.solution
