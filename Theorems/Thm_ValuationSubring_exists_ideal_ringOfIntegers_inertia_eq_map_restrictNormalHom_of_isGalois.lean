import Mathlib
import Definitions.Def_FLTPrelim_Ramification
import P2M.Util
import P2M.Sol.S_ValuationSubring_exists_ideal_ringOfIntegers_inertia_eq_map_restrictNormalHom_of_isGalois

set_option autoImplicit false

theorem ValuationSubring.exists_ideal_ringOfIntegers_inertia_eq_map_restrictNormalHom_of_isGalois
    (F : Type) [Field F] [NumberField F] [Algebra F (AlgebraicClosure ℚ)]
    (P : ValuationSubring (AlgebraicClosure ℚ)) (q : ℕ) [Fact q.Prime] (hP : P.LiesOverPrime q)
    (M : IntermediateField F (AlgebraicClosure ℚ)) [FiniteDimensional F ↥M] [IsGalois F ↥M] :
    ∃ Q : Ideal (NumberField.RingOfIntegers ↥M), Q.IsMaximal ∧
      (∀ x : NumberField.RingOfIntegers ↥M, P.valuation (algebraMap ↥M (AlgebraicClosure ℚ) x) ≤ 1) ∧
      (∀ x : NumberField.RingOfIntegers ↥M, x ∈ Q ↔ P.valuation (algebraMap ↥M (AlgebraicClosure ℚ) x) < 1) ∧
      (P.inertiaSubgroupIn F).map (AlgEquiv.restrictNormalHom ↥M) = Q.inertia (↥M ≃ₐ[F] ↥M) := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_exists_ideal_ringOfIntegers_inertia_eq_map_restrictNormalHom_of_isGalois.solution
