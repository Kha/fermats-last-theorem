import Mathlib
import Definitions.Def_FLTPrelim_Ramification
import P2M.Util
import P2M.Sol.S_ValuationSubring_exists_valuation_mul_zpow_eq_one_of_forall_inertia_apply_eq

set_option autoImplicit false

theorem ValuationSubring.exists_valuation_mul_zpow_eq_one_of_forall_inertia_apply_eq
    (F : Type) [Field F] [NumberField F] [Algebra F (AlgebraicClosure ℚ)]
    (P : ValuationSubring (AlgebraicClosure ℚ)) (q : ℕ) [Fact q.Prime] (hP : P.LiesOverPrime q)
    (ϖ : F) (hϖP : algebraMap F (AlgebraicClosure ℚ) ϖ ∈ P)
    (hirr : Irreducible (⟨ϖ, hϖP⟩ : ↥(P.comap (algebraMap F (AlgebraicClosure ℚ)))))
    (M : IntermediateField F (AlgebraicClosure ℚ)) [FiniteDimensional F ↥M] [IsGalois F ↥M]
    (Q : Ideal (NumberField.RingOfIntegers ↥M)) [Q.IsMaximal]
    (hQle : ∀ x : NumberField.RingOfIntegers ↥M, P.valuation (algebraMap ↥M (AlgebraicClosure ℚ) x) ≤ 1)
    (hQlt : ∀ x : NumberField.RingOfIntegers ↥M, x ∈ Q ↔ P.valuation (algebraMap ↥M (AlgebraicClosure ℚ) x) < 1)
    (y : ↥M) (hy : y ≠ 0)
    (hfix : ∀ τ : ↥M ≃ₐ[F] ↥M, τ ∈ Q.inertia (↥M ≃ₐ[F] ↥M) → τ y = y) :
    ∃ n : ℤ, P.valuation (((y : AlgebraicClosure ℚ)) * (algebraMap F (AlgebraicClosure ℚ) ϖ) ^ n) = 1 := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_exists_valuation_mul_zpow_eq_one_of_forall_inertia_apply_eq.solution
