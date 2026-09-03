import Mathlib
import Definitions.Def_ValuationSubring_CompletionRatClosure
import Definitions.Def_FLTPrelim_Ramification
import P2M.Util
import P2M.Sol.S_ValuationSubring_exists_isDiscreteValuationRing_isFractionRing_ratClosure_finite_residueField_and_irreducible_natCast_of_liesOverPrime

set_option autoImplicit false

p2m_open "ValuationSubring~isDiscreteValuationRing_valuationSubring_ratClosure_and_irreducible_natCast_and_finite_quotient_of_liesOverPrime"

theorem ValuationSubring.exists_isDiscreteValuationRing_isFractionRing_ratClosure_finite_residueField_and_irreducible_natCast_of_liesOverPrime
    (r : ℕ) [Fact r.Prime] (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime r) :
    ∃ (R₀ : Type) (_ : CommRing R₀) (_ : IsDomain R₀) (_ : IsDiscreteValuationRing R₀)
      (_ : Algebra R₀ ↥(ratClosure A)) (_ : IsFractionRing R₀ ↥(ratClosure A))
      (_ : Finite (IsLocalRing.ResidueField R₀)),
      (∀ x : ↥(ratClosure A), x ∈ Set.range (algebraMap R₀ ↥(ratClosure A)) ↔
          Valued.v (algebraMap ↥(ratClosure A) A.valuation.Completion x) ≤ 1) ∧
      Irreducible ((r : ℕ) : R₀) := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_exists_isDiscreteValuationRing_isFractionRing_ratClosure_finite_residueField_and_irreducible_natCast_of_liesOverPrime.solution
