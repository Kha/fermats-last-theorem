import Mathlib
import Definitions.Def_ValuationSubring_CompletionRatClosure
import Definitions.Def_FLTPrelim_Ramification
import P2M.Util
import P2M.Sol.S_ValuationSubring_isDiscreteValuationRing_valuationSubring_ratClosure_and_irreducible_natCast_and_finite_quotient_of_liesOverPrime

set_option autoImplicit false

open ValuationSubring

theorem ValuationSubring.isDiscreteValuationRing_valuationSubring_ratClosure_and_irreducible_natCast_and_finite_quotient_of_liesOverPrime
    (r : ℕ) [Fact r.Prime] (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime r) :
    (⟨(r : A.valuation.Completion), natCast_mem_ratClosure A r⟩ : ↥(ratClosure A)) ∈ (Valued.v.comap (ratClosure A).subtype).valuationSubring ∧
    IsDiscreteValuationRing ↥(Valued.v.comap (ratClosure A).subtype).valuationSubring ∧
    (∀ h : (⟨(r : A.valuation.Completion), natCast_mem_ratClosure A r⟩ : ↥(ratClosure A)) ∈ (Valued.v.comap (ratClosure A).subtype).valuationSubring,
      Irreducible (⟨(⟨(r : A.valuation.Completion), natCast_mem_ratClosure A r⟩ : ↥(ratClosure A)), h⟩ : ↥(Valued.v.comap (ratClosure A).subtype).valuationSubring) ∧
      Finite (↥(Valued.v.comap (ratClosure A).subtype).valuationSubring ⧸ Ideal.span {(⟨(⟨(r : A.valuation.Completion), natCast_mem_ratClosure A r⟩ : ↥(ratClosure A)), h⟩ : ↥(Valued.v.comap (ratClosure A).subtype).valuationSubring)}) ∧
      Nat.card (↥(Valued.v.comap (ratClosure A).subtype).valuationSubring ⧸ Ideal.span {(⟨(⟨(r : A.valuation.Completion), natCast_mem_ratClosure A r⟩ : ↥(ratClosure A)), h⟩ : ↥(Valued.v.comap (ratClosure A).subtype).valuationSubring)}) = r) := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_isDiscreteValuationRing_valuationSubring_ratClosure_and_irreducible_natCast_and_finite_quotient_of_liesOverPrime.solution
