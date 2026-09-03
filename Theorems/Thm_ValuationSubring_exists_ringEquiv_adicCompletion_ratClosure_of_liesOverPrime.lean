import Mathlib
import Definitions.Def_ValuationSubring_CompletionRatClosure
import Definitions.Def_FLTPrelim_Ramification
import P2M.Util
import P2M.Sol.S_ValuationSubring_exists_ringEquiv_adicCompletion_ratClosure_of_liesOverPrime

set_option autoImplicit false

open IsDedekindDomain NumberField ValuationSubring

theorem ValuationSubring.exists_ringEquiv_adicCompletion_ratClosure_of_liesOverPrime
    (r : ℕ) [Fact r.Prime] (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime r)
    (v : HeightOneSpectrum (𝓞 ℚ)) (hv : ((r : ℕ) : 𝓞 ℚ) ∈ v.asIdeal) :
    ∃ e : v.adicCompletion ℚ ≃+* ↥(ratClosure A),
      (∀ q : ℚ, ((e (algebraMap ℚ (v.adicCompletion ℚ) q) : ↥(ratClosure A)) : A.valuation.Completion) =
        ((q : AlgebraicClosure ℚ) : A.valuation.Completion)) ∧
      (∀ x : v.adicCompletion ℚ,
        x ∈ v.adicCompletionIntegers ℚ ↔ e x ∈ (Valued.v.comap (ratClosure A).subtype).valuationSubring) ∧
      Continuous e ∧ Continuous e.symm := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_exists_ringEquiv_adicCompletion_ratClosure_of_liesOverPrime.solution
