import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Definitions.Def_ValuationSubring_CompletionRatClosure
import Definitions.Def_FLTPrelim_Ramification
import Theorems.Thm_CerednikDrinfeld_Omega_exists_pseudoUniformizer_isExhausted_of_isCompact
import Theorems.Thm_ValuationSubring_isCompact_ratClosure_inter_closedBall_of_liesOverPrime
import Theorems.Thm_ValuationSubring_valuation_completion_ratClosure_natCast_pos_and_lt_one_and_rankOne_of_liesOverPrime
import P2M.Util
namespace P2MW.S_CerednikDrinfeld_Omega_exists_pseudoUniformizer_ratClosure_eq_natCast_of_liesOverPrime

set_option autoImplicit false

p2m_open "CerednikDrinfeld.Omega P2MW.S_CerednikDrinfeld_Omega_exists_pseudoUniformizer_ratClosure_eq_natCast_of_liesOverPrime.CerednikDrinfeld.Omega ValuationSubring"

namespace CerednikDrinfeld p2m_export "CerednikDrinfeld" "Omega.exists_pseudoUniformizer_isExhausted_of_isCompact" namespace Omega p2m_export "CerednikDrinfeld.Omega" "PseudoUniformizer IsExhausted exists_pseudoUniformizer_isExhausted_of_isCompact" namespace PUatR end CerednikDrinfeld.Omega.PUatR
p2m_open_scoped "CerednikDrinfeld CerednikDrinfeld.Omega" in
theorem CerednikDrinfeld.Omega.PUatR.coe_natCast_eq (A : ValuationSubring (AlgebraicClosure ℚ)) (n : ℕ) :
    ((n : AlgebraicClosure ℚ) : A.valuation.Completion) = (n : A.valuation.Completion) := by
  show (UniformSpace.Completion.coeRingHom : WithVal A.valuation →+* A.valuation.Completion)
      ((WithVal.equiv A.valuation).symm (n : AlgebraicClosure ℚ)) = _
  rw [map_natCast, map_natCast]

theorem solution
    (r : ℕ) [Fact r.Prime] (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime r) :
    ∃ ϖ : PseudoUniformizer ↥(ValuationSubring.ratClosure A) A.valuation.Completion,
      algebraMap ↥(ValuationSubring.ratClosure A) A.valuation.Completion ϖ.ϖ = ((r : AlgebraicClosure ℚ) : A.valuation.Completion) ∧
      IsExhausted ϖ ∧
      ∀ n : ℕ, ∃ T : Finset ↥(ValuationSubring.ratClosure A), ∀ a : ↥(ValuationSubring.ratClosure A),
        Valued.v (algebraMap ↥(ValuationSubring.ratClosure A) A.valuation.Completion a) ≤ (Valued.v (algebraMap ↥(ValuationSubring.ratClosure A) A.valuation.Completion ϖ.ϖ))⁻¹ ^ n →
          ∃ t ∈ T, Valued.v (algebraMap ↥(ValuationSubring.ratClosure A) A.valuation.Completion a - algebraMap ↥(ValuationSubring.ratClosure A) A.valuation.Completion t) <
            (Valued.v (algebraMap ↥(ValuationSubring.ratClosure A) A.valuation.Completion ϖ.ϖ)) ^ n := by
  obtain ⟨h0, h1, hrk⟩ :=
    ValuationSubring.valuation_completion_ratClosure_natCast_pos_and_lt_one_and_rankOne_of_liesOverPrime r A hA
  have hK₀ := ValuationSubring.isCompact_ratClosure_inter_closedBall_of_liesOverPrime r A hA
  obtain ⟨ϖ, hϖ, hex, hfin⟩ :=
    CerednikDrinfeld.Omega.exists_pseudoUniformizer_isExhausted_of_isCompact ↥(ValuationSubring.ratClosure A) A.valuation.Completion hK₀
      ⟨(r : A.valuation.Completion), natCast_mem_ratClosure A r⟩ h0 h1 hrk
  refine ⟨ϖ, ?_, hex, hfin⟩
  rw [hϖ, CerednikDrinfeld.Omega.PUatR.coe_natCast_eq]
  rfl
