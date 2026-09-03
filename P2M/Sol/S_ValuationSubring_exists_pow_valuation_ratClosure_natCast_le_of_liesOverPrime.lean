import Mathlib
import Definitions.Def_ValuationSubring_CompletionRatClosure
import Definitions.Def_FLTPrelim_Ramification
import Theorems.Thm_ValuationSubring_valuation_completion_ratClosure_natCast_pos_and_lt_one_and_rankOne_of_liesOverPrime
import P2M.Util
namespace P2MW.S_ValuationSubring_exists_pow_valuation_ratClosure_natCast_le_of_liesOverPrime

set_option autoImplicit false

open ValuationSubring

theorem solution
    (r : ℕ) [Fact r.Prime] (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime r) :
    ∀ ε : A.ValueGroup, ε ≠ 0 → ∃ N : ℕ, Valued.v (algebraMap (↥(ratClosure A)) A.valuation.Completion ⟨(r : A.valuation.Completion), natCast_mem_ratClosure A r⟩) ^ N ≤ ε := by
  intro ε hε
  obtain ⟨-, hlt, hrank⟩ :=
    ValuationSubring.valuation_completion_ratClosure_natCast_pos_and_lt_one_and_rankOne_of_liesOverPrime r A hA

  obtain ⟨k, hk⟩ := A.valuation_surjective ε
  have hvk : Valued.v ((k : A.valuation.Completion)) = ε := by
    rw [show (k : A.valuation.Completion) =
        (((WithVal.equiv A.valuation).symm k : WithVal A.valuation) : A.valuation.Completion) from rfl,
      Valued.valuedCompletion_apply, ← hk]
    rfl
  have hk0 : (k : A.valuation.Completion) ≠ 0 := fun h => hε (by rw [← hvk, h, map_zero])
  obtain ⟨N, hN⟩ := hrank _ _ hlt hk0
  exact ⟨N, hvk ▸ hN⟩
