import Definitions.Def_CerednikDrinfeld_DrinfeldUpperHalfPlane
import Definitions.Def_ValuationSubring_CompletionRatClosure
import Definitions.Def_FLTPrelim_Ramification
import Theorems.Thm_ValuationSubring_exists_two_closed_subfields_completion_inf_eq_ratClosure_of_liesOverPrime
import P2M.Util
namespace P2MW.S_ValuationSubring_not_countable_upperHalfPlane_ratClosure_completion_of_liesOverPrime

set_option autoImplicit false

open ValuationSubring CerednikDrinfeld

theorem solution
    (r : ℕ) [Fact r.Prime] (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime r) :
    ¬ (Omega.upperHalfPlane ↥(ratClosure A) A.valuation.Completion).Countable := by
  obtain ⟨L₁, L₂, -, -, -, -, -, hu₁, -⟩ :=
    ValuationSubring.exists_two_closed_subfields_completion_inf_eq_ratClosure_of_liesOverPrime r A hA
  intro h
  apply hu₁
  refine h.mono ?_
  rintro z ⟨-, hz⟩
  rw [Omega.mem_upperHalfPlane_iff]
  rintro ⟨x, hx⟩ rfl
  exact hz hx
