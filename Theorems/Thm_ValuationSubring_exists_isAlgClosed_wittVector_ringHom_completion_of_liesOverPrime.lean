import Mathlib
import Definitions.Def_FLTPrelim_Ramification
import P2M.Util
import P2M.Sol.S_ValuationSubring_exists_isAlgClosed_wittVector_ringHom_completion_of_liesOverPrime
attribute [-instance] ValuationSubring.mulSemiringActionWithVal ValuationSubring.mulSemiringActionCompletion ValuationSubring.uniformContinuousConstSMul_withVal ValuationSubring.charZero_completion
attribute [-simp] ValuationSubring.ratCast_mem_ratClosure ValuationSubring.intCast_mem_ratClosure ValuationSubring.natCast_mem_ratClosure

set_option autoImplicit false

theorem ValuationSubring.exists_isAlgClosed_wittVector_ringHom_completion_of_liesOverPrime
    (p : ℕ) [Fact p.Prime] (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p) :
    ∃ (k : Type) (_ : Field k) (_ : CharP k p) (_ : PerfectRing k p) (_ : IsAlgClosed k)
      (ψ : WittVector p k →+* A.valuation.Completion),
      (∀ x : k, ∃ n : ℕ, 0 < n ∧ x ^ p ^ n = x) ∧
      Function.Injective ψ ∧
      (∀ y : WittVector p k, Valued.v (ψ y) ≤ 1) ∧
      (∀ z : A.valuation.Completion, Valued.v z ≤ 1 → ∃ y : WittVector p k, Valued.v (z - ψ y) < 1) := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_exists_isAlgClosed_wittVector_ringHom_completion_of_liesOverPrime.solution
