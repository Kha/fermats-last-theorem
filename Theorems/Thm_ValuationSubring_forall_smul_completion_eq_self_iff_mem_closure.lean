import Mathlib
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_ValuationSubring_CompletionDecompositionAction
import P2M.Util
import P2M.Sol.S_ValuationSubring_forall_smul_completion_eq_self_iff_mem_closure

set_option autoImplicit false

theorem ValuationSubring.forall_smul_completion_eq_self_iff_mem_closure
    (p : ℕ) (hp : p.Prime)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (H : Subgroup ↥(A.decompositionSubgroup ℚ)) (x : A.valuation.Completion) :
    (∀ σ : ↥(A.decompositionSubgroup ℚ), σ ∈ H → σ • x = x) ↔
      x ∈ closure (((↑) : AlgebraicClosure ℚ → A.valuation.Completion) ''
        (IntermediateField.fixedField (H.map (A.decompositionSubgroup ℚ).subtype) :
          Set (AlgebraicClosure ℚ))) := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_forall_smul_completion_eq_self_iff_mem_closure.solution
