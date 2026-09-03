import Mathlib
import Definitions.Def_ModularCurve_NodeDescent
import Definitions.Def_FLTPrelim_Ramification
import P2M.Util
import P2M.Sol.S_ModularCurve_NodeLocalized_exists_finiteDimensional_forall_inertia_apply_eq_and_mem_range_redRestrict
set_option autoImplicit false

open ModularCurve

theorem ModularCurve.NodeLocalized.exists_finiteDimensional_forall_inertia_apply_eq_and_mem_range_redRestrict
    (q : ℕ) [Fact q.Prime] (A : ValuationSubring (AlgebraicClosure ℚ))
    (k : Type*) [Field k] [CharP k q] (red : A →+* k)
    (S : Finset k) (hS : ∀ a ∈ S, a ^ (q ^ 2) = a) :
    ∃ (K₀ : IntermediateField ℚ (AlgebraicClosure ℚ)) (_ : FiniteDimensional ℚ ↥K₀),
      (∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ x ∈ K₀, σ x = x) ∧
      ∀ a ∈ S, a ∈ Set.range (NodeLocalized.redRestrict red K₀) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_NodeLocalized_exists_finiteDimensional_forall_inertia_apply_eq_and_mem_range_redRestrict.solution
