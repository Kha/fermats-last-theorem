import Mathlib
import Definitions.Def_GroupCohomology_LocallyConstantClasses
import P2M.Util
import P2M.Sol.S_groupCohomology_inflationImage_eq_inflationImage_of_forall_pow_mem

set_option autoImplicit false
open CategoryTheory Module groupCohomology

universe u
theorem groupCohomology.inflationImage_eq_inflationImage_of_forall_pow_mem
    {k G : Type u} [Field k] [Group G] (M : Rep k G)
    (U W : Subgroup G) [U.Normal] [W.Normal] [U.FiniteIndex] (hUW : U ≤ W)
    (q : ℕ) [Fact q.Prime] (hq : (q : k) ≠ 0)
    (hW : ∀ w ∈ W, ∃ a : ℕ, w ^ (q ^ a) ∈ U) :
    inflationImage M U = inflationImage M W := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_inflationImage_eq_inflationImage_of_forall_pow_mem.solution
