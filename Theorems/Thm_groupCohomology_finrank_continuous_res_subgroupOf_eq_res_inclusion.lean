import Mathlib
import Definitions.Def_GroupCohomology_ContinuousH2
import Definitions.Def_GroupCohomology_ContinuousH2Map
import Definitions.Def_GroupCohomology_ContinuousH1
import P2M.Util
import P2M.Sol.S_groupCohomology_finrank_continuous_res_subgroupOf_eq_res_inclusion

set_option autoImplicit false

universe u

open CategoryTheory
theorem groupCohomology.finrank_continuous_res_subgroupOf_eq_res_inclusion {k G : Type u} [Field k] [Group G]
    (r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (S' S : Subgroup G) (hle : S' ≤ S) (N : Rep.{u} k S) :
    Module.finrank k (Rep.res (S'.subgroupOf S).subtype N).ρ.invariants
        = Module.finrank k (Rep.res (Subgroup.inclusion hle) N).ρ.invariants ∧
    Module.finrank k (groupCohomology.continuousH1 ((r.comp S.subtype).comp (S'.subgroupOf S).subtype)
          (Rep.res (S'.subgroupOf S).subtype N))
        = Module.finrank k (groupCohomology.continuousH1 (r.comp S'.subtype) (Rep.res (Subgroup.inclusion hle) N)) ∧
    Module.finrank k (groupCohomology.continuousH2 ((r.comp S.subtype).comp (S'.subgroupOf S).subtype)
          (Rep.res (S'.subgroupOf S).subtype N))
        = Module.finrank k (groupCohomology.continuousH2 (r.comp S'.subtype) (Rep.res (Subgroup.inclusion hle) N)) := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_finrank_continuous_res_subgroupOf_eq_res_inclusion.solution
