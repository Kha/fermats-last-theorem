import Mathlib
import Definitions.Def_GroupCohomology_ContinuousH2
import Definitions.Def_GroupCohomology_ContinuousH2Map
import Definitions.Def_GroupCohomology_ContinuousH1
import P2M.Util
import P2M.Sol.S_groupCohomology_finiteDimensional_continuous_of_forall_apply_eq_of_rank_one
attribute [-instance] groupCohomology.normal_comap_fixingSubgroup groupCohomology.finiteIndex_comap_fixingSubgroup

set_option autoImplicit false

universe u

open CategoryTheory
theorem groupCohomology.finiteDimensional_continuous_of_forall_apply_eq_of_rank_one {k G : Type u} [Field k] [Group G]
    (r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (T : Rep.{u} k G) [FiniteDimensional k T]
    (hT : ∀ (g : G) (t : T), T.ρ g t = t) :
    ((∀ L : Rep.{u} k G, (∀ (g : G) (x : L), L.ρ g x = x) → Module.finrank k L = 1 →
        FiniteDimensional k (groupCohomology.continuousH1 r L)) →
      FiniteDimensional k (groupCohomology.continuousH1 r T)) ∧
    ((∀ L : Rep.{u} k G, (∀ (g : G) (x : L), L.ρ g x = x) → Module.finrank k L = 1 →
        FiniteDimensional k (groupCohomology.continuousH2 r L)) →
      FiniteDimensional k (groupCohomology.continuousH2 r T)) := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_finiteDimensional_continuous_of_forall_apply_eq_of_rank_one.solution
