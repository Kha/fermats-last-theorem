import Mathlib
import Definitions.Def_GroupCohomology_ContinuousH2
import Definitions.Def_GroupCohomology_LevelSubgroup
import P2M.Util
import P2M.Sol.S_groupCohomology_exists_coind_cocycles1_isLevelConstant1_eval_one_eq

set_option autoImplicit false

universe u

open CategoryTheory
theorem groupCohomology.exists_coind_cocycles1_isLevelConstant1_eval_one_eq {k G : Type u} [CommRing k] [Group G]
    (r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (S : Subgroup G)
    (hS : ∃ F₀ : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F₀ ∧ F₀.fixingSubgroup.comap r ≤ S)
    (N : Rep.{u} k S) (b : groupCohomology.cocycles₁ N)
    (hb : groupCohomology.IsLevelConstant₁ (r.comp S.subtype) b) :
    ∃ c : groupCohomology.cocycles₁ (Rep.coind S.subtype N), groupCohomology.IsLevelConstant₁ r c ∧
      ∀ s : S, ((c (s : G) : Rep.coind S.subtype N) : G → N) 1 = b s := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_exists_coind_cocycles1_isLevelConstant1_eval_one_eq.solution
