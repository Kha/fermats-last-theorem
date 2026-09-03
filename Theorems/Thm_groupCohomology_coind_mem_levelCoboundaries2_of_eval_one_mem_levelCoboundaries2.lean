import Mathlib
import Definitions.Def_GroupCohomology_ContinuousH2
import Definitions.Def_GroupCohomology_LevelSubgroup
import P2M.Util
import P2M.Sol.S_groupCohomology_coind_mem_levelCoboundaries2_of_eval_one_mem_levelCoboundaries2

set_option autoImplicit false

universe u

open CategoryTheory
theorem groupCohomology.coind_mem_levelCoboundaries2_of_eval_one_mem_levelCoboundaries2 {k G : Type u} [CommRing k] [Group G]
    (r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (S : Subgroup G)
    (hS : ∃ F₀ : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F₀ ∧ F₀.fixingSubgroup.comap r ≤ S)
    (N : Rep.{u} k S) (c : G × G → Rep.coind S.subtype N)
    (hc : c ∈ groupCohomology.levelCocycles₂ r (Rep.coind S.subtype N))
    (h : (fun p : S × S => ((c ((p.1 : G), (p.2 : G)) : Rep.coind S.subtype N) : G → N) 1)
      ∈ groupCohomology.levelCoboundaries₂ (r.comp S.subtype) N) :
    c ∈ groupCohomology.levelCoboundaries₂ r (Rep.coind S.subtype N) := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_coind_mem_levelCoboundaries2_of_eval_one_mem_levelCoboundaries2.solution
