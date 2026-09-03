import Mathlib
import Definitions.Def_GroupCohomology_ContinuousH2
import Definitions.Def_GroupCohomology_ContinuousH2Map
import P2M.Util
import P2M.Sol.S_groupCohomology_continuousH2Map_res_injective_of_isUnit_index
attribute [-instance] groupCohomology.normal_comap_fixingSubgroup groupCohomology.finiteIndex_comap_fixingSubgroup

set_option autoImplicit false

universe u

open CategoryTheory
theorem groupCohomology.continuousH2Map_res_injective_of_isUnit_index {k G : Type u} [CommRing k] [Group G]
    (r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (S : Subgroup G) [S.FiniteIndex]
    (hS : ∃ F₀ : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F₀ ∧ F₀.fixingSubgroup.comap r ≤ S)
    (hu : IsUnit ((S.index : ℕ) : k)) (N : Rep.{u} k G) :
    Function.Injective (groupCohomology.continuousH2Map (rH := r) (rG := r.comp S.subtype) (A := N)
      (B := Rep.res S.subtype N) S.subtype (fun _ => rfl) LinearMap.id (fun _ _ => rfl)) := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_continuousH2Map_res_injective_of_isUnit_index.solution
