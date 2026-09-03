import Mathlib
import Definitions.Def_GroupCohomology_ContinuousH2
import P2M.Util
import P2M.Sol.S_groupCohomology_finrank_continuousClasses_eq_finrank_of_isUnit_index_of_forall_apply_eq

set_option autoImplicit false
universe u
open CategoryTheory Module groupCohomology
theorem groupCohomology.finrank_continuousClasses_eq_finrank_of_isUnit_index_of_forall_apply_eq
    {k G : Type u} [Field k] [Group G] (r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (A : Rep.{u} k G) (S : Subgroup G) [S.Normal] [S.FiniteIndex]
    (hindex : IsUnit ((S.index : k)))
    (htriv : ∀ s ∈ S, ∀ v : A, A.ρ s v = v)
    (hS : ∃ F₀ : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F₀ ∧
      ∀ s : G, r s ∈ F₀.fixingSubgroup → s ∈ S)
    (adm : Submodule k (H1 A))
    (hadm : ∀ x, x ∈ adm ↔ ∃ c : cocycles₁ A, IsLevelConstant₁ r c.val ∧ (H1π A).hom c = x)
    (W : Submodule k (cocycles₁ (Rep.res S.subtype A)))
    (hW : ∀ c, c ∈ W ↔ IsLevelConstant₁ (r.comp S.subtype) c.val ∧
      ∀ (g : G) (s t : S), (g⁻¹ * s * g : G) = t → A.ρ g (c t) = c s) :
    finrank k adm = finrank k W := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_finrank_continuousClasses_eq_finrank_of_isUnit_index_of_forall_apply_eq.solution
