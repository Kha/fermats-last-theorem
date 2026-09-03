import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevel
import P2M.Util
import P2M.Sol.S_groupCohomology_exists_mem_levelCocyclesSr2_res_sub_mem_levelCoboundariesSr2_of_isUnit_index
attribute [-instance] groupCohomology.normal_comap_fixingSubgroup groupCohomology.finiteIndex_comap_fixingSubgroup

set_option autoImplicit false

universe u

open CategoryTheory groupCohomology

theorem groupCohomology.exists_mem_levelCocyclesSr2_res_sub_mem_levelCoboundariesSr2_of_isUnit_index
    {k G : Type u} [CommRing k] [Group G] (r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (S : Finset Nat.Primes) (M : Rep.{u} k G)
    (hsm : ∀ m : M, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), F.IsUnramifiedOutside S ∧
      ∀ g : G, r g ∈ F.fixingSubgroup → M.ρ g m = m)
    (N : Subgroup G) [N.Normal] [N.FiniteIndex] (hu : IsUnit ((N.index : ℕ) : k))
    (hN : ∃ F₀ : IntermediateField ℚ (AlgebraicClosure ℚ), F₀.IsUnramifiedOutside S ∧ F₀.fixingSubgroup.comap r ≤ N)
    (x : ↥N × ↥N → M) (hx : x ∈ levelCocyclesSr₂ (r.comp N.subtype) S (Rep.res N.subtype M))
    (hinv : ∀ g : G,
      (fun ab : ↥N × ↥N => M.ρ g (x (MulAut.conjNormal g⁻¹ ab.1, MulAut.conjNormal g⁻¹ ab.2))) - x ∈
        levelCoboundariesSr₂ (r.comp N.subtype) S (Rep.res N.subtype M)) :
    ∃ y : G × G → M, y ∈ levelCocyclesSr₂ r S M ∧
      (fun ab : ↥N × ↥N => y ((ab.1 : G), (ab.2 : G))) - x ∈ levelCoboundariesSr₂ (r.comp N.subtype) S (Rep.res N.subtype M) := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_exists_mem_levelCocyclesSr2_res_sub_mem_levelCoboundariesSr2_of_isUnit_index.solution
