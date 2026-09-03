import Mathlib
import Definitions.Def_GroupCohomology_Selmer
import Theorems.Thm_Representation_exists_isGalois_level_forall_apply_eq_self
import P2M.Util
namespace P2MW.S_Rep_dualTwist_smooth

set_option autoImplicit false
set_option maxHeartbeats 1600000

universe u

open CategoryTheory

theorem solution {k G : Type u} [Field k] [Group G]
    (r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (M : Rep.{u} k G) [FiniteDimensional k M] (χ : G →* kˣ)
    (hsm : ∀ m : M, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ s, r s ∈ F.fixingSubgroup → M.ρ s m = m)
    (hχ : ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ s, r s ∈ F.fixingSubgroup → χ s = 1) :
    ∀ f : M.dualTwist χ, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ s, r s ∈ F.fixingSubgroup → (M.dualTwist χ).ρ s f = f := by
  intro f
  obtain ⟨F₁, hF₁, -, h₁⟩ := Representation.exists_isGalois_level_forall_apply_eq_self r M.ρ hsm
  obtain ⟨F₂, hF₂, h₂⟩ := hχ
  haveI := hF₁; haveI := hF₂
  refine ⟨F₁ ⊔ F₂, inferInstance, fun s hs => ?_⟩
  have hs₁ : r s ∈ F₁.fixingSubgroup := IntermediateField.fixingSubgroup_antitone le_sup_left hs
  have hs₂ : r s ∈ F₂.fixingSubgroup := IntermediateField.fixingSubgroup_antitone le_sup_right hs
  rw [Rep.dualTwist_ρ_apply, h₂ s hs₂, Units.val_one, one_smul]
  apply LinearMap.ext; intro m
  rw [LinearMap.comp_apply]
  congr 1
  have hs₁' : r s⁻¹ ∈ F₁.fixingSubgroup := by rw [map_inv]; exact F₁.fixingSubgroup.inv_mem hs₁
  exact h₁ s⁻¹ hs₁' m
