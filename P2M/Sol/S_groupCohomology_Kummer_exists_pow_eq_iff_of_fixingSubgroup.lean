import Mathlib
import Definitions.Def_GroupCohomology_Kummer
import Theorems.Thm_groupCohomology_Kummer_exists_pow_eq_iff_exists_rootOfUnity_coboundary
import P2M.Util
namespace P2MW.S_groupCohomology_Kummer_exists_pow_eq_iff_of_fixingSubgroup

set_option autoImplicit false

universe u v

open groupCohomology groupCohomology.Kummer

private theorem fixingSubgroupEquiv_smul_units
    {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] (K : IntermediateField k Ω)
    (σ : K.fixingSubgroup) (x : Ωˣ) :
    (IntermediateField.fixingSubgroupEquiv K σ) • x = (σ : Ω ≃ₐ[k] Ω) • x :=
  Units.ext rfl

private theorem kummerCocycle_fixingSubgroupEquiv
    {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] (K : IntermediateField k Ω)
    (α : Ωˣ) (σ : K.fixingSubgroup) :
    kummerCocycle α (IntermediateField.fixingSubgroupEquiv K σ) = kummerCocycle α (σ : Ω ≃ₐ[k] Ω) := by
  rw [kummerCocycle_apply, kummerCocycle_apply, fixingSubgroupEquiv_smul_units]

theorem solution
    {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] [IsGalois k Ω] (K : IntermediateField k Ω)
    {p : ℕ} {a : Kˣ} {α : Ωˣ} (hα : algebraMap K Ω (a : K) = (α : Ω) ^ p) :
    (∃ b : Kˣ, b ^ p = a) ↔
      ∃ ζ : Ωˣ, ζ ^ p = 1 ∧ ∀ σ : K.fixingSubgroup,
        (σ : Ω ≃ₐ[k] Ω) • ζ / ζ = kummerCocycle α (σ : Ω ≃ₐ[k] Ω) := by
  rw [exists_pow_eq_iff_exists_rootOfUnity_coboundary (K := K) (L := Ω) hα]
  refine exists_congr fun ζ => and_congr_right fun _ => ⟨fun h σ => ?_, fun h σ => ?_⟩
  · rw [← fixingSubgroupEquiv_smul_units, ← kummerCocycle_fixingSubgroupEquiv]
    exact h _
  · obtain ⟨τ, rfl⟩ := (IntermediateField.fixingSubgroupEquiv K).surjective σ
    rw [fixingSubgroupEquiv_smul_units, kummerCocycle_fixingSubgroupEquiv]
    exact h τ
