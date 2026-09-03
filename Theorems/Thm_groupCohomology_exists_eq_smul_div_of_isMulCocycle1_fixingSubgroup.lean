import Mathlib
import P2M.Util
import P2M.Sol.S_groupCohomology_exists_eq_smul_div_of_isMulCocycle1_fixingSubgroup

set_option autoImplicit false

universe u v

open groupCohomology
theorem groupCohomology.exists_eq_smul_div_of_isMulCocycle1_fixingSubgroup
    {k : Type u} {Ω : Type v} [Field k] [Field Ω] [Algebra k Ω] [IsGalois k Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K]
    {f : K.fixingSubgroup → Ωˣ} (hf : IsMulCocycle₁ f)
    (hlc : ∃ L : IntermediateField k Ω, FiniteDimensional k L ∧
      ∀ σ τ : K.fixingSubgroup, (τ : Ω ≃ₐ[k] Ω) ∈ L.fixingSubgroup → f (σ * τ) = f σ) :
    ∃ α : Ωˣ, ∀ σ : K.fixingSubgroup, f σ = (σ : Ω ≃ₐ[k] Ω) • α / α := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_exists_eq_smul_div_of_isMulCocycle1_fixingSubgroup.solution
