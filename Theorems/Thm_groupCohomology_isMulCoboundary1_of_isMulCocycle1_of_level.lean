import Mathlib
import P2M.Util
import P2M.Sol.S_groupCohomology_isMulCoboundary1_of_isMulCocycle1_of_level

set_option autoImplicit false

universe u v

open groupCohomology
theorem groupCohomology.isMulCoboundary1_of_isMulCocycle1_of_level
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L] [IsGalois K L]
    {f : (L ≃ₐ[K] L) → Lˣ} (hf : IsMulCocycle₁ f)
    (hlc : ∃ E : IntermediateField K L, FiniteDimensional K E ∧
      ∀ σ τ : L ≃ₐ[K] L, τ ∈ E.fixingSubgroup → f (σ * τ) = f σ) :
    IsMulCoboundary₁ f := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_isMulCoboundary1_of_isMulCocycle1_of_level.solution
