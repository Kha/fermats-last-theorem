import Mathlib
import Definitions.Def_GroupCohomology_Kummer
import P2M.Util
import P2M.Sol.S_groupCohomology_Kummer_exists_kummerCocycle_eq_of_isMulCocycle1_of_level

set_option autoImplicit false

universe u v

open groupCohomology groupCohomology.Kummer
theorem groupCohomology.Kummer.exists_kummerCocycle_eq_of_isMulCocycle1_of_level
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L] [IsGalois K L] {p : ℕ} [NeZero p]
    {f : (L ≃ₐ[K] L) → Lˣ} (hf : IsMulCocycle₁ f) (hfp : ∀ σ, f σ ^ p = 1)
    (hlc : ∃ E : IntermediateField K L, FiniteDimensional K E ∧
      ∀ σ τ : L ≃ₐ[K] L, τ ∈ E.fixingSubgroup → f (σ * τ) = f σ) :
    ∃ (a : Kˣ) (α : Lˣ),
      algebraMap K L (a : K) = (α : L) ^ p ∧ ∀ σ : L ≃ₐ[K] L, f σ = kummerCocycle α σ := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_Kummer_exists_kummerCocycle_eq_of_isMulCocycle1_of_level.solution
