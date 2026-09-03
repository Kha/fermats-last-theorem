import Mathlib
import Definitions.Def_GroupCohomology_Kummer
import P2M.Util
import P2M.Sol.S_groupCohomology_Kummer_exists_kummerCocycle_eq_of_isMulCocycle1

set_option autoImplicit false

universe u v

open groupCohomology groupCohomology.Kummer
theorem groupCohomology.Kummer.exists_kummerCocycle_eq_of_isMulCocycle1
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    {p : ℕ} {f : (L ≃ₐ[K] L) → Lˣ} (hf : IsMulCocycle₁ f) (hfp : ∀ σ : L ≃ₐ[K] L, f σ ^ p = 1) :
    ∃ (a : Kˣ) (α : Lˣ),
      algebraMap K L (a : K) = (α : L) ^ p ∧ ∀ σ : L ≃ₐ[K] L, f σ = kummerCocycle α σ := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_Kummer_exists_kummerCocycle_eq_of_isMulCocycle1.solution
