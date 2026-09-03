import Mathlib
import Definitions.Def_GroupCohomology_Kummer
import Theorems.Thm_groupCohomology_Kummer_exists_kummerClass_eq
import P2M.Util
namespace P2MW.S_groupCohomology_Kummer_kummerHom_surjective

set_option autoImplicit false

universe u v

open groupCohomology groupCohomology.Kummer

theorem solution
    {K L : Type} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L] (p : ℕ) :
    Function.Surjective (kummerHom K L p) := by
  intro x
  obtain ⟨a, α, hα, hx⟩ := exists_kummerClass_eq (Multiplicative.toAdd x)
  refine ⟨⟨a, α, hα⟩, ?_⟩
  rw [kummerHom_apply_mk a α hα, ← hx]
  exact ofAdd_toAdd x
