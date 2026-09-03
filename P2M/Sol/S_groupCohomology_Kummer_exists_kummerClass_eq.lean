import Mathlib
import Definitions.Def_GroupCohomology_Kummer
import Theorems.Thm_groupCohomology_Kummer_exists_kummerCocycle_eq_of_isMulCocycle1
import P2M.Util
namespace P2MW.S_groupCohomology_Kummer_exists_kummerClass_eq

set_option autoImplicit false

universe u v

open groupCohomology groupCohomology.Kummer

theorem solution
    {K L : Type} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    {p : ℕ} (x : H1 (kummerRep K L p)) :
    ∃ (a : Kˣ) (α : Lˣ) (hα : algebraMap K L (a : K) = (α : L) ^ p), x = kummerClass hα := by
  induction x using H1_induction_on with
  | h y =>
    have hy : IsMulCocycle₁ (M := rootsOfUnity p L) (Additive.toMul ∘ ⇑y) :=
      isMulCocycle₁_of_mem_cocycles₁ _ y.2
    set f : (L ≃ₐ[K] L) → Lˣ := fun σ => ((Additive.toMul (y.1 σ) : rootsOfUnity p L) : Lˣ)
      with hf_def
    have hf : IsMulCocycle₁ f := fun σ τ => congrArg Subtype.val (hy σ τ)
    have hfp : ∀ σ : L ≃ₐ[K] L, f σ ^ p = 1 := fun σ =>
      (mem_rootsOfUnity p _).1 (Additive.toMul (y.1 σ) : rootsOfUnity p L).2
    obtain ⟨a, α, hα, hfeq⟩ := exists_kummerCocycle_eq_of_isMulCocycle1 hf hfp
    refine ⟨a, α, hα, ?_⟩
    have : y = kummerCocycles hα := by
      ext σ
      exact congrArg Additive.ofMul (Subtype.ext (hfeq σ))
    rw [kummerClass, this]
