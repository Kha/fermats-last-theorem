import Mathlib
import Definitions.Def_GroupCohomology_Kummer
import Theorems.Thm_groupCohomology_Kummer_exists_pow_eq_iff_exists_rootOfUnity_coboundary
import P2M.Util
namespace P2MW.S_groupCohomology_Kummer_kummerClass_eq_zero_iff

set_option autoImplicit false

universe u v

open groupCohomology groupCohomology.Kummer

theorem solution
    {K L : Type} [Field K] [Field L] [Algebra K L] [IsGalois K L]
    {p : ℕ} {a : Kˣ} {α : Lˣ} (hα : algebraMap K L (a : K) = (α : L) ^ p) :
    kummerClass hα = 0 ↔ ∃ b : Kˣ, b ^ p = a := by
  rw [kummerClass, H1π_eq_zero_iff]
  constructor
  · intro h
    have h2 : IsMulCoboundary₁ (M := rootsOfUnity p L) (kummerCocycleRoots hα) :=
      isMulCoboundary₁_of_mem_coboundaries₁ _ h
    obtain ⟨ζ, hζ⟩ := h2
    refine (exists_pow_eq_iff_exists_rootOfUnity_coboundary hα).2
      ⟨(ζ : Lˣ), (mem_rootsOfUnity p (ζ : Lˣ)).1 ζ.2, fun σ => ?_⟩
    exact congrArg (Subtype.val) (hζ σ)
  · intro h
    obtain ⟨ζ, hζp, hζ⟩ := (exists_pow_eq_iff_exists_rootOfUnity_coboundary hα).1 h
    exact (coboundariesOfIsMulCoboundary₁
      (f := kummerCocycleRoots hα) ⟨⟨ζ, hζp⟩, fun σ => Subtype.ext (hζ σ)⟩).2
