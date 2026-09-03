import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_CubicInduction_isGL3PsiWhittakerFn_and_hasWhittakerMultOne_of_eq_mul_det
attribute [-simp] LanglandsTunnell.CubicInduction.fnTwist3_apply

set_option autoImplicit false

open Matrix IsDedekindDomain NumberField AutomorphicForm

theorem LanglandsTunnell.CubicInduction.isGL3PsiWhittakerFn_and_hasWhittakerMultOne_of_eq_mul_det
    (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (v : HeightOneSpectrum (𝓞 ℚ))
    (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (hχ : IsLocallyConstant χ)
    (W : LocalGL3 v → ℂ)
    (hW :
      IsGL3PsiWhittakerFn (psiLoc ψ v) (W) ∧ W 1 = 1 ∧
      HasWhittakerMultOne (psiLoc ψ v) (W) ∧
      (∀ F ∈ gl3CyclicSubspace (W), F ≠ 0 → W ∈ gl3CyclicSubspace F) ∧
      (∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧
        ∀ k ∈ Uv, ∀ g : LocalGL3 v, W (g * k) = W g) ∧
      ∀ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) →
        ∃ B : Finset (LocalGL3 v → ℂ), ∀ F ∈ gl3CyclicSubspace (W),
          (∀ k ∈ Uv, ∀ g : LocalGL3 v, F (g * k) = F g) → F ∈ Submodule.span ℂ (B : Set (LocalGL3 v → ℂ))) :
    ∀ W' : LocalGL3 v → ℂ,
      (∀ g : LocalGL3 v, W' g = ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) * W g) →
        IsGL3PsiWhittakerFn (psiLoc ψ v) (W') ∧ W' 1 = 1 ∧
        HasWhittakerMultOne (psiLoc ψ v) (W') ∧
        (∀ F ∈ gl3CyclicSubspace (W'), F ≠ 0 → W' ∈ gl3CyclicSubspace F) ∧
        (∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧
          ∀ k ∈ Uv, ∀ g : LocalGL3 v, W' (g * k) = W' g) ∧
        ∀ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) →
          ∃ B : Finset (LocalGL3 v → ℂ), ∀ F ∈ gl3CyclicSubspace (W'),
            (∀ k ∈ Uv, ∀ g : LocalGL3 v, F (g * k) = F g) → F ∈ Submodule.span ℂ (B : Set (LocalGL3 v → ℂ)) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_CubicInduction_isGL3PsiWhittakerFn_and_hasWhittakerMultOne_of_eq_mul_det.solution
