import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_CubicInduction_exists_mem_gl3CyclicSubspace_iotaGL_bump_of_isCompact_of_isOpen

set_option autoImplicit false

open Matrix IsDedekindDomain NumberField AutomorphicForm

theorem LanglandsTunnell.CubicInduction.exists_mem_gl3CyclicSubspace_iotaGL_bump_of_isCompact_of_isOpen
    (v : HeightOneSpectrum (𝓞 ℚ)) (ψ : AddChar (v.adicCompletion ℚ) ℂ) (hψ : ψ ≠ 1)
    (W : LocalGL3 v → ℂ) (hW : IsGL3PsiWhittakerFn ψ W)
    (hsm : ∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧
      ∀ k ∈ Uv, ∀ g : LocalGL3 v, W (g * k) = W g)
    (hne : W ≠ 0) (t₀ : GL (Fin 2) (v.adicCompletion ℚ)) (U₁ : Subgroup (GL (Fin 2) (v.adicCompletion ℚ)))
    (hU₁ : IsCompact (U₁ : Set (GL (Fin 2) (v.adicCompletion ℚ))))
    (hU₁' : IsOpen (U₁ : Set (GL (Fin 2) (v.adicCompletion ℚ))))
    (hψU₁ : ∀ x : v.adicCompletion ℚ, t₀⁻¹ * unipotentGL2 x * t₀ ∈ U₁ → ψ x = 1) :
    ∃ W' ∈ gl3CyclicSubspace W,
      (∀ k ∈ U₁, ∀ h : GL (Fin 2) (v.adicCompletion ℚ), W' (iotaGL (h * k)) = W' (iotaGL h)) ∧
      (∀ h : GL (Fin 2) (v.adicCompletion ℚ), W' (iotaGL h) ≠ 0 →
        ∃ x : v.adicCompletion ℚ, ∃ k ∈ U₁, h = unipotentGL2 x * t₀ * k) ∧
      W' (iotaGL t₀) = 1 := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_gl3CyclicSubspace_iotaGL_bump_of_isCompact_of_isOpen.solution
