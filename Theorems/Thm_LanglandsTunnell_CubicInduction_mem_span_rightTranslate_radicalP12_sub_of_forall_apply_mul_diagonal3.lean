import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries3
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_CubicInduction_mem_span_rightTranslate_radicalP12_sub_of_forall_apply_mul_diagonal3

set_option autoImplicit false

open IsDedekindDomain NumberField LanglandsTunnell.CubicInduction

theorem LanglandsTunnell.CubicInduction.mem_span_rightTranslate_radicalP12_sub_of_forall_apply_mul_diagonal3
    (v : HeightOneSpectrum (𝓞 ℚ)) (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))
    (F : LocalGL3 v → ℂ) (hF : F ∈ principalSeries3 v χ)
    (hsm : ∃ U : Subgroup (LocalGL3 v), IsOpen (U : Set (LocalGL3 v)) ∧ ∀ k ∈ U, ∀ g : LocalGL3 v, F (g * k) = F g)
    (θ : (v.adicCompletion ℚ)ˣ →* ℂˣ)
    (hθ : ∀ u : (v.adicCompletion ℚ)ˣ, Valued.v (u : v.adicCompletion ℚ) = 1 →
      ∀ g : LocalGL3 v, F (g * diagonal3 v ![u, 1, 1]) = ((θ u : ℂˣ) : ℂ) * F g)
    (hne : ∀ i : Fin 3, ∃ u : (v.adicCompletion ℚ)ˣ, Valued.v (u : v.adicCompletion ℚ) = 1 ∧ θ u ≠ χ i u) :
    F ∈ Submodule.span ℂ {h : LocalGL3 v → ℂ | ∃ (w : Fin 2 → v.adicCompletion ℚ) (G : LocalGL3 v → ℂ),
      G ∈ principalSeries3 v χ ∧ h = gl3AmbientRightTranslate (R := ℂ) (radicalP12 w) G - G} := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_CubicInduction_mem_span_rightTranslate_radicalP12_sub_of_forall_apply_mul_diagonal3.solution
