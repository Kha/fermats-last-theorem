import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries3
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_CubicInduction_exists_finset_coefficientFn_mem_span_of_isOpen
attribute [-simp] LanglandsTunnell.CubicInduction.translateRepStep_apply_coe LanglandsTunnell.CubicInduction.translateFn_apply

set_option autoImplicit false

p2m_open "Matrix IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.Converse LanglandsTunnell.CubicInduction~finiteDimensional_fixedPoints_principalSeries3~exists_forall_gl3AmbientRightTranslate_eq_of_mem_principalSeries3"

theorem LanglandsTunnell.CubicInduction.exists_finset_coefficientFn_mem_span_of_isOpen
    (v : HeightOneSpectrum (𝓞 ℚ)) (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))
    (Λ : ↥(principalSeries3 v χ) →ₗ[ℂ] ℂ)
    (Uv : Subgroup (LocalGL3 v)) (hU : IsOpen (Uv : Set (LocalGL3 v))) :
    ∃ B : Finset (LocalGL3 v → ℂ), ∀ f : ↥(principalSeries3 v χ),
      (∀ k ∈ Uv, ∀ g : LocalGL3 v, coefficientFn Λ f (g * k) = coefficientFn Λ f g) →
        coefficientFn Λ f ∈ Submodule.span ℂ (B : Set (LocalGL3 v → ℂ)) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_CubicInduction_exists_finset_coefficientFn_mem_span_of_isOpen.solution
