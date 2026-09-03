import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries3
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_CubicInduction_exists_eq_smul_of_isWhittakerFunctional3
attribute [-simp] LanglandsTunnell.CubicInduction.translateRepStep_apply_coe LanglandsTunnell.CubicInduction.translateFn_apply

set_option autoImplicit false

open IsDedekindDomain NumberField

theorem LanglandsTunnell.CubicInduction.exists_eq_smul_of_isWhittakerFunctional3
    (v : HeightOneSpectrum (𝓞 ℚ))
    (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (ψ : AddChar (v.adicCompletion ℚ) ℂ) (hψ : ψ ≠ 1)
    (Λ₀ Λ : ↥(principalSeries3 v χ) →ₗ[ℂ] ℂ) (hΛ₀ : IsWhittakerFunctional3 ψ Λ₀) (hne : Λ₀ ≠ 0)
    (hΛ : IsWhittakerFunctional3 ψ Λ) : ∃ c : ℂ, Λ = c • Λ₀ := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_of_isWhittakerFunctional3.solution
