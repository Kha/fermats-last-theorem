import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries3
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_CubicInduction_whittakerFunctional3_spherical_ne_zero_of_norm_eq_one
attribute [-simp] LanglandsTunnell.CubicInduction.translateRepStep_apply_coe LanglandsTunnell.CubicInduction.translateFn_apply

set_option autoImplicit false

open IsDedekindDomain NumberField open LanglandsTunnell.CubicInduction hiding exists_eq_smul_of_isWhittakerFunctional3

theorem LanglandsTunnell.CubicInduction.whittakerFunctional3_spherical_ne_zero_of_norm_eq_one
    (v : HeightOneSpectrum (𝓞 ℚ)) (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))
    (hχ : ∀ (i : Fin 3) (x : (v.adicCompletion ℚ)ˣ), ‖(x : v.adicCompletion ℚ)‖ = 1 → χ i x = 1)
    (hχu : ∀ (i : Fin 3) (x : (v.adicCompletion ℚ)ˣ), ‖((χ i x : ℂˣ) : ℂ)‖ = 1)
    (f : ↥(principalSeries3 v χ)) (hf1 : (f : LocalGL3 v → ℂ) 1 = 1)
    (hfK : IsRightInvariant (localMaximalCompact3 (𝓞 ℚ) ℚ v) (f : LocalGL3 v → ℂ))
    (ψv : AddChar (v.adicCompletion ℚ) ℂ)
    (hψ0 : ∀ x : v.adicCompletion ℚ, Valued.v x ≤ 1 → ψv x = 1)
    (hψ1 : ∃ x : v.adicCompletion ℚ, Valued.v x ≤ WithZero.exp (1 : ℤ) ∧ ψv x ≠ 1)
    (Λ : ↥(principalSeries3 v χ) →ₗ[ℂ] ℂ) (hΛ : IsWhittakerFunctional3 ψv Λ) (hΛne : Λ ≠ 0) :
    Λ f ≠ 0 := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_CubicInduction_whittakerFunctional3_spherical_ne_zero_of_norm_eq_one.solution
